module Aevum.Main

import System
import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util
import Aevum.Type

-- Parsed Datatype

data Parsed : Type where
  EOF : Parsed
  Dec : (id : Name) -> (type : Fn) -> Parsed -> Parsed
  Def : (id : Name) -> (val : Fn) -> Parsed -> Parsed

data Message : Type where
  End : Message
  Info : (msg : String) -> Message -> Message
  Err : (msg : String) -> Message -> Message

covering
Show Parsed where
  show EOF = "EOF"
  show (Dec id x y) = "Dec " ++ pack id ++ " : " ++ show x ++ ",\n" ++ show y
  show (Def id x y) = "Def " ++ pack id ++ " = " ++ show x ++ ",\n" ++ show y

Show Message where
  show End = "End"
  show (Info msg tl) = "[Info] " ++ msg ++ ",\n" ++ show tl
  show (Err msg tl) = "[Error] " ++ msg ++ ",\n" ++ show tl

chk : (List Dec, List Def) -> Fn -> Maybe Fn -> Message -> Message
chk (decs, defs) val fn msg =
  let Just ty = fn
    | Nothing => Err "value not defined" msg in
  let Fail err = check decs defs (norm decs id val) (norm decs id ty) 
    | Success => Info (show val ++ " : " ++ show ty) msg in
  Err (show val ++ " is not " ++ show ty ++ ": " ++ err) msg

-- Lexer

reserved : List String
reserved = ["data", "where", "case", "of"]

exactPack : List Char -> Parser ()
exactPack (a :: b) = P $ \str => case str of
  c :: d => if a == c then solve (exactPack b) d else Err ""
  [] => Err "exact match fail"
exactPack [] = P $ \rem => Res rem ()

exact : String -> Parser ()
exact str = exactPack $ unpack str

some : (Char -> Bool) -> (nullable : Bool) -> Parser (List Char)
some pred nullable = P $ \str => case str of
  a :: b => if pred a then case solve (some pred True) b of
      Res rem res => Res rem (a :: res)
      Err e => Err e
    else if nullable then Res (a :: b) [] else Err "didn't match any"
  [] => if nullable then Res [] [] else Err "didn't match any"

kwd : Parser (List Char)
kwd = P $ \str =>
  let Res rem res = solve (some identChar False) str
    | Err e => Err e in
  if pack res `elem` reserved then Err "reserved" else Res rem res

eof : Parser ()
eof = P $ \str => case str of
  [] => Res [] ()
  _ => Err "not eof"

-- Parser

data Binding = L | R

order : Pos (String, Binding)
order = ("*", L) 
      |+| ("+", L)
      |+| One ("=", R)

oprt : (String, Binding) -> Parser Fn -> Parser Fn
oprt pair@(op, bd) path =
  case bd of
    R => do u <- path; restr u
    L => do u <- path; restl u where
      app : Fn -> Fn -> Fn
      app u v = App (App (Lit $ unpack op) u) v
      restr : Fn -> Parser Fn
      restr u = (do exact op; v <- oprt pair path; pure $ app u v) <|> pure u
      restl : Fn -> Parser Fn
      restl u = (do exact op; v <- path; restl $ app u v) <|> pure u

term : Parser Fn
term =
  let hole = do exact "?"; pure Hole in
  let ident = do id <- kwd; pure $ Lit id in
  let block = do exact "("; u <- term; exact ")"; pure u in
  let atom = hole <|> ident <|> block in
  let single = do u <- atom; rests atom u in
  let comp = frac order single oprt in
  let clause = do exact "\n"; u <- comp; exact "=>"; v <- term; pure (u, v) in
  let cases = do u <- clause; restc clause [u] in
  let cased = do exact "case"; u <- comp; exact "of"; v <- cases; pure $ Case u v in
  let val = cased <|> comp in
  let pi = do exact "("; u <- kwd; exact ":"; v <- term; exact ")";
              exact "->"; w <- term; pure $ Pi u v w in
  let simpPi = do u <- val; restp u in
  let lam = do exact "\\"; u <- kwd; exact "=>"; v <- term; pure $ Lam u v in
  lam <|> pi <|> simpPi where
    frac : Pos a -> Parser b -> (a -> Parser b -> Parser b) -> Parser b
    frac (One x) p f = f x p
    frac (hd |+| tl) p f = let q = f hd p in frac tl q f
    rests : Parser Fn -> Fn -> Parser Fn
    rests p u = (do v <- p; rests p (App u v)) <|> pure u
    restc : Parser a -> List a -> Parser (List a)
    restc p u = (do v <- p; restc p (v :: u)) <|> pure u
    restp : Fn -> Parser Fn
    restp u = (do exact "->"; v <- term; restp (Pi ['_'] u v)) <|> pure u


file : (List Dec, List Def) -> Parser (Parsed, Message)
file info@(decs, defs) = 
  let end = do eof; pure (EOF, End) in
  let endl = do exact "\n"; file info in
  let comment = do exact "--"; _ <- some (/= '\n') True; file info in
  let dec = do id <- kwd; exact ":"; u <- term;
               (v, msg) <- file (id @: u :: decs, defs);
               pure (Dec id u v, chk info u (Just type) msg) in
  let dat = do exact "data"; id <- kwd; exact ":"; u <- term; exact "where";
               (v, msg) <- file (id @: u :: decs, defs);
               pure (Dec id u v, chk info u (Just type) msg) in
  let def = do id <- kwd; exact "="; u <- term;
               (v, msg) <- file (decs, id @= u :: defs);
               pure (Def id u v, chk info u (findDec id decs) msg) in
  end <|> endl <|> comment <|> dec <|> dat <|> def

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 1048576
    | Left err => pure $ Left $ show err
  let Res rem (res, msg) = solve (file ([unpack "Type" @: type], [])) (unpack str)
    | Err err => pure $ Left ("Error on parsing: " ++ err)
  printLn res
  printLn msg
  pure $ Right ()

main : IO ()
main = do
  (_ :: (opt :: _)) <- getArgs
    | _ => printLn "No file specified"
  res <- withFile opt Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
