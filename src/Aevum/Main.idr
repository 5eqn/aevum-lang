module Aevum.Main

import System
import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

Name : Type
Name = List Char

data Pat : Type where
  Cons : Name -> Pat
  Arg : Name -> Pat -> Pat

data Fn : Type where
  Lit : Name -> Fn
  Pi : Name -> Fn -> Fn -> Fn
  Lam : Name -> Fn -> Fn -> Fn
  App : Fn -> Fn -> Fn
  Case : Fn -> List (Pat, Fn) -> Fn

record KV where
  constructor MkKV
  key : Name
  val : Fn

record Info where
  constructor MkInfo
  decs : List KV
  defs : List KV

find : Name -> List KV -> Maybe Fn
find name [] = Nothing
find name (a :: b) = if key a == name then Just a.val else find name b

appendDecs : KV -> Info -> Info
appendDecs kv info = MkInfo (kv :: info.decs) info.defs

appendDefs : KV -> Info -> Info
appendDefs kv info = MkInfo info.decs (kv :: info.defs)

match : Info -> List (Pat, Fn) -> Fn -> Maybe (Info, Fn)
match info ls arg = foldl tryMatch Nothing ls where     -- fold over all paths
  tryMatch : Maybe (Info, Fn) -> (Pat, Fn) -> Maybe (Info, Fn)
  tryMatch Nothing (pat, fn) =
    let Just info' = bindPat pat arg                    -- check and bind argument
      | Nothing => Nothing in
    Just (info', fn) where                              -- apply path if succeeded
    bindPat : Pat -> Fn -> Maybe Info
    bindPat (Cons a) (Lit b) =
      if a == b then Just info else Nothing
    bindPat (Arg a x) (App f (Lit b)) =
      let Just info' = bindPat x f
        | Nothing => Nothing in
      Just $ appendDefs (MkKV a (Lit b)) info'
    bindPat _ _ = Nothing
  tryMatch res _ = res

equal : Info -> Fn -> Fn -> Bool
equal info (Lit n) (Lit m) =
  let Nothing = find n info.defs                        -- left simped
    | Just fn => equal info fn (Lit m) in
  let Nothing = find m info.defs                        -- right simped
    | Just fn => equal info (Lit n) fn in
  n == m
equal info (Pi n a x) (Pi m b y) =
  let True = equal info a b                             -- same argument type
    | False => False in
  equal (appendDefs (MkKV n (Lit m)) info) x y          -- same body when argument replaced
equal info (Lam n a x) (Lam m b y) =
  let True = equal info a b                             -- same argument type
    | False => False in
  equal (appendDefs (MkKV n (Lit m)) info) x y          -- same body when argument replaced
equal info (App (Lam n a x) arg) u = 
  equal (appendDefs (MkKV n arg) info) x u              -- same when argument replaced
equal info u (App fn arg) = equal info (App fn arg) u   -- symmetry
equal info (Case arg ls) u =
  let Nothing = match info ls arg                       -- case choice may commit
    | Just (info', body) => equal info' body u in
  let Case arg' ls' = u                                 -- if didn't commit, rhs must be cased
    | _ => False in
  let True = equal info arg arg'                        -- argument must equal 
    | False => False in
  caseEq info ls ls' where                              -- all case paths equal
  caseEq : Info -> List (Pat, Fn) -> List (Pat, Fn) -> Bool
  caseEq info lhs rhs = foldl contains True lhs where
    contains : Bool -> (Pat, Fn) -> Bool                -- rhs contains all lhs paths
    contains orig (pat, fn) = foldl same False rhs where
      same : Bool -> (Pat, Fn) -> Bool                  -- one of rhs equals each lhs path
      same orig (pat', fn') =
        let Just info' = bindPat pat pat'               -- check and replace argument
          | Nothing => orig in
        equal info' fn fn' where                        -- path with same pattern determines if each lhs path is contained
        bindPat : Pat -> Pat -> Maybe Info
        bindPat (Cons a) (Cons b) = 
          if a == b then Just info else Nothing
        bindPat (Arg a x) (Arg b y) =
          let Just info' = bindPat x y
            | Nothing => Nothing in
          Just $ appendDefs (MkKV a (Lit b)) info'
        bindPat _ _ = Nothing
equal info u (Case arg ls) = equal info (Case arg ls) u -- symmetry
equal info _ _ = False

-- handle lambda and case here, bind dec and def by changing arg `info`. `unify` is not needed in case split.
check : Info -> Fn -> Fn -> Bool
check info (Lit name) ty =
  let Just fn = find name info.decs
    | Nothing => False in
  equal info fn ty
check info _ _ = ?chk

dec : Name -> Fn -> Info -> Maybe Info
dec name fn info =
  let Nothing = find name info.decs
    | Just _ => Nothing in
  Just $ appendDecs (MkKV name fn) info

def : Name -> Fn -> Info -> Maybe Info
def name fn info = ?bind

data Parsed : Type where
  EOF : Parsed

Show Parsed where
  show EOF = "EOF"

-- Lexer

exact' : Name -> Lexer ()
exact' (a :: b) (c :: d) = if a == c then exact' b d else Nothing
exact' [] rem = Just (rem, ())
exact' _ _ = Nothing

exact : String -> Lexer ()
exact str = exact' $ unpack str

any : (Char -> Bool) -> Lexer $ Name
any pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Just (a :: b, [])
any _ _ = Just ([], [])

some : (Char -> Bool) -> Lexer $ Name
some pred (a :: b) = if pred a then case any pred b of
    Just (rem, res) => Just (rem, a :: res)
    Nothing => Nothing
  else Nothing
some _ _ = Nothing

eof : Lexer ()
eof [] = Just ([], ())
eof _ = Nothing

-- Path

data Binding = L | R

order : Pos (String, Binding)
order = ("*", L) 
      |+| ("+", L)
      |+| One ("=", R)

file : Path Parsed
file = 
  let end = eof 
        |> Res EOF in
  let endl = exact "\n"
        |> file in
  let comment = exact "--"
        |> any ^ neq '\n'
        |> file in
  end // endl // comment

-- Main

onError : FileError -> IO String
onError err = pure $ show err

onOpen : File -> IO $ Either String ()
onOpen f = do
  Right str <- fGetChars f 1048576
    | Left err => pure $ Left $ show err
  let Just (rem, res) = solve ^ unpack str $ file
    | Nothing => pure $ Left "Error on parsing"
  printLn res
  pure $ Right ()

main : IO ()
main = do
  (_ :: (opt :: _)) <- getArgs
    | _ => printLn "No file specified"
  res <- withFile opt Read onError onOpen
  case res of
    Left err => printLn err
    Right () => pure ()
