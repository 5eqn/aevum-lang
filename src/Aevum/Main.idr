module Aevum.Main

import System
import System.File.Handle
import System.File.ReadWrite
import Aevum.Path
import Aevum.Util

-- Parsed Datatype

Name : Type
Name = List Char

data Fn : Type where
  Lit : Name -> Fn
  Pi : Name -> Fn -> Fn -> Fn
  Lam : Name -> Fn -> Fn -> Fn
  App : Fn -> Fn -> Fn
  Case : Fn -> List (Fn, Fn) -> Fn

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
appendDefs kv info = MkInfo info.decs (kv :: info.defs) -- TODO prevent self loop

||| Match an argument against a pattern, returns new info and match result.
match : Info -> List (Fn, Fn) -> Fn -> Maybe (Info, Fn)
match info ls arg = foldl tryMatch Nothing ls where     -- fold over all paths
  tryMatch : Maybe (Info, Fn) -> (Fn, Fn) -> Maybe (Info, Fn)
  tryMatch Nothing (pat, fn) =
    let Just info' = bindPat pat arg                    -- check and bind argument
      | Nothing => Nothing in
    Just (info', fn) where                              -- apply path if succeeded
    bindPat : Fn -> Fn -> Maybe Info
    bindPat (Lit a) (Lit b) =
      if a == b then Just info else Nothing
    bindPat (App x (Lit a)) (App f (Lit b)) =
      let Just info' = bindPat x f
        | Nothing => Nothing in
      Just $ appendDefs (MkKV a (Lit b)) info'
    bindPat _ _ = Nothing
  tryMatch res _ = res

||| Bind variables across two patterns to check if their corresponding fn equals.
diffPat : Info -> Fn -> Fn -> Maybe Info
diffPat info (Lit a) (Lit b) = 
  if a == b then Just info else Nothing
diffPat info (App x (Lit a)) (App y (Lit b)) =
  let Just info' = diffPat info x y
    | Nothing => Nothing in
  Just $ appendDefs (MkKV a (Lit b)) info'
diffPat _ _ _ = Nothing

||| Simplify a value.
simp : Info -> Fn -> Fn
simp info (Lit n) =
  let Nothing = find n info.defs                        -- find replacement
    | Just fn => simp info fn in
  Lit n
simp info (Pi id ty body) =
  Pi id (simp info ty) (simp info body)                 -- simp argument type and body
simp info (Lam id ty body) =
  Lam id (simp info ty) (simp info body)                -- simp argument type and body
simp info (App fn arg) =
  let Lam id ty body = simp info fn                     -- if fn is applied, simplifying it yields a lambda
    | _ => App fn arg in
  simp (appendDefs (MkKV id arg) info) body             -- bind argument
simp info (Case arg ls) =
  let Nothing = match info ls arg                       -- case choice may commit
    | Just (info', body) => simp info' body in
  Case arg ls

||| Check if two simplified term equal.
equal : Info -> Fn -> Fn -> Bool
equal info (Lit n) (Lit m) =
  n == m
equal info (Pi n a x) (Pi m b y) =
  let True = equal info a b                             -- same argument type
    | False => False in
  equal (appendDefs (MkKV n (Lit m)) info) x y          -- same body when argument replaced
equal info (Lam n a x) (Lam m b y) =
  let True = equal info a b                             -- same argument type
    | False => False in
  equal (appendDefs (MkKV n (Lit m)) info) x y          -- same body when argument replaced
equal info (App fn arg) (App fn' arg') =
  equal info fn fn' && equal info arg arg'              -- constructor and argument should be the same
equal info (Case arg ls) (Case arg' ls') =
  let True = equal info arg arg'                        -- argument must equal 
    | False => False in
  foldl contains True ls where
    contains : Bool -> (Pat, Fn) -> Bool                -- rhs contains all lhs paths
    contains orig (pat, fn) = foldl same False ls' where
      same : Bool -> (Pat, Fn) -> Bool                  -- one of `ls'` equals each `ls`
      same orig (pat', fn') =
        let Just info' = diffPat info pat pat'          -- check and replace argument
          | Nothing => orig in
        equal info' fn fn'                              -- path with same pattern determines if each `ls` is contained
equal info _ _ = False

||| Check if a simplified value is of a simplified type.
check : Info -> (value : Fn) -> (type : Fn) -> Bool
check info (Lit n) fn =
  let Just ty = find n info.decs                        -- lookup
    | Nothing => False in
  equal info ty fn
check info (Pi _ _ _) (Lit n) = pack n == "Type"        -- pi has type "Type"
check info (Lam n a x) (Pi m b y) = 
  let info' = appendDefs (MkKV n (Lit m)) info in       -- replace and check
  let info' = appendDecs (MkKV n a) info' in
  let info' = appendDecs (MkKV m b) info' in
  equal info a b && check info' x y
check info (App (Lit n) arg) ty =
  let Just (Pi id ty body) = find n info.decs
    | _ => False in
  let info' = appendDefs (MkKV id arg) info in          -- bind constructor pi
  equal info' body ty
check info (Case arg ls) ty =
  foldl checkPath True ls where
    checkPath : Bool -> (Pat, Fn) -> Bool
    checkPath orig (pat, fn) =
      let Just fn' = patType pat                        -- get pi type of constructor
        | Nothing => False in
      let Just val' = patVal pat                        -- get value to bind with arg
        | Nothing => False in
      let Just info' = bindPat val' fn'                 -- bind arguments of pattern from it's pi type
        | Nothing => False in
      check info' fn ty where                           -- check each path
      patType : Pat -> Maybe Fn
      patType (Cons a) = find a info.decs
      patType (Arg a x) = patType x
      patVal : Pat -> Maybe Fn
      patVal (Cons a) = Just (Lit a)
      patVal (Arg a x) =
        let Just fn = patVal x
          | Nothing => Nothing in
        Just (App fn (Lit a))
      bindPat : Fn -> Fn -> Maybe Info
      bindPat val (Lit a) =
        let Lit id = arg                                -- bind arg decs and defs only when arg is literal
          | _ => Just info in
        let info' = appendDecs (MkKV id (Lit a)) info in
        let info' = appendDefs (MkKV id val) info' in
        Just info'
      bindPat val (Pi id ty body) =
        let Just info' = bindPat val body               -- bind argument literal
          | Nothing => Nothing in
        Just $ appendDecs (MkKV id ty) info'            -- TODO argument of original pattern is not bound!
      bindPat _ _ = Nothing
check info _ _ = False

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
