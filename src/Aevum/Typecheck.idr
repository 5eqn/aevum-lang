module Aevum.Typecheck

-- Datatypes

||| Type of function name.
public export
Name : Type
Name = List Char

||| Representation of function.
public export
data Fn : Type where
  Lit : Name -> Fn
  Pi : Name -> Fn -> Fn -> Fn
  Lam : Name -> Fn -> Fn
  App : Fn -> Fn -> Fn
  Case : Fn -> List (Fn, Fn) -> Fn

||| Existing declaration and definition to be remembered.
public export
record Info where
  constructor MkInfo
  decs : List (Name, Fn)
  defs : List (Name, Fn)

||| Equivalent to hashmap "find".
public export
find : Name -> List (Name, Fn) -> Maybe Fn
find name [] = Nothing
find name ((key, val) :: b) = if key == name then Just val else find name b

infixl 3 <+
infixl 3 <*

||| Append declaration.
public export
(<+) : Info -> (Name, Fn) -> Info
(<+) info kv = MkInfo (kv :: info.decs) info.defs

||| Append definition.
public export
(<*) : Info -> (Name, Fn) -> Info
(<*) info kv = MkInfo info.decs (kv :: info.defs)       -- TODO prevent self loop

-- Case split

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
      Just $ info' <* (a, Lit b)
    bindPat _ _ = Nothing
  tryMatch res _ = res

||| Bind variables across two patterns to check if their corresponding fn equals.
diffPat : Info -> Fn -> Fn -> Maybe Info
diffPat info (Lit a) (Lit b) = 
  if a == b then Just info else Nothing
diffPat info (App x (Lit a)) (App y (Lit b)) =
  let Just info' = diffPat info x y
    | Nothing => Nothing in
  Just $ info' <* (a, Lit b)
diffPat _ _ _ = Nothing

||| Bind declaration for a pattern when it applies.
declPat : Info -> Fn -> Maybe Info
declPat info (Lit a) = Just info
declPat info (App (Pi id ty body) (Lit a)) =
  let Just info' = declPat (info <* (id, Lit a) <+ (id, ty)) body
    | Nothing => Nothing in
  Just $ info' <+ (a, ty)
declPat info _ = Nothing

-- Typecheck

||| Simplify a value.
simp : Info -> Fn -> Fn
simp info (Lit n) =
  let Nothing = find n info.defs                        -- find replacement
    | Just fn => simp info fn in
  Lit n
simp info (Pi id ty body) =
  Pi id (simp info ty) (simp info body)                 -- simp argument type and body
simp info (Lam id body) =
  Lam id (simp info body)                               -- simp argument type and body
simp info (App fn arg) =
  let Lam id body = simp info fn                        -- if fn is applied, simplifying it yields a lambda
    | _ => App fn arg in
  simp (info <* (id, arg)) body                         -- bind argument
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
  equal (info <* (n, Lit m)) x y                        -- same body when argument replaced
equal info (Lam n x) (Lam m y) =
  equal (info <* (n, Lit m)) x y                        -- same body when argument replaced
equal info (App fn arg) (App fn' arg') =
  equal info fn fn' && equal info arg arg'              -- constructor and argument should be the same
equal info (Case arg ls) (Case arg' ls') =
  let True = equal info arg arg'                        -- argument must equal 
    | False => False in
  foldl contains True ls where
    contains : Bool -> (Fn, Fn) -> Bool                 -- rhs contains all lhs paths
    contains orig (pat, fn) = foldl same False ls' where
      same : Bool -> (Fn, Fn) -> Bool                   -- one of `ls'` equals each `ls`
      same orig (pat', fn') =
        let Just info' = diffPat info pat pat'          -- check and replace argument
          | Nothing => orig in
        equal info' fn fn'                              -- path with same pattern determines if each `ls` is contained
equal info _ _ = False

||| Check if a simplified value is of a simplified type.
public export
check : Info -> (value : Fn) -> (type : Fn) -> Bool
check info (Lit n) fn =
  let Just ty = find n info.decs                        -- lookup
    | Nothing => False in
  equal info ty fn
check info (Pi _ _ _) (Lit n) = pack n == "Type"        -- pi has type "Type"
check info (Lam n x) (Pi m b y) = 
  check (info <* (n, Lit m) <+ (n, b) <+ (m, b)) x y
check info (App (Lit n) arg) ty =
  let Just (Pi id ty body) = find n info.decs
    | _ => False in
  equal (info <* (id, arg)) body ty
check info (Case arg ls) ty =
  foldl checkPath True ls where
    checkPath : Bool -> (Fn, Fn) -> Bool
    checkPath orig (pat, fn) = 
      let Just info' = declPat info pat                 -- bind pattern declaration
        | Nothing => False in
      let Lit n = arg                                   -- bind pattern to arg when it's literal
        | _ => check info' fn ty in
      check (info' <* (n, pat)) fn ty
check info _ _ = False
