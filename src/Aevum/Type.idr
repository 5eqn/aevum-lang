module Aevum.Type

infixl 8 @:
infixl 8 @=

-- Datatypes

||| Type of function name.
public export
Name : Type
Name = List Char

||| Representation of function.
public export
data Fn : Type where
  Hole : Fn
  Lit : Name -> Fn
  Pi : Name -> Fn -> Fn -> Fn
  Lam : Name -> Fn -> Fn
  App : Fn -> Fn -> Fn
  Case : Fn -> List (Fn, Fn) -> Fn

||| Literal "Type".
public export
type : Fn
type = Lit $ unpack "Type"

||| Serialize function.
public export covering
Show Fn where
  show Hole = "?"
  show (Lit name) = pack name
  show (Pi id ty body) = "(" ++ pack id ++ " : " ++ show ty ++ ") -> " ++ show body
  show (Lam id body) = "\\" ++ pack id ++ " => " ++ show body
  show (App fn arg) = show fn ++ " (" ++ show arg ++ ")"
  show (Case arg ls) = "case " ++ show arg ++ " of { " ++ foldl showCases "" ls ++ "}" where
    showCases : String -> (Fn, Fn) -> String
    showCases orig (pat, fn) = orig ++ show pat ++ " => "  ++ show fn ++ "; "

public export
data Dec : Type where
  (@:) : Name -> Fn -> Dec

public export
data Def : Type where
  (@=) : Name -> Fn -> Def

covering
public export
Show Dec where
  show (a @: b) = "Dec " ++ show a ++ " : " ++ show b

covering
public export
Show Def where
  show (a @= b) = "Def " ++ show a ++ " = " ++ show b

public export
findDec : Name -> List Dec -> Maybe Fn
findDec name [] = Nothing
findDec name ((key @: val) :: b) = if key == name then Just val else findDec name b

public export
findDef : Name -> List Def -> Maybe Fn
findDef name [] = Nothing
findDef name ((key @= val) :: b) = if key == name then Just val else findDef name b

||| Representation of typecheck result.
public export
data CheckResult : Type where
  Success : CheckResult
  Fail : String -> CheckResult

||| "And" operator for `CheckResult`.
public export
(&&) : CheckResult -> CheckResult -> CheckResult
(&&) a b = let Success = a | fail => fail in b

-- Typecheck

||| Match an argument against a pattern, returns new defs and match result.
match : List (Fn, Fn) -> Fn -> Maybe (List Def, Fn)
match ls arg = foldl tryMatch Nothing ls where
  tryMatch : Maybe (List Def, Fn) -> (Fn, Fn) -> Maybe (List Def, Fn)
  tryMatch Nothing (pat, fn) =
    let Just defs = bindPat pat arg
      | Nothing => Nothing in
    Just (defs, fn) where
    bindPat : Fn -> Fn -> Maybe (List Def)
    bindPat (Lit a) (Lit b) =
      if a == b then Just [] else Nothing
    bindPat (App x (Lit a)) (App f (Lit b)) =  -- TODO HANDLE ALREADY-DEFINED ARGUMENT
      let Just defs = bindPat x f
        | Nothing => Nothing in
      Just $ a @= Lit b :: defs
    bindPat _ _ = Nothing
  tryMatch res _ = res

||| Expand from definition.
expand : Nat -> List Def -> Fn -> Fn
expand 100 defs val = val
expand cnt defs Hole = Hole
expand cnt defs (Lit n) = let Nothing = findDef n defs | Just fn => expand (S cnt) defs fn in Lit n
expand cnt defs (Pi id ty body) = Pi id (expand (S cnt) defs ty) (expand (S cnt) defs body)
expand cnt defs (Lam id body) = Lam id (expand (S cnt) defs body)
expand cnt defs (App fn arg) = App (expand (S cnt) defs fn) (expand (S cnt) defs arg)
expand cnt defs (Case arg ls) =
  let Nothing = match ls arg
    | Just (defs', body) => expand (S cnt) defs' body in
  Case (expand (S cnt) defs arg) ls

||| Bind pi / lambda argument.
bind : List Def -> Fn -> Fn
bind defs Hole = Hole
bind defs fn@(Lit n) = let Nothing = findDef n defs | Just val => val in fn
bind defs (Pi id ty body) = Pi id (bind defs ty) (bind defs body)
bind defs fn@(Lam id body) = let Nothing = findDef id defs | Just _ => fn in Lam id (bind defs body)
bind defs (App fn arg) = App (bind defs fn) (bind defs arg)
bind defs (Case arg ls) =
  Case (bind defs arg) (map bindCase ls) where
    bindCase : (Fn, Fn) -> (Fn, Fn)
    bindCase (pat, fn) = (bind defs pat, bind defs fn)

||| Normalize lambda and cased expressions. Injected function is applied when case choice is committed.
public export
norm : (inj : Fn -> Fn) -> Fn -> Fn
norm inj Hole = Hole
norm inj fn@(Lit n) = fn
norm inj (Pi id ty body) = Pi id (norm inj ty) (norm inj body)
norm inj (Lam id body) = Lam id (norm inj body)
norm inj (App fn arg) =
  let Lam id body = fn
    | _ => App (norm inj fn) (norm inj arg) in
  norm inj (bind [id @= arg] body)
norm inj (Case arg ls) =
  let Nothing = match ls arg
    | Just (defs, body) => bind defs (norm inj (inj body)) in
  Case (norm inj arg) (map normCase ls) where
    normCase : (Fn, Fn) -> (Fn, Fn)
    normCase (pat, fn) = (pat, norm inj fn)

||| Bind variables across two patterns to check if their corresponding fn equals.
diffPat : Fn -> Fn -> Maybe (List Def)
diffPat (Lit a) (Lit b) = 
  if a == b then Just [] else Nothing
diffPat (App x (Lit a)) (App y (Lit b)) =
  let Just defs = diffPat x y
    | Nothing => Nothing in
  Just $ a @= Lit b :: defs
diffPat _ _ = Nothing

||| Bind declaration for a pattern when it applies.
declPat : List Dec -> Fn -> Maybe (List Dec, Fn)
declPat decs (Lit a) =
  let Just ty = findDec a decs
    | _ => Nothing in
  Just (decs, ty)
declPat decs (App fn (Lit a)) =
  let Just (decs, Pi id ty body) = declPat decs fn
    | _ => Nothing in
  Just (a @: ty :: decs, bind [id @= Lit a] body)
declPat defs _ = Nothing

||| Check if two terms equal.
equal : Fn -> Fn -> CheckResult
equal (Lit n) (Lit m) =
  if n == m then Success else Fail ("\n  " ++ pack n ++ " not equals " ++ pack m)
equal fn1@(Pi n a x) fn2@(Pi m b y) =
  let Success = equal a b
    | Fail msg => Fail ("\n  when comparing " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in
  equal x (bind [m @= Lit n] y)
equal (Lam n x) (Lam m y) =
  equal x (bind [m @= Lit n] y)
equal fn1@(App fn arg) fn2@(App fn' arg') =
  let Success = equal fn fn'
    | Fail msg => Fail ("\n  when comparing functions of " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in
  let Success = equal arg arg'
    | Fail msg => Fail ("\n  when comparing arguments of " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in Success
equal (Case arg ls) (Case arg' ls') =
  let Success = equal arg arg' 
    | fail => fail in
  foldl contains Success ls where
    contains : CheckResult -> (Fn, Fn) -> CheckResult
    contains orig (pat, fn) = foldl same (Fail "\n  no matching case") ls' where
      same : CheckResult -> (Fn, Fn) -> CheckResult
      same orig (pat', fn') =
        let Just defs' = diffPat pat pat'
          | Nothing => orig in
        equal fn (bind defs' fn')
equal Hole _ = Success
equal _ Hole = Success
equal lhs rhs = Fail ("\n  " ++ show lhs ++ " not equals " ++ show rhs)

||| Expand and equal.
eq : List Def -> Fn -> Fn -> CheckResult
eq defs a b =
  let a' = norm (expand Z defs) (expand Z defs a) in
  let b' = norm (expand Z defs) (expand Z defs b) in
  let Success = equal a' b'
    | Fail msg => Fail ("\n  when comparing\n    " ++ show a ++ " = " ++ show a' ++ "\n    " ++ show b ++ " = " ++ show b' ++ ": " ++ msg) in Success

||| Check if a value is of expected type.
public export
check : List Dec -> List Def -> (value : Fn) -> (expected : Fn) -> CheckResult
check decs defs (Lit n) fn =
  let Just ty = findDec n decs
    | Nothing => Fail ("\n  " ++ pack n ++ " is not declared") in
  let Success = eq defs ty fn
    | Fail msg => Fail ("\n  when checking " ++ pack n ++ " and " ++ show fn ++ ": " ++ msg) in Success
check decs defs fn1@(Pi id ty body) (Lit n) =
  if pack n == "Type" 
  then Success
  else Fail ("\n  " ++ show fn1 ++ " is not " ++ pack n) &&
  check decs defs ty type && 
  check decs defs body type
check decs defs (Lam n x) (Pi m b y) =
  check (n @: b :: m @: b :: decs) defs x (bind [m @= Lit n] y)
check decs defs fn1@(App fn arg) exp =
  let Left ty = checkArg fn arg
    | Right msg => Fail msg in
  let Success = eq defs ty exp 
    | Fail msg => Fail ("\n  when checking " ++ show fn1 ++ " and " ++ show exp ++ ": " ++ msg) in Success where
  checkArg : Fn -> Fn -> Either Fn String
  checkArg (App fn arg) arg' =
    let Left $ Pi id ty body = checkArg fn arg
      | Left ty => Right ("\n  " ++ show fn ++ " : " ++ show ty ++ " is not applicable")
      | Right msg => Right ("\n  when checking fn " ++ show (App fn arg) ++ " and " ++ show arg' ++ ": " ++ msg) in
    let Success = check decs defs arg' ty
      | Fail msg => Right ("\n  when checking arg " ++ show (App fn arg) ++ " and " ++ show arg' ++ ": " ++ msg) in
    Left (bind [id @= arg'] body)
  checkArg (Lit fn) arg =
    let Just (Pi id ty body) = findDec fn decs
      | _ => Right ("\n  " ++ pack fn ++ " is not a function") in
    let Success = check decs defs arg ty
      | Fail msg => Right ("\n  when checking arg (" ++ show (Lit fn) ++ ", " ++ show arg ++ ":) " ++ msg) in
    Left (bind [id @= arg] body)
  checkArg fn arg = Right ("\n  " ++ show fn ++ " is not applicable")
check decs defs (Case arg ls) ty =
  foldl checkPath Success ls where
    checkPath : CheckResult -> (Fn, Fn) -> CheckResult
    checkPath Success (pat, fn) = 
      let Just (decs, _) = declPat decs pat
        | Nothing => Fail ("\n  pattern " ++ show pat ++ " is invalid") in
      let Lit n = arg
        | _ => check decs defs fn ty in
      check decs (n @= pat :: defs) fn ty
    checkPath fail _ = fail
check decs defs Hole _ = Success
check decs defs _ Hole = Success
check decs defs lhs rhs = Fail ("\n  " ++ show lhs ++ " is not " ++ show rhs)
