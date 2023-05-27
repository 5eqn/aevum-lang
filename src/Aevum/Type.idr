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


mutual
  -- Pattern matching

  ||| Match an argument against a pattern, returns new defs and match result.
  match : List Dec -> List (Fn, Fn) -> Fn -> Maybe (List Def, Fn)
  match decs ls arg = foldl tryMatch Nothing ls where
    tryMatch : Maybe (List Def, Fn) -> (Fn, Fn) -> Maybe (List Def, Fn)
    tryMatch Nothing (pat, fn) =
      let Just bound = bindPat pat arg
        | Nothing => Nothing in
      Just (bound, fn) where
      bindPat : Fn -> Fn -> Maybe (List Def)
      bindPat (Lit a) (Lit b) =
        if a == b then Just [] else Nothing
      bindPat (App f a) (App g b) =
        let Just bound = bindPat f g
          | Nothing => Nothing in
        let Lit n = a
          | _ => (let Success = equal decs a b | _ => Nothing in Just bound) in
        let Nothing = findDec n decs
          | _ => (let Success = equal decs a b | _ => Nothing in Just bound) in
        Just $ n @= b :: bound
      bindPat _ _ = Nothing
    tryMatch res _ = res
  
  ||| Bind variables across two patterns to check if their corresponding fn equals.
  diffPat : List Dec -> Fn -> Fn -> Maybe (List Def)
  diffPat decs (Lit a) (Lit b) = 
    if a == b then Just [] else Nothing
  diffPat decs (App x (Lit a)) (App y (Lit b)) =
    let Just defs = diffPat decs x y
      | Nothing => Nothing in
    case (findDec a decs, findDec b decs) of
      (Nothing, Nothing) => Just $ a @= Lit b :: defs
      (Just _, Just _) => if a == b then Just defs else Nothing
      _ => Nothing
  diffPat decs (App x a) (App y b) =
    let Success = equal decs a b
      | _ => Nothing in
    let Just defs = diffPat decs x y
      | Nothing => Nothing in
    Just defs
  diffPat decs _ _ = Nothing
  
  ||| Bind declaration for a pattern when it applies.
  declPat : List Dec -> Fn -> Maybe (List Dec, Fn)
  declPat decs (Lit a) =
    let Just ty = findDec a decs
      | _ => Nothing in
    Just (decs, ty)
  declPat decs (App fn a) =
    let Just (decs, Pi id ty body) = declPat decs fn
      | _ => Nothing in
    let Lit n = a
      | _ => Just (decs, bind [id @= a] body) in
    Just (n @: ty :: decs, bind [id @= a] body)
  declPat defs _ = Nothing

  -- Typecheck

  ||| Expand from definition.
  expand : Nat -> List Dec -> List Def -> Fn -> Fn
  expand 100 decs defs val = val
  expand cnt decs defs Hole = Hole
  expand cnt decs defs (Lit n) = let Nothing = findDef n defs | Just fn => expand (S cnt) decs defs fn in Lit n
  expand cnt decs defs (Pi id ty body) = Pi id (expand (S cnt) decs defs ty) (expand (S cnt) decs defs body)
  expand cnt decs defs (Lam id body) = Lam id (expand (S cnt) decs defs body)
  expand cnt decs defs (App fn arg) = App (expand (S cnt) decs defs fn) (expand (S cnt) decs defs arg)
  expand cnt decs defs (Case arg ls) =
    let Nothing = match decs ls arg
      | Just (defs', body) => expand (S cnt) decs defs' body in
    Case (expand (S cnt) decs defs arg) ls

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
  norm : List Dec -> (inj : Fn -> Fn) -> Fn -> Fn
  norm decs inj Hole = Hole
  norm decs inj fn@(Lit n) = fn
  norm decs inj (Pi id ty body) = Pi id (norm decs inj ty) (norm decs inj body)
  norm decs inj (Lam id body) = Lam id (norm decs inj body)
  norm decs inj (App fn arg) =
    let Lam id body = fn
      | _ => App (norm decs inj fn) (norm decs inj arg) in
    norm decs inj (bind [id @= arg] body)
  norm decs inj (Case arg ls) =
    let Nothing = match decs ls arg
      | Just (defs, body) => bind defs (norm decs inj (inj body)) in
    Case (norm decs inj arg) (map normCase ls) where
      normCase : (Fn, Fn) -> (Fn, Fn)
      normCase (pat, fn) = (pat, norm decs inj fn)
  
  ||| Check if two terms equal.
  equal : List Dec -> Fn -> Fn -> CheckResult
  equal decs (Lit n) (Lit m) =
    if n == m then Success else Fail ("\n  " ++ pack n ++ " not equals " ++ pack m)
  equal decs fn1@(Pi n a x) fn2@(Pi m b y) =
    let Success = equal decs a b
      | Fail msg => Fail ("\n  when comparing " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in
    equal decs x (bind [m @= Lit n] y)
  equal decs (Lam n x) (Lam m y) =
    equal decs x (bind [m @= Lit n] y)
  equal decs fn1@(App fn arg) fn2@(App fn' arg') =
    let Success = equal decs fn fn'
      | Fail msg => Fail ("\n  when comparing functions of " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in
    let Success = equal decs arg arg'
      | Fail msg => Fail ("\n  when comparing arguments of " ++ show fn1 ++ " and " ++ show fn2 ++ ": " ++ msg) in Success
  equal decs (Case arg ls) (Case arg' ls') =
    let Success = equal decs arg arg' 
      | fail => fail in
    foldl contains Success ls where
      contains : CheckResult -> (Fn, Fn) -> CheckResult
      contains orig (pat, fn) = foldl same (Fail "\n  no matching case") ls' where
        same : CheckResult -> (Fn, Fn) -> CheckResult
        same orig (pat', fn') =
          let Just defs' = diffPat decs pat pat'
            | Nothing => orig in
          equal decs fn (bind defs' fn')
  equal decs Hole _ = Success
  equal decs _ Hole = Success
  equal decs lhs rhs = Fail ("\n  " ++ show lhs ++ " not equals " ++ show rhs)
  
  ||| Expand and equal.
  eq : List Dec -> List Def -> Fn -> Fn -> CheckResult
  eq decs defs a b =
    let a' = norm decs (expand Z decs defs) (expand Z decs defs a) in
    let b' = norm decs (expand Z decs defs) (expand Z decs defs b) in
    let Success = equal decs a' b'
      | Fail msg => Fail ("\n  when comparing\n    " ++ show a ++ " = " ++ show a' ++ "\n    " ++ show b ++ " = " ++ show b' ++ ": " ++ msg) in Success
  
  ||| Check if a value is of expected type.
  public export
  check : List Dec -> List Def -> (value : Fn) -> (expected : Fn) -> CheckResult
  check decs defs (Lit n) fn =
    let Just ty = findDec n decs
      | Nothing => Fail ("\n  " ++ pack n ++ " is not declared") in
    let Success = eq decs defs ty fn
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
    let Success = eq decs defs ty exp 
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
        | Fail msg => Right ("\n  when checking arg " ++ show (Lit fn) ++ " and " ++ show arg ++ ": " ++ msg) in
      Left (bind [id @= arg] body)
    checkArg fn arg = Right ("\n  " ++ show fn ++ " is not applicable")
  check decs defs (Case arg ls) ty =
    foldl checkPath Success ls where
      checkPath : CheckResult -> (Fn, Fn) -> CheckResult
      checkPath Success (pat, fn) = 
        let Just (decs, argTy) = declPat decs pat
          | Nothing => Fail ("\n  pattern " ++ show pat ++ " is invalid") in
        let Success = check decs defs arg argTy
          | Fail msg => Fail ("\n  when checking pattern " ++ show pat ++ " with arg " ++ show arg ++ ": " ++ msg) in
        let Lit n = arg
          | _ => check decs defs fn ty in
        check decs (n @= pat :: defs) fn ty
      checkPath fail _ = fail
  check decs defs Hole _ = Success
  check decs defs _ Hole = Success
  check decs defs lhs rhs = Fail ("\n  " ++ show lhs ++ " is not " ++ show rhs)
