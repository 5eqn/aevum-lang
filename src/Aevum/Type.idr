module Aevum.Type

infixl 8 @:
infixl 8 @=

-- Datatypes

public export
Name : Type
Name = List Char

public export
data Fn : Type where
  Hole : Fn
  Lit : Name -> Fn
  Pi : Name -> Fn -> Fn -> Fn
  Lam : Name -> Fn -> Fn
  App : Fn -> Fn -> Fn
  Case : Fn -> List (Fn, Fn) -> Fn

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
data Dec = (@:) Name Fn

public export
data Def = (@=) Name Fn

public export covering
Show Dec where
  show (a @: b) = "Dec " ++ show a ++ " : " ++ show b

public export covering
Show Def where
  show (a @= b) = "Def " ++ show a ++ " = " ++ show b

public export
findDec : Name -> List Dec -> Either String Fn
findDec name [] = Left ""
findDec name ((key @: val) :: b) = if key == name then Right val else findDec name b

public export
findDef : Name -> List Def -> Either String Fn
findDef name [] = Left ""
findDef name ((key @= val) :: b) = if key == name then Right val else findDef name b

mutual

  -- Pattern matching

  ||| Match an argument against a pattern, returns new defs and match result.
  match : List Dec -> List (Fn, Fn) -> Fn -> Either String (List Def, Fn)
  match decs ls arg = foldl tryMatch (Left "") ls where
    tryMatch : Either String (List Def, Fn) -> (Fn, Fn) -> Either String (List Def, Fn)
    tryMatch (Left _) (pat, fn) = do
      bound <- bindPat pat arg; pure (bound, fn) where
      bindPat : Fn -> Fn -> Either String (List Def)
      bindPat (Lit a) (Lit b) = if a == b then pure [] else Left ""
      bindPat (App f a) (App g b) = do
        bound <- bindPat f g
        let Lit n = a | _ => do equal decs a b; pure bound
        let Left _ = findDec n decs | _ => do equal decs a b; pure bound
        pure $ n @= b :: bound
      bindPat _ _ = Left ""
    tryMatch res _ = res
  
  ||| Bind variables across two patterns to check if their corresponding fn equals.
  diffPat : List Dec -> Fn -> Fn -> Either String (List Def)
  diffPat decs (Lit a) (Lit b) = if a == b then Right [] else Left ""
  diffPat decs (App x (Lit a)) (App y (Lit b)) = do
    defs <- diffPat decs x y
    case (findDec a decs, findDec b decs) of
      (Left _, Left _) => Right $ a @= Lit b :: defs
      (Right _, Right _) => if a == b then Right defs else Left ""
      _ => Left ""
  diffPat decs (App x a) (App y b) = do
    equal decs a b; defs <- diffPat decs x y; pure defs
  diffPat decs _ _ = Left ""
  
  ||| Bind declaration for a pattern when it applies.
  declPat : List Dec -> Fn -> Either String (List Dec, Fn)
  declPat decs (Lit a) = do ty <- findDec a decs; pure (decs, ty)
  declPat decs (App fn a) = do
    (decs, Pi id ty body) <- declPat decs fn | _ => Left ""
    let Lit n = a | _ => Right (decs, bind [id @= a] body)
    pure (n @: ty :: decs, bind [id @= a] body)
  declPat defs _ = Left ""

  -- Typecheck

  ||| Expand from definition.
  expand : Nat -> List Dec -> List Def -> Fn -> Fn
  expand 100 decs defs val = val
  expand cnt decs defs Hole = Hole
  expand cnt decs defs (Lit n) = let Left _ = findDef n defs | Right fn => expand (S cnt) decs defs fn in Lit n
  expand cnt decs defs (Pi id ty body) = Pi id (expand (S cnt) decs defs ty) (expand (S cnt) decs defs body)
  expand cnt decs defs (Lam id body) = Lam id (expand (S cnt) decs defs body)
  expand cnt decs defs (App fn arg) = App (expand (S cnt) decs defs fn) (expand (S cnt) decs defs arg)
  expand cnt decs defs (Case arg ls) =
    let Left _ = match decs ls arg
      | Right (defs', body) => expand (S cnt) decs defs' body in
    Case (expand (S cnt) decs defs arg) ls

  ||| Bind pi / lambda argument.
  bind : List Def -> Fn -> Fn
  bind defs Hole = Hole
  bind defs fn@(Lit n) = let Left _ = findDef n defs | Right val => val in fn
  bind defs (Pi id ty body) = Pi id (bind defs ty) (bind defs body)
  bind defs fn@(Lam id body) = let Left _ = findDef id defs | Right _ => fn in Lam id (bind defs body)
  bind defs (App fn arg) = App (bind defs fn) (bind defs arg)
  bind defs (Case arg ls) = Case (bind defs arg) (map bindCase ls) where
    bindCase : (Fn, Fn) -> (Fn, Fn)
    bindCase (pat, fn) = (bind defs pat, bind defs fn)
  
  ||| Normalize lambda and cased expressions. Injected function is applied when case choice is committed.
  norm : List Dec -> (inj : Fn -> Fn) -> Fn -> Fn
  norm decs inj Hole = Hole
  norm decs inj fn@(Lit n) = fn
  norm decs inj (Pi id ty body) = Pi id (norm decs inj ty) (norm decs inj body)
  norm decs inj (Lam id body) = Lam id (norm decs inj body)
  norm decs inj (App fn arg) =
    let Lam id body = fn | _ => App (norm decs inj fn) (norm decs inj arg) in
    norm decs inj (bind [id @= arg] body)
  norm decs inj (Case arg ls) =
    let Left _ = match decs ls arg | Right (defs, body) => bind defs (norm decs inj (inj body)) in
    Case (norm decs inj arg) (map normCase ls) where
      normCase : (Fn, Fn) -> (Fn, Fn)
      normCase (pat, fn) = (pat, norm decs inj fn)
  
  ||| Check if two terms equal.
  equal : List Dec -> Fn -> Fn -> Either String ()
  equal decs (Lit n) (Lit m) = if n == m then pure () else Left ""
  equal decs fn1@(Pi n a x) fn2@(Pi m b y) = do logEqual decs a b; logEqual decs x (bind [m @= Lit n] y)
  equal decs (Lam n x) (Lam m y) = logEqual decs x (bind [m @= Lit n] y)
  equal decs fn1@(App fn arg) fn2@(App fn' arg') = do logEqual decs fn fn'; logEqual decs arg arg'
  equal decs (Case arg ls) (Case arg' ls') = do logEqual decs arg arg'; foldl contains (Right ()) ls where
      contains : Either String () -> (Fn, Fn) -> Either String ()
      contains orig (pat, fn) = foldl same (Left "") ls' where
        same : Either String () -> (Fn, Fn) -> Either String ()
        same orig (pat', fn') =
          let Right defs' = diffPat decs pat pat' | Left _ => orig in
          logEqual decs fn (bind defs' fn')
  equal decs Hole _ = Right ()
  equal decs _ Hole = Right ()
  equal decs lhs rhs = Left ""

  ||| Compare and log.
  logEqual : List Dec -> Fn -> Fn -> Either String ()
  logEqual decs lhs rhs = case equal decs lhs rhs of
    Right () => Right ()
    Left err => Left ("\n  when comparing " ++ show lhs ++ " and " ++ show rhs ++ ";" ++ err)
  
  ||| Expand, norm, compare and log.
  normEqual : List Dec -> List Def -> Fn -> Fn -> Either String ()
  normEqual decs defs a b =
    let a' = norm decs (expand Z decs defs) (expand Z decs defs a) in
    let b' = norm decs (expand Z decs defs) (expand Z decs defs b) in
    logEqual decs a' b'
  
  ||| Check if a value is of expected type.
  check : List Dec -> List Def -> (value : Fn) -> (expected : Fn) -> Either String ()
  check decs defs (Lit n) fn = do ty <- findDec n decs; normEqual decs defs ty fn
  check decs defs fn1@(Pi id ty body) (Lit n) = do
    (if pack n == "Type" then pure () else Left "")
    check (id @: ty :: decs) defs ty (Lit $ unpack "Type")
    check (id @: ty :: decs) defs body (Lit $ unpack "Type")
  check decs defs (Lam n x) (Pi m b y) = logCheck (n @: b :: decs) defs x (bind [m @= Lit n] y)
  check decs defs fn1@(App fn arg) exp = do ty <- checkArg fn arg; normEqual decs defs ty exp where
    checkArg : Fn -> Fn -> Either String Fn
    checkArg (App fn arg) arg' = do
      Pi id ty body <- checkArg fn arg | ty => Left ""
      logCheck decs defs arg' ty
      pure (bind [id @= arg'] body)
    checkArg (Lit fn) arg = do
      Pi id ty body <- findDec fn decs | _ => Left ""
      logCheck decs defs arg ty
      pure (bind [id @= arg] body)
    checkArg fn arg = Left ""
  check decs defs (Case arg ls) ty =
    foldl checkPath (Right ()) ls where
      checkPath : Either String () -> (Fn, Fn) -> Either String ()
      checkPath (Right ()) (pat, fn) = do
        (decs, argTy) <- declPat decs pat
        logCheck decs defs arg argTy
        let Lit n = arg | _ => logCheck decs defs fn ty
        logCheck decs (n @= pat :: defs) fn ty
      checkPath fail _ = fail
  check decs defs Hole _ = Right ()
  check decs defs _ Hole = Right ()
  check decs defs lhs rhs = Left ""

  ||| Check and log.
  logCheck : List Dec -> List Def -> (value : Fn) -> (expected : Fn) -> Either String ()
  logCheck decs defs val exp = case check decs defs val exp of
    Right () => Right ()
    Left err => Left ("\n  when checking " ++ show val ++ " is " ++ show exp ++ ";" ++ err)

public export
normCheck : List Dec -> List Def -> (value : Fn) -> (expected : Fn) -> Either String ()
normCheck decs defs val exp = logCheck decs defs (norm decs id val) (norm decs id exp)
