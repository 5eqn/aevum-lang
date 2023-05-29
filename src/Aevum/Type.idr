module Aevum.Type

infixl 8 @:
infixl 8 @=

-- Datatypes

public export
Checked : Type -> Type
Checked = Either String

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

public export
Show Fn where
  show Hole = "?"
  show (Lit name) = pack name
  show (Pi id ty body) = "(" ++ pack id ++ " : " ++ show ty ++ ") -> " ++ show body
  show (Lam id body) = "\\" ++ pack id ++ " => " ++ show body
  show (App fn arg) = show fn ++ " (" ++ show arg ++ ")"
  show (Case arg ls) =
    "case " ++ show arg ++ " of { " ++ foldl showCases "" ls ++ "}" where
    showCases : String -> (Fn, Fn) -> String
    showCases orig (pat, fn) =
      orig ++ assert_total (show pat) ++ " => "  ++ assert_total (show fn) ++ "; "

public export
data Dec = (@:) Name Fn

public export
data Def = (@=) Name Fn

public export
Show Dec where
  show (a @: b) = "Dec " ++ show a ++ " : " ++ show b

public export
Show Def where
  show (a @= b) = "Def " ++ show a ++ " = " ++ show b

public export
findDec : Name -> List Dec -> Checked Fn
findDec name [] = Left ""
findDec name ((key @: val) :: b) = if key == name then Right val else findDec name b

public export
findDef : Name -> List Def -> Checked Fn
findDef name [] = Left ""
findDef name ((key @= val) :: b) = if key == name then Right val else findDef name b

mutual

  ||| Expand from definition.
  expand : List Dec -> List Def -> Fn -> Fn
  expand decs defs Hole = Hole
  expand decs defs (Lit n) =
    let Right fn = findDef n defs | Left _ => Lit n in
    expand decs defs fn
  expand decs defs (Pi id ty body) =
    Pi id (expand decs defs ty) (expand decs defs body)
  expand decs defs fn@(Lam id body) =
    let Left _ = findDef id defs | Right _ => fn in Lam id (expand decs defs body)
  expand decs defs (App fn arg) = App (expand decs defs fn) (expand decs defs arg)
  expand decs defs (Case arg ls) = Case (expand decs defs arg) ls

  ||| Bind pi / lambda argument.
  bind : List Def -> Fn -> Fn
  bind defs Hole = Hole
  bind defs fn@(Lit n) =
    let Left _ = findDef n defs | Right val => val in fn
  bind defs (Pi id ty body) = Pi id (bind defs ty) (bind defs body)
  bind defs fn@(Lam id body) =
    let Left _ = findDef id defs | Right _ => fn in Lam id (bind defs body)
  bind defs (App fn arg) = App (bind defs fn) (bind defs arg)
  bind defs (Case arg ls) = Case (bind defs arg) (map bindCase ls) where
    bindCase : (Fn, Fn) -> (Fn, Fn)
    bindCase (pat, fn) = (bind defs pat, bind defs fn)
  
  ||| Normalize lambda and cased expressions.
  ||| Injected function is applied when case choice is committed.
  norm : List Dec -> (inj : Fn -> Fn) -> Fn -> Fn
  norm decs inj Hole = Hole
  norm decs inj fn@(Lit n) = fn
  norm decs inj (Pi id ty body) = Pi id (norm decs inj ty) (norm decs inj body)
  norm decs inj (Lam id body) = Lam id (norm decs inj body)
  norm decs inj (App fn arg) =
    let Lam id body = fn | _ => App (norm decs inj fn) (norm decs inj arg) in
    norm decs inj (bind [id @= arg] body)
  norm decs inj (Case arg ls) =
    let Left _ = match decs ls arg
      | Right (defs, body) => bind defs (norm decs inj (inj body)) in
    Case (norm decs inj arg) (map normCase ls) where
      normCase : (Fn, Fn) -> (Fn, Fn)
      normCase (pat, fn) = (pat, norm decs inj fn)
      match : List Dec -> List (Fn, Fn) -> Fn -> Checked (List Def, Fn)
      match decs ls arg = foldl tryMatch (Left "") ls where
        tryMatch : Checked (List Def, Fn) -> (Fn, Fn) -> Checked (List Def, Fn)
        tryMatch (Left _) (pat, fn) = do
          bound <- bindPat pat arg
          pure (bound, fn) where
          bindPat : Fn -> Fn -> Checked (List Def)
          bindPat (Lit a) (Lit b) = if a == b then pure [] else Left ""
          bindPat (App f a) (App g b) = do
            bound <- bindPat f g
            let Lit n = a | _ => do equal decs a b >> pure bound  -- TODO use normEqual
            let Left _ = findDec n decs | _ => do equal decs a b >> pure bound
            pure $ n @= b :: bound
          bindPat _ _ = Left ""
        tryMatch res _ = res
  
  ||| Check if two terms equal.
  equal : List Dec -> Fn -> Fn -> Checked ()
  equal decs (Lit n) (Lit m) = if n == m then pure () else Left ""
  equal decs fn1@(Pi n a x) fn2@(Pi m b y) = do
    logEqual decs a b
    logEqual decs x (bind [m @= Lit n] y)
  equal decs (Lam n x) (Lam m y) = logEqual decs x (bind [m @= Lit n] y)
  equal decs fn1@(App fn arg) fn2@(App fn' arg') = do
    logEqual decs fn fn'
    logEqual decs arg arg'
  equal decs (Case arg ls) (Case arg' ls') = do
    logEqual decs arg arg'
    foldl contains (Right ()) ls where
      contains : Checked () -> (Fn, Fn) -> Checked ()
      contains orig (pat, fn) = foldl same (Left "") ls' where
        same : Checked () -> (Fn, Fn) -> Checked ()
        same orig (pat', fn') =
          let Right defs' = diffPat decs pat pat' | Left _ => orig in
          logEqual decs fn (bind defs' fn') where
          diffPat : List Dec -> Fn -> Fn -> Checked (List Def)
          diffPat decs (Lit a) (Lit b) = if a == b then Right [] else Left ""
          diffPat decs (App x (Lit a)) (App y (Lit b)) = do
            defs <- diffPat decs x y
            case (findDec a decs, findDec b decs) of
              (Left _, Left _) => Right $ a @= Lit b :: defs
              (Right _, Right _) => if a == b then Right defs else Left ""
              _ => Left ""
          diffPat decs (App x a) (App y b) = do
            equal decs a b  -- TODO use normEqual
            diffPat decs x y
          diffPat decs _ _ = Left ""
  equal decs Hole _ = Right ()
  equal decs _ Hole = Right ()
  equal decs lhs rhs = Left ""

  ||| Check if a value is of expected type.
  check : List Dec -> List Def -> (val : Fn) -> (exp : Fn) -> Checked ()
  check decs defs (Lit n) fn = do
    ty <- findDec n decs
    normEqual decs defs ty fn
  check decs defs fn1@(Pi id ty body) exp = do
    normEqual decs defs exp (Lit $ unpack "Type")
    logCheck (id @: ty :: decs) defs ty (Lit $ unpack "Type")
    logCheck (id @: ty :: decs) defs body (Lit $ unpack "Type")
  check decs defs (Lam n x) (Pi m b y) =
    logCheck (n @: b :: decs) defs x (bind [m @= Lit n] y)
  check decs defs fn1@(App fn arg) exp = do
    ty <- checkArg fn arg
    normEqual decs defs ty exp where
    checkArg : Fn -> Fn -> Checked Fn
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
      checkPath : Checked () -> (Fn, Fn) -> Checked ()
      checkPath (Right ()) (pat, fn) = do
        (decs, argTy) <- declPat decs defs pat
        logCheck decs defs arg argTy
        let Lit n = arg | _ => logCheck decs defs fn ty
        logCheck decs (n @= pat :: defs) fn ty where
        declPat : List Dec -> List Def -> Fn -> Checked (List Dec, Fn)
        declPat decs defs (Lit a) = pure (decs, !(findDec a decs))
        declPat decs defs (App fn a) = do
          (decs, Pi id ty body) <- declPat decs defs fn | _ => Left ""
          let Lit n = a | _ => Right (decs, bind [id @= a] body)
          let Right ty' = findDec n decs
            | Left _ => pure (n @: ty :: decs, bind [id @= a] body)
          normEqual decs defs ty ty'
          pure (decs, bind [id @= a] body)
        declPat decs defs _ = Left ""
      checkPath fail _ = fail
  check decs defs Hole _ = Right ()
  check decs defs _ Hole = Right ()
  check decs defs lhs rhs = Left ""

  ||| Compare and log.
  logEqual : List Dec -> Fn -> Fn -> Checked ()
  logEqual decs lhs rhs = case equal decs lhs rhs of
    Right () => Right ()
    Left err => Left ("\n  " ++ show lhs ++ " neq " ++ show rhs ++ ";" ++ err)
  
  ||| Expand, norm, compare and log.
  normEqual : List Dec -> List Def -> Fn -> Fn -> Checked ()
  normEqual decs defs a b =
    let a' = norm decs (expand decs defs) (expand decs defs a) in
    let b' = norm decs (expand decs defs) (expand decs defs b) in
    logEqual decs a' b'

  ||| Check and log.
  logCheck : List Dec -> List Def -> (val : Fn) -> (exp : Fn) -> Checked ()
  logCheck decs defs val exp = case check decs defs val exp of
    Right () => Right ()
    Left err => Left ("\n  " ++ show val ++ " is not " ++ show exp ++ ";" ++ err)

public export
normCheck : List Dec -> List Def -> (val : Fn) -> (exp : Fn) -> Checked ()
normCheck decs defs val exp = logCheck decs defs (norm decs id val) (norm decs id exp)
