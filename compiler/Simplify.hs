module Simplify where

import Core
import Panic
import qualified SystemFI             as FI
import qualified Src                  as S
import qualified Language.Java.Syntax as J

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace   (trace)
import Data.Maybe    (fromMaybe)
import Unsafe.Coerce (unsafeCoerce)

simplify :: FI.Expr Index (Index, FI.Type Index) -> Expr Index Index
simplify = transExpr 0 0

infer :: Index -> Index -> FI.Expr Index (Index, FI.Type Index) -> FI.Type Index
infer i j (FI.Var _ (_, t)) = t
infer i j (FI.Lit (S.Int    _)) = FI.JClass "java.lang.Integer"
infer i j (FI.Lit (S.String _)) = FI.JClass "java.lang.String"
infer i j (FI.Lit (S.Bool   _)) = FI.JClass "java.lang.Boolean"
infer i j (FI.Lit (S.Char   _)) = FI.JClass "java.lang.Character"
infer i j (FI.Lam n t f) = FI.Fun t $ infer i (j + 1) (f (j, t))
infer i j (FI.Fix _ _ _ t1 t) = FI.Fun t1 t
infer i j (FI.Let _ b f) = infer i (j + 1) $ f (j, infer i j b)
infer i j (FI.LetRec _ ts _ e) = infer i (j + n) $ e (zip [j..j+n-1] ts)
  where n = length ts
infer i j (FI.BLam n f) = FI.Forall n (\a -> FI.fsubstTT i (FI.TVar n a) . infer (i + 1) j $ f i)
infer i j (FI.App f x) = t where FI.Fun _ t = infer i j f
--infer i j FI.TApp ?=
infer i j (FI.If _ e _) = infer i j e
infer i j (FI.PrimOp _ op _) = case op of S.Arith   _ -> FI.JClass "java.lang.Integer"
                                          S.Compare _ -> FI.JClass "java.lang.Boolean"
                                          S.Logic   _ -> FI.JClass "java.lang.Boolean" 
--infer i j FI.Tuple ?=
--infer i j FI.Proj ?=
--infer i j FI.JNew ?=
--infer i j FI.JMethod ?=
--infer i j FI.JField ?=
--infer i j FI.PolyList ?=
--infer i j FI.JProxyCall ?=
--infer i j FI.Seq ?=
--infer i j FI.Merge ?=
--infer i j FI.RecordIntro ?=
--infer i j FI.RecordElim ?=
--infer i j FI.RecordUpdate ?=
--infer i j FI.Constr ?=
--infer i j FI.Case ?=
infer _ _ _ = trace "Wrong1" FI.Unit

transExpr :: Index -> Index -> FI.Expr Index (Index, FI.Type Index) -> Expr Index Index
transExpr i j (FI.Var n (x, _)) = Var n x
transExpr i j (FI.Lit l) = Lit l
transExpr i j (FI.Lam n t f) = Lam n (transType i t) (\x -> fsubstEE j (Var n x) . transExpr i (j + 1) $ f (j, t)) -- why feed f with j before subst, not x directly?
transExpr i j this@(FI.Fix fn pn e t1 t) = Fix fn pn e' t1' t' 
  where
    body = transExpr i (j + 2) $ e (j, infer i j this) (j + 1, t1)
    e'   = \x x1 -> fsubstEE j (Var fn x) . fsubstEE (j + 1) (Var pn x1) $ body
    t1'  = transType i t1
    t'   = transType i t
transExpr i j (FI.Let n b f) = Let n (transExpr i j b) (\x -> fsubstEE j (Var n x) . transExpr i (j + 1) $ f (j, infer i j b))
transExpr i j (FI.LetRec ns ts bs e) = LetRec ns ts' bs' e'
  where
    ts' = map (transType i) ts
    bs' args = map (subst args . trans) . bs $ fs_ts
    e'  args = subst args . trans . e $ fs_ts  
    n = length ts
    fs_ts = zip [j..j+n-1] ts
    trans = transExpr i (j + n)
    subst :: [Index] -> Expr Index Index -> Expr Index Index
    subst rs = foldl (.) id [ fsubstEE x (Var (ns !! k) (rs !! k)) | (x, k) <- zip [j..j+n-1] [0..n-1] ]
transExpr i j (FI.BLam n f) = BLam n (\a -> fsubstTE i (TVar n a) . transExpr (i + 1) j $ f i)
transExpr i j (FI.App f x) =
  let (FI.Fun t1 t2, e1) = (infer i j f, transExpr i j f)
      (t3, e2)           = (infer i j x, transExpr i j x)
      panic_doc          = text "Coercion failed" <$>
                           text "Function: " <> pretty_typing f (FI.Fun t1 t2) <$>
                           text "Argument: " <> pretty_typing x t3 <$>
                           text "Coercion: " <> pretty_coercion t3 t1
      pretty_typing temp1 temp2   = FI.prettyExpr (unsafeCoerce temp1 :: FI.Expr Index Index) <+> colon <+>
                                    FI.prettyType (unsafeCoerce temp2 :: FI.Type Index)
      pretty_coercion temp1 temp2 = FI.prettyType (unsafeCoerce temp1 :: FI.Type Index) <+> text "<:" <+>
                                    FI.prettyType (unsafeCoerce temp2 :: FI.Type Index)
  in let c = fromMaybe (prettyPanic "Simplify.transExpr" panic_doc) (coerce i t3 t1)
     in App e1 (App c e2)
--transExpr i j FI.TApp ?=
transExpr i j (FI.If e1 e2 e3) = If e1' e2' e3'
  where [e1', e2', e3'] = map (transExpr i j) [e1, e2, e3]
transExpr i j (FI.PrimOp e1 op e2) = PrimOp (transExpr i j e1) op (transExpr i j e2)
--transExpr i j FI.Tuple ?=
--transExpr i j FI.Proj ?=
--transExpr i j FI.JNew ?=
--transExpr i j FI.JMethod ?=
--transExpr i j FI.JField ?=
--transExpr i j FI.PolyList ?=
--transExpr i j FI.JProxyCall ?=
--transExpr i j FI.Seq ?=
--transExpr i j FI.Merge ?=
--transExpr i j FI.RecordIntro ?=
--transExpr i j FI.RecordElim ?=
--transExpr i j FI.RecordUpdate ?=
--transExpr i j FI.Constr ?=
--transExpr i j FI.Case ?=
transExpr _ _ _ = trace "Wrong2" (Var "" (-1))

transType :: Index -> FI.Type Index -> Type Index
transType i (FI.TVar n a) = TVar n a
transType i (FI.JClass c) = JClass c 
transType i (FI.Fun a1 a2) = Fun (transType i a1) (transType i a2)
transType i (FI.Forall n f) = Forall n (\a -> transType (i + 1) . FI.fsubstTT i (FI.TVar n a) $ f i) -- why not (f a) directly?
--transType i (FI.Product ts) = 
transType i (FI.Unit) = Unit 
--transType i (FI.And a1 a2) = 
--transType i (FI.Record (_, t)) = 
--transType i (FI.Datatype n ns) = 
--transType i (FI.ListOf t) = 

coerce :: Index -> FI.Type Index -> FI.Type Index -> Maybe (Expr Index Index)
coerce i this@(FI.TVar _ a) (FI.TVar _ b)
  | a == b = return $ lam (transType i this) var
  | otherwise = Nothing
coerce i this@(FI.JClass c) (FI.JClass d)
  | c == d = return $ lam (transType i this) var
  | otherwise = Nothing
--coerce i FI.ListOf FI.ListOf =
coerce i this@(FI.Fun t1 t2) (FI.Fun t3 t4) = do
  c1 <- coerce i t3 t1
  c2 <- coerce i t2 t4
  return $ lam (transType i this) (\f -> lam (transType i t3) ((App c2 . App (var f) . App c1) . var))
--coerce i FI.Forall FI.Forall =
--coerce i FI.Product FI.Product =
coerce i this@(FI.Unit) (FI.Unit) = return $ lam (transType i this) var
--coerce i _ FI.And =
--coerce i FI.Record FI.Record =
--coerce i FI.Datatype FI.Datatype =
coerce _ _ _ = Nothing

test :: Int -> Doc
test id = prettyExpr . simplify $ l !! id
  where l = [setZero, fact, evenOdd, apply]

-- Utils.
jInt  = FI.JClass "java.lang.Integer"
jBool = FI.JClass "java.lang.Boolean"
lit x = FI.Lit (S.Int x)
true  = FI.Lit (S.Bool True)
false = FI.Lit (S.Bool False)
equal = S.Compare J.Equal
add = S.Arith J.Add
sub = S.Arith J.Sub
mul = S.Arith J.Mult

-- let setZero x : Int = 0 in setZero 5
setZero :: FI.Expr Index (Index, FI.Type Index)
setZero = FI.Let "setZero"  (FI.Lam "x" jInt (\x -> lit 0)) (\e -> FI.App (FI.Var "setZero" e) (lit 5))

-- letfix fact n : Int = if n == 0 then 1 else n * fact n - 1 in fact 10
fact :: FI.Expr Index (Index, FI.Type Index)
fact = FI.Let "factorial" (FI.Fix "fact" "n" (\x x1 -> FI.If (FI.PrimOp (FI.Var "n" x1) equal (lit 0)) (lit 1) (FI.PrimOp (FI.Var "n" x1) mul (FI.App (FI.Var "fact" x) (FI.PrimOp (FI.Var "n" x1) sub (lit 1))))) jInt jInt) (\e -> FI.App (FI.Var "factorial" e) (lit 10))

-- letrec even x = if x == 0 then true else odd x-1, odd y = if y == 0 then false else even y-1 in even 50 
evenOdd :: FI.Expr Index (Index, FI.Type Index)
evenOdd = FI.LetRec ["even", "odd"] [FI.Fun jInt jBool, FI.Fun jInt jBool] (\(l1:l2:_) -> [FI.Lam "x" jInt (\x -> FI.If (FI.PrimOp (FI.Var "x" x) equal (lit 0)) true (FI.App (FI.Var "odd" l2) (FI.PrimOp (FI.Var "x" x) sub (lit 1)))), FI.Lam "y" jInt (\y -> FI.If (FI.PrimOp (FI.Var "y" y) equal (lit 0)) false (FI.App (FI.Var "even" l1) (FI.PrimOp (FI.Var "y" y) sub (lit 1))))]) (\(l1:l2:_) -> FI.App (FI.Var "even" l1) (lit 50))

-- let apply P Q [x P] [y Q] [f P -> Q -> Int] = f x y in apply Int Bool 2 True (\m.\n. if n True m + 1 else m).
apply :: FI.Expr Index (Index, FI.Type Index)
apply = FI.Let "apply" app_body (\app -> lit 0)
--  (\app -> FI.App (FI.App (FI.App (FI.TApp (FI.TApp (FI.Var "apply" app) jInt) jBool) (lit 2)) true) lambda_f)

app_body :: FI.Expr Index (Index, FI.Type Index)
app_body = FI.BLam "P" (\p -> FI.BLam "Q" (\q -> FI.Lam "x" (FI.TVar "P" p) (\x -> FI.Lam "y" (FI.TVar "Q" q) (\y -> FI.Lam "f" (FI.Fun (FI.TVar "P" p) (FI.Fun (FI.TVar "Q" q) jInt)) (\f -> FI.App (FI.App (FI.Var "f" f) (FI.Var "x" x)) (FI.Var "y" y))))))

lambda_f :: FI.Expr Index (Index, FI.Type Index)
lambda_f = FI.Lam "m" jInt (\m -> FI.Lam "n" jBool (\n -> FI.If (FI.PrimOp (FI.Var "n" n) equal true) (FI.PrimOp (FI.Var "m" m) add (lit 1)) (FI.Var "m" m)))
