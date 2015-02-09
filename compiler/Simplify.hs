module Simplify where

import Core
import Panic
import qualified SystemFI             as FI
import qualified Src                  as S
import qualified Language.Java.Syntax as J

import Text.PrettyPrint.ANSI.Leijen

import Debug.Trace   (trace)
import Data.Maybe    (fromMaybe)
import Control.Monad (zipWithM)
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

--Old: infer i j (FI.BLam n f) = FI.Forall n (\a -> FI.fsubstTT i (FI.TVar n a) . infer (i + 1) j $ f i)
infer i j (FI.BLam n f) = FI.Forall n (\a -> infer (i + 1) j $ f a)

infer i j (FI.App f x) = t where FI.Fun _ t = infer i j f

infer i j (FI.TApp f x) = substTT (\n a -> if a == i then x else FI.TVar n a) [g i] 
  where FI.Forall n g = infer i j f
-- Note: should be infer i j f actually. There is a bug here.
-- When infer i j f:
-- Example: let apply A B (x : A) (y : B) = 0 in apply Int Bool
-- apply: forall A. forall B. A -> B -> Int
-- (1) infer 0 0 (TApp (TApp apply Int) Bool): should infer 0 0 TApp(apply Int) first.
-- (2) infer 0 0 (TApp apply Int):
--     1. Type of apply:  forall A. forall B. A -> B -> Int
--     2. Pass i = 0:     forall B. TVar 0 -> B -> Int
--     3. Substitution:   forall B. Int    -> B -> Int                           (Expected)
--                        forall B. Int    -> (if B == 0 then Int else B) -> Int (Actual)
-- (3) When Bool comes:
--     Expected:  forall B. Int -> B -> Int
--     (i = 0) => Int -> TVar 0 -> Int
--      (Bool) => Int -> Bool   -> Int
--     Actual:    forall B. Int -> (if B == 0 then Int else B) -> Int
--     (i = 0) => Int -> Int -> Int
--      (Bool) => Int -> Int -> Int

infer i j (FI.If _ e _) = infer i j e
infer i j (FI.PrimOp _ op _) = case op of S.Arith   _ -> FI.JClass "java.lang.Integer"
                                          S.Compare _ -> FI.JClass "java.lang.Boolean"
                                          S.Logic   _ -> FI.JClass "java.lang.Boolean" 
infer i j (FI.Tuple es) = FI.Product . map (infer i j) $ es
infer i j (FI.Proj index e) = ts !! (index - 1) where FI.Product ts = infer i j e
--infer i j FI.JNew ?=
--infer i j FI.JMethod ?=
--infer i j FI.JField ?=
--infer i j FI.PolyList ?=
--infer i j FI.JProxyCall ?=
infer i j (FI.Seq es) = infer i j (last es)
infer i j (FI.Merge e1 e2) = FI.And (infer i j e1) (infer i j e2)
infer i j (FI.RecordIntro (l, e)) = FI.Record (l, infer i j e)
infer i j (FI.RecordElim e l1) = t1 where Just (t1, _) = getter i j (infer i j e) l1
infer i j (FI.RecordUpdate e _) = infer i j e
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

--Old: transExpr i j (FI.BLam n f) = BLam n (\a -> fsubstTE i (TVar n a) . transExpr (i + 1) j $ f i)
transExpr i j (FI.BLam n f) = BLam n (\a -> transExpr (i + 1) j $ f a)

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
transExpr i j (FI.TApp f x) = TApp (transExpr i j f) (transType i x)
transExpr i j (FI.If e1 e2 e3) = If e1' e2' e3'
  where [e1', e2', e3'] = map (transExpr i j) [e1, e2, e3]
transExpr i j (FI.PrimOp e1 op e2) = PrimOp (transExpr i j e1) op (transExpr i j e2)
transExpr i j (FI.Tuple es) = Tuple . map (transExpr i j) $ es
transExpr i j (FI.Proj index e) = Proj index $ transExpr i j e
--transExpr i j FI.JNew ?=
--transExpr i j FI.JMethod ?=
--transExpr i j FI.JField ?=
--transExpr i j FI.PolyList ?=
--transExpr i j FI.JProxyCall ?=
transExpr i j (FI.Seq es) = Seq . map (transExpr i j) $ es
transExpr i j (FI.Merge e1 e2) = Tuple . map (transExpr i j) $ [e1, e2]
transExpr i j (FI.RecordIntro (l, e)) = transExpr i j e
transExpr i j (FI.RecordElim e l1) = App c (transExpr i j e)
  where Just (_, c) = getter i j (infer i j e) l1
transExpr i j (FI.RecordUpdate e (l1, e1)) = App c (transExpr i j e)
  where Just (_, c) = putter i j (infer i j e) l1 (transExpr i j e1)
--transExpr i j FI.Constr ?=
--transExpr i j FI.Case ?=
transExpr _ _ _ = trace "Wrong2" (Var "" (-1))

transType :: Index -> FI.Type Index -> Type Index
transType i (FI.TVar n a) = TVar n a
transType i (FI.JClass c) = JClass c 
transType i (FI.Fun a1 a2) = Fun (transType i a1) (transType i a2)

--Old: transType i (FI.Forall n f) = Forall n (\a -> transType (i + 1) . FI.fsubstTT i (FI.TVar n a) $ f i)
transType i (FI.Forall n f) = Forall n (\a -> transType (i + 1) $ f a)

transType i (FI.Product ts) = Product . map (transType i) $ ts 
transType i (FI.Unit) = Unit 
transType i (FI.And a1 a2) = Product . map (transType i) $ [a1, a2]
transType i (FI.Record (_, t)) = transType i t 
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
coerce i this@(FI.Forall _ f) (FI.Forall _ g) = do
  c <- coerce (i + 1) (f i) (g i)
  return $ lam (transType i this) (\f' -> bLam $ (App c . TApp (var f')) . TVar "")
coerce i this@(FI.Product ss) (FI.Product ts)
  | length ss /= length ts = Nothing
  | otherwise = do
      cs <- zipWithM (coerce i) ss ts
      let f x = Tuple $ zipWith (\c idx -> App c $ Proj idx x) cs [1..length ss]
      return $ lam (transType i this) (f . var)
coerce i this@(FI.Unit) (FI.Unit) = return $ lam (transType i this) var
coerce i t1 (FI.And t2 t3) = do
  c1 <- coerce i t1 t2
  c2 <- coerce i t1 t3
  return $ lam (transType i t1) (\x -> Tuple [App c1 (var x), App c2 (var x)])
coerce i this@(FI.And t1 t2) t3 =
  case coerce i t1 t3 of
    Just c  -> return $ lam (transType i this) (App c . Proj 1 . var)
    Nothing -> case coerce i t2 t3 of
                 Just c  -> return $ lam (transType i this) (App c . Proj 2 . var)
                 Nothing -> Nothing
coerce i (FI.Record (l1, t1)) (FI.Record (l2, t2))
  | l1 == l2  = coerce i t1 t2
  | otherwise = Nothing
--coerce i FI.Datatype FI.Datatype =
coerce _ _ _ = Nothing

getter :: Index -> Index -> FI.Type Index -> S.Label -> Maybe (FI.Type Index, Expr Index Index)
getter i j this@(FI.Record (l, t)) l1
  | l1 == l = return $ (t, lam (transType i this) var)
  | otherwise = Nothing
getter i j this@(FI.And t1 t2) l =
  case getter i j t2 l of
    Just (t, c) -> return $ (t, lam (transType i this) (App c . Proj 2 . var))
    Nothing     -> case getter i j t1 l of
                     Just (t, c) -> return $ (t, lam (transType i this) (App c . Proj 1 . var))
                     Nothing     -> Nothing
getter _ _ _ _ = Nothing

putter :: Index -> Index -> FI.Type Index -> S.Label -> Expr Index Index -> Maybe (FI.Type Index, Expr Index Index)
putter i j this@(FI.Record (l, t)) l1 e
  | l1 == l = return $ (t, lam (transType i this) (Prelude.const e))
  | otherwise = Nothing
putter i j this@(FI.And t1 t2) l e =
  case putter i j t2 l e of
    Just (t, c) -> return $ (t, lam (transType i this) (\x -> Tuple [Proj 1 . var $ x, App c . Proj 2 . var $ x]))
    Nothing     -> case putter i j t1 l e of
                     Just (t, c) -> return $ (t, lam (transType i this) (\x -> Tuple [App c . Proj 1 . var $ x, Proj 2 . var $ x]))
                     Nothing     -> Nothing
putter _ _ _ _ _ = Nothing

substTT :: (S.ReaderId -> Index -> FI.Type Index) -> [FI.Type Index] -> FI.Type Index
substTT g ts@((FI.TVar n a):_) = if const then g n a else FI.TVar n a
  where const = all (== a) . map (\x -> let FI.TVar _ y = x in y) $ ts
substTT g ((FI.JClass c):_) = FI.JClass c
substTT g ts@((FI.Fun _ _):_) = FI.Fun (substTT g ts1) (substTT g ts2)
  where (ts1, ts2) = unzip . map (\x -> let FI.Fun t1 t2 = x in (t1, t2)) $ ts
substTT g ts@((FI.Forall n _):_) = FI.Forall n (\z -> substTT g $ ts' z)
  where ts' z = concat . map (\x -> let FI.Forall _ f = x in [f z, f (z + 1)]) $ ts
substTT g ts@((FI.Product _):_) = FI.Product ts'
  where 
    ts' = map (substTT g) . transpose . map (\x -> let FI.Product hs = x in hs) $ ts
    transpose :: [[a]] -> [[a]]
    transpose [] = []
    transpose xs = (map head xs):(transpose . map tail $ xs)
substTT g ((FI.Unit):_) = FI.Unit
--substTT g ((FI.ListOf _):_) =
substTT g ts@((FI.And _ _):_) = FI.And (substTT g ts1) (substTT g ts2)
  where (ts1, ts2) = unzip . map (\x -> let FI.And t1 t2 = x in (t1, t2)) $ ts
substTT g ts@((FI.Record (l, _)):_) = FI.Record (l, t')
  where t' = substTT g . map (\x -> let FI.Record (_, t) = x in t) $ ts
--substTT g ((FI.Datatype _ _):_) =

test :: Int -> Doc
test id = prettyExpr . simplify $ l !! id
  where l = [setZero, fact, evenOdd, apply, intersection, product0]

test2 :: Int -> Doc
test2 id = prettyExpr . simplify $ l !! id
  where l = [bob, bob1, bob2, listAlg]

-- Utils.
jInt  = FI.JClass "java.lang.Integer"
jBool = FI.JClass "java.lang.Boolean"
lit x = FI.Lit (S.Int x)
str s = FI.Lit (S.String s)
true  = FI.Lit (S.Bool True)
false = FI.Lit (S.Bool False)
equal = S.Compare J.Equal
add = S.Arith J.Add
sub = S.Arith J.Sub
mul = S.Arith J.Mult
t2str = show . FI.prettyType
e2str = show . FI.prettyExpr
t2str' = show . prettyType
e2str' = show . prettyExpr

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
apply = FI.Let "apply" app_body
  (\app -> FI.App (FI.App (FI.App (FI.TApp (FI.TApp (FI.Var "apply" app) jInt) jBool) (lit 2)) true) lambda_f)
  where
    app_body :: FI.Expr Index (Index, FI.Type Index)
    app_body = FI.BLam "P" (\p -> FI.BLam "Q" (\q -> FI.Lam "x" (FI.TVar "P" p) (\x -> FI.Lam "y" (FI.TVar "Q" q) (\y -> FI.Lam "f" (FI.Fun (FI.TVar "P" p) (FI.Fun (FI.TVar "Q" q) jInt)) (\f -> FI.App (FI.App (FI.Var "f" f) (FI.Var "x" x)) (FI.Var "y" y))))))
    lambda_f :: FI.Expr Index (Index, FI.Type Index)
    lambda_f = FI.Lam "m" jInt (\m -> FI.Lam "n" jBool (\n -> FI.If (FI.PrimOp (FI.Var "n" n) equal true) (FI.PrimOp (FI.Var "m" m) add (lit 1)) (FI.Var "m" m)))

-- let succ x = x + 1 in succ (setZero ,, 1)
intersection :: FI.Expr Index (Index, FI.Type Index)
intersection = FI.Let "succ" (FI.Lam "x" jInt (\x -> FI.PrimOp (FI.Var "x" x) add (lit 1))) (\succ -> FI.App (FI.Var "succ" succ) (FI.Merge (FI.Lam "setZero" jInt (\x -> lit 0)) (lit 1)))

-- let f x = (x, 2x) in (f 3)._2
product0 :: FI.Expr Index (Index, FI.Type Index)
product0 = FI.Let "f" (FI.Lam "x" jInt (\x -> FI.Tuple [FI.Var "x" x, FI.PrimOp (FI.Var "x" x) mul (lit 2)])) (\f -> FI.Proj 2 (FI.App (FI.Var "f" f) (lit 3)))

-- { name = "Bob", age = 30, language = "Haskell"}
bob :: FI.Expr Index (Index, FI.Type Index)
bob = FI.Merge (FI.Merge (FI.RecordIntro ("name", str "Bob")) (FI.RecordIntro ("age", lit 30))) (FI.RecordIntro ("language", str "Haskell"))

-- bob.language
bob1 :: FI.Expr Index (Index, FI.Type Index)
bob1 = FI.RecordElim (FI.Merge (FI.Merge (FI.RecordIntro ("name", str "Bob")) (FI.RecordIntro ("age", lit 30))) (FI.RecordIntro ("language", str "Haskell"))) "language"

-- let x = bob with {age = 35} in (x.name, x.age, x.language)._2
bob2 :: FI.Expr Index (Index, FI.Type Index)
bob2 = FI.Let "x" (FI.RecordUpdate bob ("age", lit 35)) (\x -> FI.Proj 2 (FI.Tuple [FI.RecordElim (FI.Var "x" x) "name", FI.RecordElim (FI.Var "x" x) "age", FI.RecordElim (FI.Var "x" x) "language"]))

-- type ListAlg A L = { nil : L, cons : A -> L -> L };
-- type MyList A = { accept : forall K. ListAlg A K -> K };
-- let nil A (x : Int) : MyList A = { accept = /\M. \(f : ListAlg A M). f.nil };
-- let cons A (x : A) (xs : MyList A) : MyList A = { accept = /\N. \(f : ListAlg A N). f.cons x (xs.accept N f) };
-- cons Int 5 (cons Int 3 (nil Int 0))
listAlg :: FI.Expr Index (Index, FI.Type Index)
listAlg = FI.Let "nil" nil (\n -> FI.Let "cons" cons (\c -> FI.App (FI.App (FI.TApp (FI.Var "cons" c) jInt) (lit 5)) (FI.App (FI.App (FI.TApp (FI.Var "cons" c) jInt) (lit 3)) (FI.App (FI.TApp (FI.Var "nil" n) jInt) (lit 0))))) 
  where
    alg :: FI.Type Index -> FI.Type Index -> FI.Type Index
    alg a l = FI.And (FI.Record ("nil", l)) (FI.Record ("cons", FI.Fun a (FI.Fun l l)))
    myList :: FI.Type Index -> FI.Type Index
    myList a = FI.Record ("accept", FI.Forall "K" (\k -> FI.Fun (alg a (FI.TVar "K" k)) (FI.TVar "K" k)))
    nil :: FI.Expr Index (Index, FI.Type Index)
    nil = FI.BLam "A" (\a -> FI.Lam "x" jInt (\x -> FI.RecordIntro ("accept", FI.BLam "M" (\m -> FI.Lam "f" (alg (FI.TVar "A" a) (FI.TVar "M" m)) (\f -> FI.RecordElim (FI.Var "f" f) "nil")))))
    cons :: FI.Expr Index (Index, FI.Type Index)
    cons  = FI.BLam "A" (\a -> FI.Lam "x" (FI.TVar "A" a) (\x -> FI.Lam "xs" (myList (FI.TVar "A" a)) (\xs -> FI.RecordIntro ("accept", FI.BLam "N" (\n -> FI.Lam "f" (alg (FI.TVar "A" a) (FI.TVar "N" n)) (\f -> FI.App (FI.App (FI.RecordElim (FI.Var "f" f) "cons") (FI.Var "x" x)) (FI.App (FI.TApp (FI.RecordElim (FI.Var "xs" xs) "accept") (FI.TVar "N" n)) (FI.Var "f" f))))))))
