module Playground where

import           BackEnd (module2java)
import qualified ClosureF as C
import           Core
import qualified Src as S
import           Unsafe.Coerce (unsafeCoerce)

import qualified Language.Java.Syntax as J (Op(..))

instance Show (Expr t e) where
  show = show . prettyExpr . unsafeCoerce

instance Show (Type t) where
  show = show . prettyType . unsafeCoerce

instance Show (Module t e) where
  show = show . prettyMod . unsafeCoerce

instance Show (C.Module t e) where
  show = show . C.prettyMod . unsafeCoerce

{-
module;

def f1 (n : Int) = n + 1;

def f2 (n : Int) = f1 n + 1;

-}

javaIntS = (S.JType (S.JClass "java.lang.Integer"))

m1 :: Module t e
m1 = Mod "M1"
       (Def "f1" (javaIntS `S.Fun` javaIntS) (lam javaInt (\n -> var n `add` one))
          (\f1 ->
             Def
               "f2"
               (javaIntS `S.Fun` javaIntS)
               (lam javaInt (\n -> ((var f1 `App` (var n)) `add` one)))
               (\f2 -> Def "f3" javaIntS one (\f3 -> Null))))

printModule m = module2java m >>= putStrLn


m2 = Let "a" one (\a -> Let "b" zero (\b -> var a `add` var b))

tailFact :: Expr t e
tailFact
  = fix (\tail_fact acc ->
      lam javaInt (\n ->
        If (var n `eq` zero)
           (var acc)
           (var tail_fact `App` (var acc `mult` var n) `App` (var n `sub` one))))
    javaInt (javaInt `Fun` javaInt)

testTail :: Expr t e
testTail = App (fix (\f n -> If (var n `eq` zero)
                           one
                           (var f `App` (var n `sub` one)))
               javaInt
               (javaInt `Fun` javaInt)) one

fact :: Expr t e
fact = fix (\f n -> If (var n `eq` zero)
                       one
                       (var n `mult` (var f `App` (var n `sub` one))))
           javaInt
           (javaInt `Fun` javaInt)


test1 :: Expr t e
test1 =
  lam javaInt (\f ->
                lam javaInt (\g -> App (var f)
                                   (lam javaInt (\x -> Let "" (App (var g) (var x)) (\t -> var t)))))

tailFactLike :: Expr t e
tailFactLike
  = fix (\tail_fact acc ->
      lam javaInt (\n ->
                    If (var n `eq` zero)
                    (var acc)
                    (var tail_fact `App` (var acc `mult` one) `App` one)))
    javaInt (javaInt `Fun` javaInt)


plus2 :: Expr t e
plus2 = (App (lam (Fun javaInt (Fun javaInt javaInt)) (\e -> (App (App (var e) one) zero)))
             (lam javaInt (\e -> (lam javaInt (\f -> (var e) `mult` (var f))))))

evenOdd :: Expr t e
evenOdd
  = LetRec
      ["even", "odd"]
      [(Fun javaInt javaBool), (Fun javaInt javaBool)]
      (\ids ->
         [ lam javaInt (\n -> If (var n `eq` zero) true  (App (var (ids !! 1)) (var n `sub` one)))
         , lam javaInt (\n -> If (var n `eq` zero) false (App (var (ids !! 0)) (var n `sub` one)))])
      (\ids ->
         App (var (ids !! 1)) magicNumber)


javaBool     = JClass "java.lang.Boolean"
zero         = Lit (S.Int 0)
one          = Lit (S.Int 1)
five         = Lit (S.Int 5)
ten          = Lit (S.Int 10)
negOne       = Lit (S.Int (-1))
magicNumber  = Lit (S.Int 42)
true         = Lit (S.Bool True)
false        = Lit (S.Bool False)
x `eq` y     = PrimOp x (S.Compare J.Equal) y
x `neq` y    = PrimOp x (S.Compare J.NotEq) y
x `lt` y     = PrimOp x (S.Compare J.LThan) y
x `bAnd` y    = PrimOp x (S.Logic J.And) y
x `add` y    = PrimOp x (S.Arith J.Add) y
x `sub` y    = PrimOp x (S.Arith J.Sub) y
x `mult` y   = PrimOp x (S.Arith J.Mult) y

-- sf2c :: String -> IO (Expr t e)
-- sf2c fname = do
--   path <- {-"/Users/weixin/Project/systemfcompiler/compiler/"-} getCurrentDirectory
--   string <- readFile (path ++ "/" ++ fname)
--   let readSrc = Parser.reader string
--   result <- readSrc `seq` (typeCheck readSrc)
--   case result of
--    Left typeError -> error $ show typeError
--    Right (typ, tcheckedSrc) -> do
--      print tcheckedSrc
--      return (simplify . desugar $ tcheckedSrc)
     -- case n of
     --  1 -> return (peval . simplify . desugar $ tcheckedSrc)
     --  2 -> return (simplify . desugar $ tcheckedSrc)
      -- 3 -> return (desugar $ tcheckedSrc)
      -- _ -> return (peval . desugar $ tcheckedSrc)

mconst =
  (bLam (\a ->
    lam (tVar a) (\x ->
       lam (tVar a) (\y ->
          var x
       )
    )
  ))

notail2 =
  bLam (\a ->
    lam (Fun (tVar a) (Fun (tVar a) (tVar a))) (\f ->
      lam (tVar a) (\x ->
        lam (tVar a) (\y ->
          App (App (var f) (var x)) (App (App (var f) (var y)) (var y)) ))))

program2 = App (App (App (TApp notail2 (JClass "java.lang.Integer")) (TApp mconst (JClass "java.lang.Integer"))) (Lit (S.Int 5))) (Lit (S.Int 6))

notail4 =
  bLam (\a ->
    lam ( Fun (Fun (tVar a) (tVar a)) (Fun (Fun (tVar a) (tVar a)) (tVar a))) (\g ->
      lam (Fun (tVar a) (Fun (tVar a) (tVar a))) (\f ->
        lam (tVar a) (\x ->
          lam (tVar a) (\y ->
            App (App (var g) (App (var f) (var x))) (App (var f) (var y)))))))

summa =
    lam (Fun (JClass "java.lang.Integer") (JClass "java.lang.Integer")) (\x ->
       lam (Fun (JClass "java.lang.Integer") (JClass "java.lang.Integer")) (\y ->
          PrimOp (App (var x) (Lit (S.Int 0))) (S.Arith J.Add) (App (var y) (Lit (S.Int 0)))
       )
    )

program4 = App (App (App (App (TApp notail4 (JClass "java.lang.Integer")) summa) (TApp mconst (JClass "java.lang.Integer"))) (Lit (S.Int 5))) (Lit (S.Int 6))
