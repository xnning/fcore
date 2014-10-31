{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wall #-}

module Core
  ( Type(..)
  , Expr(..)
  , TypeContext
  , ValueContext
  , Index
  , alphaEq
  , mapTVar
  , mapVar
  , fsubstTT
  , fsubstTE
  , fsubstEE
  , joinType
  , prettyType
  , prettyExpr
  , javaInt
  ) where

import qualified Src

import JavaUtils
import PrettyUtils

import Text.PrettyPrint.Leijen
import qualified Language.Java.Pretty      (prettyPrint)

import           Data.List (intersperse)
import qualified Data.Map as Map
import qualified Data.Set as Set

data Type t
  = TVar t                 -- a
  | JClass ClassName       -- C
  | Fun (Type t) (Type t)  -- t1 -> t2
  | Forall (t -> Type t)   -- forall a. t
  | Product [Type t]       -- (t1, ..., tn)
  | Unit

  | And (Type t) (Type t)  -- t1 & t2
  | Record (Src.Label, Type t)
  | Thunk (Type t)
    -- Warning: If you ever add a case to this, you *must* also define the
    -- binary relations on your new case. Namely, add cases for your data
    -- constructor in `alphaEq' (below) and `coerce' (in Simplify.hs). Consult
    -- George if you're not sure.

data Expr t e
  = Var e
  | Lit Src.Lit

  -- Binders we have: λ, fix, letrec, and Λ
  | Lam (Type t) (e -> Expr t e)
  | Fix (e -> e -> Expr t e)
        (Type t)  -- t1
        (Type t)  -- t
      -- fix x (x1 : t1) : t. e     Syntax in the tal-toplas paper
      -- fix (x : t1 -> t). \x1. e  Alternative syntax, which is arguably clear
  | Let (Expr t e) (e -> Expr t e)
  | LetRec [Type t]             -- Signatures
           ([e] -> [Expr t e])  -- Bindings
           ([e] -> Expr t e)    -- Body
  | BLam (t -> Expr t e)

  | App  (Expr t e) (Expr t e)
  | TApp (Expr t e) (Type t)

  | If (Expr t e) (Expr t e) (Expr t e)
  | PrimOp (Expr t e) Src.Operator (Expr t e)
      -- SystemF extension from:
      -- https://www.cs.princeton.edu/~dpw/papers/tal-toplas.pdf
      -- (no int restriction)

  | Tuple [Expr t e]     -- Tuple introduction
  | Proj Int (Expr t e)  -- Tuple elimination

  -- Java
  | JNew ClassName [Expr t e]
  | JMethod (Src.JCallee (Expr t e)) MethodName [Expr t e] ClassName
  | JField  (Src.JCallee (Expr t e)) FieldName ClassName

  | Seq [Expr t e]

  | Merge (Expr t e) (Expr t e)  -- e1 ,, e2
  | RecordLit    (Src.Label, Expr t e)
  | RecordElim   (Expr t e) Src.Label
  | RecordUpdate (Expr t e) (Src.Label, Expr t e)
  | Lazy (Expr t e)

-- newtype Typ = HideTyp { revealTyp :: forall t. Type t } -- type of closed types

-- newtype Exp = HideExp { revealExp :: forall t e. Expr t e }

type TypeContext t    = Set.Set t
type ValueContext t e = Map.Map e (Type t)

type Index = Int

alphaEq :: Int -> Type Index -> Type Index -> Bool
alphaEq _ (TVar a)     (TVar b)     = a == b
alphaEq _ (JClass c)   (JClass d)   = c == d
alphaEq i (Fun s1 s2)  (Fun t1 t2)  = alphaEq i s1 t1 && alphaEq i s2 t2
alphaEq i (Forall f)   (Forall g)   = alphaEq (succ i) (f i) (g i)
alphaEq i (Product ss) (Product ts) = length ss == length ts && uncurry (alphaEq i) `all` zip ss ts
alphaEq _  Unit     Unit            = True
alphaEq i (And s1 s2)  (And t1 t2)  = alphaEq i s1 t1 && alphaEq i s2 t2
alphaEq i (Thunk t1)   (Thunk t2)   = alphaEq i t1 t2
alphaEq _ _            _            = False

mapTVar :: (t -> Type t) -> Type t -> Type t
mapTVar g (TVar a)       = g a
mapTVar _ (JClass c)     = JClass c
mapTVar g (Fun t1 t2)    = Fun (mapTVar g t1) (mapTVar g t2)
mapTVar g (Forall f)     = Forall (mapTVar g . f)
mapTVar g (Product ts)   = Product (map (mapTVar g) ts)
mapTVar _  Unit          = Unit
mapTVar g (And t1 t2)    = And (mapTVar g t1) (mapTVar g t2)
mapTVar g (Record (l,t)) = Record (l, mapTVar g t)
mapTVar g (Thunk t)      = Thunk (mapTVar g t)

mapVar :: (e -> Expr t e) -> (Type t -> Type t) -> Expr t e -> Expr t e
mapVar g _ (Var a)                   = g a
mapVar _ _ (Lit n)                   = Lit n
mapVar g h (Lam t f)                 = Lam (h t) (mapVar g h . f)
mapVar g h (BLam f)                  = BLam (mapVar g h . f)
mapVar g h (Fix f t1 t)              = Fix (\x x1 -> mapVar g h (f x x1)) (h t1) (h t)
mapVar g h (Let b e)                 = Let (mapVar g h b) (mapVar g h . e)
mapVar g h (LetRec ts bs e)          = LetRec (map h ts) (map (mapVar g h) . bs) (mapVar g h . e)
mapVar g h (App f e)                 = App (mapVar g h f) (mapVar g h e)
mapVar g h (TApp f t)                = TApp (mapVar g h f) (h t)
mapVar g h (If p b1 b2)              = If (mapVar g h p) (mapVar g h b1) (mapVar g h b2)
mapVar g h (PrimOp e1 op e2)         = PrimOp (mapVar g h e1) op (mapVar g h e2)
mapVar g h (Tuple es)                = Tuple (map (mapVar g h) es)
mapVar g h (Proj i e)                = Proj i (mapVar g h e)
mapVar g h (JNew c args)             = JNew c (map (mapVar g h) args)
mapVar g h (JMethod callee m args c) = JMethod (fmap (mapVar g h) callee) m (map (mapVar g h) args) c
mapVar g h (JField  callee f c)      = JField (fmap (mapVar g h) callee) f c
mapVar g h (Seq es)                  = Seq (map (mapVar g h) es)
mapVar g h (Merge e1 e2)             = Merge (mapVar g h e1) (mapVar g h e2)
mapVar g h (RecordLit (l, e))        = RecordLit (l, mapVar g h e)
mapVar g h (RecordElim e l)          = RecordElim (mapVar g h e) l
mapVar g h (RecordUpdate e (l1,e1))  = RecordUpdate (mapVar g h e) (l1, mapVar g h e1)
mapVar g h (Lazy e)                  = Lazy (mapVar g h e)

fsubstTT :: Eq a => a -> Type a -> Type a -> Type a
fsubstTT x r = mapTVar (\a -> if a == x then r else TVar a)

fsubstTE :: Eq t => t -> Type t -> Expr t e -> Expr t e
fsubstTE x r = mapVar Var (fsubstTT x r)

fsubstEE :: Eq a => a -> Expr t a -> Expr t a -> Expr t a
fsubstEE x r = mapVar (\a -> if a == x then r else Var a) id


joinType :: Type (Type t) -> Type t
joinType (TVar a)         = a
joinType (JClass c)       = JClass c
joinType (Fun t1 t2)      = Fun (joinType t1) (joinType t2)
joinType (Forall g)       = Forall (joinType . g . TVar)
joinType (Product ts)     = Product (map joinType ts)
joinType  Unit        = Unit
joinType (And t1 t2)      = And (joinType t1) (joinType t2)
joinType (Record (l,t)) = Record (l, joinType t)
joinType (Thunk t)        = Thunk (joinType t)


-- instance Show (Type Index) where
--   show = show . pretty

-- instance Pretty (Type Index) where
--   pretty = prettyType

prettyType :: Type Index -> Doc
prettyType = prettyType' basePrec 0

prettyType' :: Prec -> Index -> Type Index -> Doc

prettyType' _ _ (TVar a)     = prettyTVar a

prettyType' p i (Fun t1 t2)  =
  parensIf p 2
    (prettyType' (2,PrecPlus) i t1 <+> arrow <+> prettyType' (2,PrecMinus) i t2)

prettyType' p i (Forall f)   =
  parensIf p 1
    (forall <+> prettyTVar i <> dot <+>
     prettyType' (1,PrecMinus) (succ i) (f i))

prettyType' _ i (Product ts) = parens $ hcat (intersperse comma (map (prettyType' basePrec i) ts))

prettyType' _ _  Unit = text "Unit"

prettyType' _ _ (JClass "java.lang.Integer")   = text "Int"
prettyType' _ _ (JClass "java.lang.String")    = text "String"
prettyType' _ _ (JClass "java.lang.Boolean")   = text "Bool"
prettyType' _ _ (JClass "java.lang.Character") = text "Char"
prettyType' _ _ (JClass c)                     = text c

prettyType' p i (And t1 t2) =
  parensIf p 2
    (prettyType' (2,PrecMinus) i t1 <+>
     ampersand  <+>
     prettyType' (2,PrecPlus) i t2)

prettyType' _ i (Record (l,t)) = lbrace <> text l <> colon <> prettyType' basePrec i t <> rbrace

prettyType' p i (Thunk t) = squote <>
                             case t of
                               Fun _ _  -> parens (prettyType' basePrec i t)
                               Forall _ -> parens (prettyType' basePrec i t)
                               And _ _  -> parens (prettyType' basePrec i t)
                               _        -> prettyType' p i t

-- instance Show (Expr Index Index) where
--   show = show . pretty

-- instance Pretty (Expr Index Index) where
--   pretty = prettyExpr

prettyExpr :: Expr Index Index -> Doc
prettyExpr = prettyExpr' basePrec (0, 0)

prettyExpr' :: Prec -> (Index, Index) -> Expr Index Index -> Doc

prettyExpr' _ _ (Var x) = prettyVar x

prettyExpr' p (i,j) (Lam t f) =
  parensIf p 2
    (hang 3 (lambda <+> parens (prettyVar j <+> colon <+> prettyType' basePrec i t) <> dot <+>
             prettyExpr' (2,PrecMinus) (i, succ j) (f j)))

prettyExpr' p (i,j) (App e1 e2) =
  parensIf p 4
    (prettyExpr' (4,PrecMinus) (i,j) e1 <+> prettyExpr' (4,PrecPlus) (i,j) e2)

prettyExpr' p (i,j) (BLam f) =
  parensIf p 2
    (biglambda <+> prettyTVar i <> dot <+>
     prettyExpr' (2,PrecMinus) (succ i, j) (f i))

prettyExpr' p (i,j) (TApp e t) =
  parensIf p 4
    (prettyExpr' (4,PrecMinus) (i,j) e <+> prettyType' (4,PrecPlus) i t)

prettyExpr' _ _ (Lit (Src.Int n))    = integer n
prettyExpr' _ _ (Lit (Src.String s)) = dquotes (string s)
prettyExpr' _ _ (Lit (Src.Bool b))   = bool b
prettyExpr' _ _ (Lit (Src.Char c))   = char c
prettyExpr' _ _ (Lit Src.UnitLit)    = unit

prettyExpr' p (i,j) (If e1 e2 e3)
  = parensIf p prec
      (hang 3 (text "if"   <+> prettyExpr' (prec,PrecMinus) (i,j) e1 <+>
               text "then" <+> prettyExpr' (prec,PrecMinus) (i,j) e2 <+>
               text "else" <+> prettyExpr' (prec,PrecMinus) (i,j) e3))
  where prec = 3

prettyExpr' p (i,j) (PrimOp e1 op e2)
  = parens (prettyExpr' p (i,j) e1 <+> pretty_op <+> prettyExpr' p (i,j) e2)
  where
    pretty_op = text (Language.Java.Pretty.prettyPrint java_op)
    java_op   = case op of
                  Src.Arith   op' -> op'
                  Src.Compare op' -> op'
                  Src.Logic   op' -> op'

prettyExpr' _ (i,j) (Tuple es) = parens $ hcat (intersperse comma (map (prettyExpr' basePrec (i,j)) es))

prettyExpr' p i (Proj n e) =
  parensIf p 5
    (prettyExpr' (5,PrecMinus) i e <> dot <> char '_' <> int n)

prettyExpr' _ (i,j) (JNew c args) =
  parens (text "new" <+> text c <> tupled (map (prettyExpr' basePrec (i,j)) args))

prettyExpr' _ i (JMethod name m args _) = methodStr name <> dot <> text m <> tupled (map (prettyExpr' basePrec i) args)
  where
    methodStr (Src.Static x) = text x
    methodStr (Src.NonStatic x) = prettyExpr' (6,PrecMinus) i x

prettyExpr' _ i (JField name f _) = fieldStr name <> dot <> text f
  where
    fieldStr (Src.Static x) = text x
    fieldStr (Src.NonStatic x) = prettyExpr' (6,PrecMinus) i x

prettyExpr' p (i,j) (Seq es) = semiBraces (map (prettyExpr' p (i,j)) es)

prettyExpr' p (i,j) (Fix f t1 t) =
  parens
    (text "fix" <+> prettyVar j <+>
     parens (prettyVar (succ j) <+> colon <+> prettyType' p i t1) <+>
     colon <+>
     prettyType' p i t <> dot <$$>
     indent 2 (prettyExpr' p (i, j + 2) (f j (j + 1))))

prettyExpr' _ (i,j) (Let x f) =
  text "let" <$$>
  indent 2 (prettyVar j <> text " = " <>
    prettyExpr' basePrec (i, succ j) x) <$$>
  text "in" <$$>
  indent 2 (prettyExpr' basePrec (i, succ j) (f j))

prettyExpr' p (i,j) (LetRec sigs binds body)
  = text "let" <+> text "rec" <$$>
    vcat (intersperse (text "and") (map (indent 2) pretty_binds)) <$$>
    text "in" <$$>
    pretty_body
  where
    n   = length sigs
    ids = [i..(i+n-1)]
    pretty_ids   = map prettyVar ids
    pretty_sigs  = map (prettyType' p i) sigs
    pretty_defs  = map (prettyExpr' p (i, j + n)) (binds ids)
    pretty_binds = zipWith3 (\pretty_id pretty_sig pretty_def ->
                  pretty_id <+> colon <+> pretty_sig <$$> indent 2 (equals <+> pretty_def))
                  pretty_ids pretty_sigs pretty_defs
    pretty_body  = prettyExpr' p (i, j + n) (body ids)

prettyExpr' p (i,j) (Merge e1 e2) =
  parens $ prettyExpr' p (i,j) e1 <+> dcomma <+> prettyExpr' p (i,j) e2

prettyExpr' _ (i,j) (RecordLit (l, e))       = lbrace <> text l <> equals <> prettyExpr' basePrec (i,j) e <> rbrace
prettyExpr' p (i,j) (RecordElim e l)         = prettyExpr' p (i,j) e <> dot <> text l
prettyExpr' p (i,j) (RecordUpdate e (l, e1)) = prettyExpr' p (i,j) e <+> text "with" <+> prettyExpr' p (i,j) (RecordLit (l, e1))
prettyExpr' _ (i,j) (Lazy e)                 = char '\'' <> parens (prettyExpr' basePrec (i,j) e)


javaInt :: Type t
javaInt = JClass "java.lang.Integer"
