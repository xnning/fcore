{-# LANGUAGE RecordWildCards #-}
{-# OPTIONS_GHC -Wall #-}

module TypeCheck
  ( typeCheck

  -- For REPL
  , typeCheckWithEnv
  , mkInitTcEnvWithEnv
  , TypeError
  ) where

import Src

import IOEnv
import JavaUtils
import PrettyUtils
import JvmTypeQuery
import Panic
import StringPrefixes

import Text.PrettyPrint.Leijen

import System.IO
import System.Process

import Control.Monad.Error

import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Map  as Map
import qualified Data.Set  as Set
import Data.List (intersperse)

import Prelude hiding (pred)

type Connection = (Handle, Handle)

typeCheck :: Expr Name -> IO (Either TypeError (Expr (Name,Type), Type))
-- type_server is (Handle, Handle)
typeCheck e = withTypeServer (\type_server ->
  (evalIOEnv (mkInitTcEnv type_server) . runErrorT . infer) e)

-- Temporary hack for REPL
typeCheckWithEnv :: ValueContext -> Expr Name -> IO (Either TypeError (Expr (Name,Type), Type))
-- type_server is (Handle, Handle)
typeCheckWithEnv value_ctxt e = withTypeServer (\type_server ->
  (evalIOEnv (mkInitTcEnvWithEnv value_ctxt type_server) . runErrorT . infer) e)

withTypeServer :: (Connection -> IO a) -> IO a
withTypeServer do_this =
  do cp <- getClassPath
     let p = (proc "java" ["-cp", cp, (namespace ++ "TypeServer")])
               { std_in = CreatePipe, std_out = CreatePipe }
     (Just inp, Just out, _, proch) <- createProcess p
     hSetBuffering inp NoBuffering
     hSetBuffering out NoBuffering
     res <- do_this (inp, out)
     terminateProcess proch
     return res

data TcEnv
  = TcEnv
  { tceTypeContext     :: Map.Map Name (Kind, Type)
  , tceValueContext    :: Map.Map Name Type
  , tceTypeserver   :: Connection
  , tceMemoizedJavaClasses :: Set.Set ClassName -- Memoized Java class names
  }

mkInitTcEnv :: Connection -> TcEnv
mkInitTcEnv type_server
  = TcEnv
  { tceTypeContext     = Map.empty
  , tceValueContext    = Map.empty
  , tceTypeserver   = type_server
  , tceMemoizedJavaClasses = Set.empty
  }

-- Temporary hack for REPL
mkInitTcEnvWithEnv :: ValueContext -> Connection -> TcEnv
mkInitTcEnvWithEnv value_ctxt type_server
  = TcEnv
  { tceTypeContext     = Map.empty
  , tceValueContext    = value_ctxt
  , tceTypeserver   = type_server
  , tceMemoizedJavaClasses = Set.empty
  }

data TypeError
  = General Doc
  | ConflictingDefinitions Name
  | ExpectJClass
  | IndexTooLarge
  | Mismatch { expectedTy :: Type, actualTy :: Type }
  | MissingRHSAnnot
  | NotInScopeTVar Name
  | NotInScopeVar Name
  | NotInScopeConstr Name
  | ProjectionOfNonProduct

  -- Java-specific type errors
  | NoSuchClass       ClassName
  | NoSuchConstructor ClassName [ClassName]
  | NoSuchMethod      (JCallee ClassName) MethodName [ClassName]
  | NoSuchField       (JCallee ClassName) FieldName
  deriving (Show)

instance Pretty TypeError where
  pretty (General doc)      = text "error:" <+> doc
  pretty (NotInScopeTVar a) = text "error:" <+> text "type" <+> bquotes (text a) <+> text "is not in scope"
  pretty (NotInScopeConstr a) = text "error:" <+> text "data constructor" <+> bquotes (text a) <+> text "is not in scope"
  pretty e                  = text "error:" <+> text (show e)

instance Error TypeError where
  -- strMsg

type Checker a = ErrorT TypeError (IOEnv TcEnv) a

getTcEnv :: Checker TcEnv
getTcEnv = lift getEnv

setTcEnv :: TcEnv -> Checker ()
setTcEnv tc_env = lift $ setEnv tc_env

getTypeContext = liftM tceTypeContext getTcEnv

getValueContext = liftM tceValueContext getTcEnv

getTypeServer :: Checker (Handle, Handle)
getTypeServer = liftM tceTypeserver getTcEnv

getMemoizedJavaClasses :: Checker (Set.Set ClassName)
getMemoizedJavaClasses = liftM tceMemoizedJavaClasses getTcEnv

memoizeJavaClass :: ClassName -> Checker ()
memoizeJavaClass c
  = do TcEnv{..} <- getTcEnv
       memoized_java_classes <- getMemoizedJavaClasses
       setTcEnv TcEnv{ tceMemoizedJavaClasses = c `Set.insert` memoized_java_classes, ..}

withLocalTVars :: [(Name, (Kind, Type))] -> Checker a -> Checker a
withLocalTVars tvars do_this
  = do delta <- getTypeContext
       let delta' = Map.fromList tvars `Map.union` delta
       TcEnv {..} <- getTcEnv
       setTcEnv TcEnv { tceTypeContext = delta', ..}
       r <- do_this
       TcEnv {..} <- getTcEnv
       setTcEnv TcEnv { tceTypeContext = delta, ..}
       return r

withLocalVars :: [(Name, Type)]-> Checker a -> Checker a
withLocalVars vars do_this
  = do gamma <- getValueContext
       let gamma' = Map.fromList vars `Map.union` gamma
       TcEnv {..} <- getTcEnv
       setTcEnv TcEnv { tceValueContext = gamma', ..}
       r <- do_this
       TcEnv {..} <- getTcEnv
       setTcEnv TcEnv { tceValueContext = gamma, ..}
       return r

type TypeSubstitution = Map.Map Name Type

applyTSubst :: TypeSubstitution -> Type -> Type
applyTSubst s (TVar a)     = fromMaybe (TVar a) (Map.lookup a s)
-- applyTSubst _ (JClass c)   = JClass c
applyTSubst _ (JType c)    = JType c
applyTSubst s (Fun t1 t2)  = Fun (applyTSubst s t1) (applyTSubst s t2)
applyTSubst s (Forall a t) = Forall a (applyTSubst s' t) where s' = Map.delete a s
applyTSubst _ _            = sorry "TypeCheck.applyTSubst"

kind :: TypeContext -> Type -> IO (Maybe Kind)
kind d (TVar a)     = return (Map.lookup a d)
-- kind _ (JClass c)   = undefined
kind _ (JType c)    = undefined
kind _  Unit        = return (Just Star)
kind d (Fun t1 t2)  = justStarIffAllHaveKindStar d [t1, t2]
kind d (Forall a t) = kind d' t where d' = Map.insert a Star d
kind d (Product ts) = justStarIffAllHaveKindStar d ts
kind d (Record fs)  = justStarIffAllHaveKindStar d (map snd fs)
kind d (ListOf t)   = kind d t
kind d (And t1 t2)  = justStarIffAllHaveKindStar d [t1, t2]
kind d (Thunk t)    = kind d t
kind d (OpApp t1 t2)
  = do maybe_k1 <- kind d t1
       case maybe_k1 of
         Just (KArrow k11 k12) ->
           do maybe_k2 <- kind d t2
              case maybe_k2 of
                Just k2 | k2 == k11 -> return (Just k12)
                _ -> return Nothing
         _ -> return Nothing

justStarIffAllHaveKindStar :: TypeContext -> [Type] -> IO (Maybe Kind)
justStarIffAllHaveKindStar d ts
  = do ps <- mapM (hasKindStar d) ts
       if and ps
          then return (Just Star)
          else return Nothing

hasKindStar :: TypeContext -> Type -> IO Bool
hasKindStar d t
  = do k <- kind d t
       return (k == Just Star)

infer :: Expr Name -> Checker (Expr (Name,Type), Type)
infer (Var name)
  = do value_ctxt <- getValueContext
       case Map.lookup name value_ctxt of
         Just t  -> return (Var (name,t), t)
         Nothing -> throwError (NotInScopeVar name)

infer (Lit lit) = return (Lit lit, srcLitType lit)

infer (Lam (x1,t1) e)
  = do checkType t1
       (e', t) <- withLocalVars [(x1,t1)] (infer e)
       return (Lam (x1,t1) e', Fun t1 t)

infer (App e1 e2)
  = do (e1', t1) <- infer e1
       (e2', t2) <- infer e2
       case t1 of
         Fun t11 t12 -> do t11' <- evalType t11
                           t2'  <- evalType t2
                           unless (dethunk t2' `subtype` dethunk t11') $
                             throwError
                               (General
                                  (bquotes (pretty e1) <+> text "expects an argument of type at least" <+> bquotes (pretty t11) <> comma <+>
                                   text "but the argument" <+> bquotes (pretty e2) <+> text "has type" <+> pretty t2))
                           return (App e1' e2', t12)
         _         -> throwError (General (bquotes (pretty e1) <+> text "is of type" <+> bquotes (pretty t1) <> text "; it cannot be applied"))

infer (BLam a e)
  = do (e', t) <- withLocalTVars [(a, (Star, TVar a))] (infer e)
       return (BLam a e', Forall a t)

infer (TApp e targ)
  = do (e', t) <- infer e
       checkType targ
       case t of
         Forall a t1 -> return (TApp e' targ, fsubstTT (a, targ) t1)
         _           -> sorry "TypeCheck.infer: TApp"

infer (Tuple es)
  | length es < 2 = panic "Src.TypeCheck.infer: Tuple: fewer than two items"
  | otherwise     = do (es', ts) <- mapAndUnzipM infer es
                       return (Tuple es', Product ts)

infer (Proj e i)
  = do (e', t) <- infer e
       case t of
         Product ts
           | 1 <= i && i <= length ts -> return (Proj e' i, ts !! (i - 1))
           | otherwise -> throwError IndexTooLarge
         _ -> throwError ProjectionOfNonProduct

infer (PrimOp e1 op e2)
  = case op of
      Arith _ ->
        do (e1', _t1) <- inferAgainst e1 (JType $ JClass "java.lang.Integer")
           (e2', _t2) <- inferAgainst e2 (JType $ JClass "java.lang.Integer")
           return (PrimOp e1' op e2', JType $ JClass "java.lang.Integer")
      Compare _ ->
        do (e1', t1)  <- infer e1
           (e2', _t2) <- inferAgainst e2 t1
           return (PrimOp e1' op e2', JType $ JClass "java.lang.Boolean")
      Logic _ ->
        do (e1', _t1) <- inferAgainst e1 (JType $ JClass "java.lang.Boolean")
           (e2', _t2) <- inferAgainst e2 (JType $ JClass "java.lang.Boolean")
           return (PrimOp e1' op e2', JType $ JClass "java.lang.Boolean")

infer (If pred b1 b2)
  = do (pred', _pred_ty) <- inferAgainst pred (JType $ JClass "java.lang.Boolean")
       (b1', t1)         <- infer b1
       (b2', _t2)        <- inferAgainst b2 t1
       return (If pred' b1' b2', t1)

infer (Let rec_flag binds e) =
  do checkDupNames (map bindId binds)
     -- type_ctxt <- getTypeContext
     -- when True $
     --     throwError (General $ text (show type_ctxt))
     binds' <- case rec_flag of
                 NonRec -> mapM inferBind binds
                 Rec    -> do sigs <- collectBindNameSigs binds
                              withLocalVars sigs (mapM inferBind binds)
     -- when True $ throwError (General $ text (show binds'))
     (e', t) <- withLocalVars (map (\ (f,t,_) -> (f,t)) binds') (infer e)
     return (LetOut rec_flag binds' e', t)

infer (LetOut{..}) = panic "TypeCheck.infer: LetOut"

infer (JNew c args)
  = do checkClassName c -- TODO: Needed?
       (args', arg_cs) <- mapAndUnzipM inferAgainstAnyJClass args
       checkNew c arg_cs
       return (JNew c args', JType $ JClass c)

infer (JMethod callee m args _)
  = case callee of
      Static c ->
        do (args', arg_cs) <- mapAndUnzipM inferAgainstAnyJClass args
           ret_c <- checkMethodCall (Static c) m arg_cs
           if (ret_c == "char")
             then return (JMethod (Static c) m args' ret_c, JType $ JPrim "char")
             else return (JMethod (Static c) m args' ret_c, JType $ JClass ret_c)
      NonStatic e ->
        do (e', c)         <- inferAgainstAnyJClass e
           (args', arg_cs) <- mapAndUnzipM inferAgainstAnyJClass args
           ret_c <- checkMethodCall (NonStatic c) m arg_cs
           if ret_c == "char"
             then return (JMethod (NonStatic e') m args' ret_c, JType $ JPrim "char")
             else return (JMethod (NonStatic e') m args' ret_c, JType $ JClass ret_c)

infer (JField callee f _)
  = case callee of
      Static c ->
        do ret_c <- checkFieldAccess (Static c) f
           if ret_c == "char"
              then return (JField (Static c) f ret_c, JType $ JPrim ret_c)
              else return (JField (Static c) f ret_c, JType $ JClass ret_c)
      NonStatic e ->
        do (e', t) <- infer e
           case t of
             Record _ -> infer (RecordAccess e f) -- Then the typechecker realized!
             JType (JClass c)   ->
               do ret_c   <- checkFieldAccess (NonStatic c) f
                  if ret_c == "char"
                    then return (JField (NonStatic e') f ret_c, JType $ JPrim "char")
                    else return (JField (NonStatic e') f ret_c, JType $ JClass ret_c)
             _          -> throwError
                           (General
                            (bquotes (pretty e) <+> text "has type" <+> bquotes (pretty t) <>
                             text ", which does not support the dot notation"))

infer (Seq es) = do
  (es', ts) <- mapAndUnzipM infer es
  return (Seq es', last ts)

infer (Merge e1 e2) =
  do (e1', t1) <- infer e1
     (e2', t2) <- infer e2
     return (Merge e1' e2', And t1 t2)

infer (PrimList l) =
      do (es, ts) <- mapAndUnzipM infer l
         case ts of [] -> return (PrimList es, JType $ JClass (namespace ++ "FunctionalList"))
                    _  -> if all (`alphaEq` (ts !! 0)) ts
                            then return (PrimList es, JType $ JClass (namespace ++ "FunctionalList"))
                            else throwError $ General (text "Primitive List Type Mismatch" <+> text (show (PrimList l)))

infer (RecordLit fs) =
  do (es', ts) <- mapAndUnzipM infer (map snd fs)
     return (RecordLit (zip (map fst fs) es'), Record (zip (map fst fs) ts))

infer (RecordAccess e l) =
  do (e', t) <- infer e
     return (RecordAccess e' l, fromJust (lookup (Just l) (fields t)))

infer (RecordUpdate e fs) =
  do (es', ts) <- mapAndUnzipM infer (map snd fs)
     (e', t) <- infer e
     return (RecordUpdate e' (zip (map fst fs) es'), t)

-- Well, I know the desugaring is too early to happen here...
infer (LetModule (Module m binds) e) =
  do let fs = map bindId binds
     let letrec = Let Rec binds (RecordLit (map (\f -> (f, Var f)) fs))
     infer $ Let NonRec [Bind m [] [] letrec Nothing] e
infer (ModuleAccess m f) = infer (RecordAccess (Var m) f)

infer (Type tid params rhs e)
  = do checkDupNames params
       withLocalTVars [(tid, (k params, pullRight params rhs))] (infer e)
  where k []     = Star
        k (_:as) = KArrow Star (k as)
        pullRight as t = foldr OpAbs t as

infer (Data name cs e) =
    do let names = map constrName cs
       checkDupNames names
       -- let dt = Datatype name names
       -- type_ctxt <- withLocalTVars [(name, (Star, dt))] getTypeContext
       type_ctxt <- getTypeContext
       -- types <- mapM (mapM (substTVar type_ctxt) . constrParams) cs

       -- let dt = Datatype name constrBindings
       --     type_ctxt' = Map.insert name (Star, dt) type_ctxt
       --     types' = map (map (substTVar type_ctxt') . constrParams) cs
       --     constrBindings = zip names (map (foldTypes dt) types')

       let dt = Datatype name names
           type_ctxt' = Map.insert name (Star, dt) type_ctxt
           types' = map (map (substTVar type_ctxt') . constrParams) cs
           constrBindings = zip names (map (foldTypes dt) types')
       withLocalTVars [(name, (Star, dt))] (withLocalVars constrBindings (infer e))

    where substTVar :: Map.Map Name (Kind, Type) -> Type -> Type
          substTVar ctxt t =
              case t of
                TVar n ->
                    case Map.lookup n ctxt of
                           Just (_, t') -> t'
                           _ -> t
                _ -> t

    -- where substTVar :: Map.Map Name (Kind, Type) -> Name -> Type -> Checker Type
    --       substTVar ctxt self t =
    --           case t of
    --             TVar n ->
    --                 if n == self
    --                 then return t
    --                 else case Map.lookup n ctxt of
    --                        Just (_, t') -> return t'
    --                        _ -> throwError (NotInScopeTVar n)
    --             _ -> return t

          -- substSelf :: Type -> Type -> Type
          -- substSelf dt (TVar _) = dt
          -- substSelf _ t = t

infer (Constr c es) =
    do value_ctxt <- getValueContext
       let n = constrName c
       ts <- case Map.lookup n value_ctxt of
                  Just t -> return $ unfoldTypes t
                  Nothing -> throwError (NotInScopeConstr n)
       let (len_expected, len_actual) = (length ts - 1, length es)
       unless (len_expected == len_actual) $
              throwError (General $ text "Constructor" <+> bquotes (text n) <+> text "should have" <+> int len_expected <+> text "arguments, but has been given" <+> int len_actual)
       (es', _) <- mapAndUnzipM (\(e',t) -> inferAgainst e' t) (zip es ts)
       return (Constr (Constructor n ts) es', last ts)

infer (Case e alts) =
    do (e', t) <- infer e
       unless (isDatatype t) $
              throwError (General (bquotes (pretty e) <+> text "is of type" <+> bquotes (pretty t) <> comma <+> text "which is not a datatype"))
       value_ctxt <- getValueContext
       let ns = (\(Datatype _ xs) -> xs) t
           constrs = map (\(ConstrAlt c _ _) -> c) alts
       constrs' <- mapM (\c -> let n = constrName c
                               in case Map.lookup n value_ctxt of
                                    Just t' -> let ts = unfoldTypes t'
                                               in if last ts `alphaEq` t
                                                  then return $ Constructor n ts
                                                  else throwError (Mismatch t t')
                                    Nothing -> throwError (NotInScopeConstr n))
                   constrs
       -- let nts = (\(Datatype _ xs) -> xs) t
       --     constrs = map (\(ConstrAlt c _ _) -> c) alts
       -- -- Fill in the constrParams
       -- constrs' <- mapM (\c -> let n = constrName c
       --                      in case lookup n nts of
       --                       Just ts -> return $ Constructor {constrName=n, constrParams=unfoldTypes ts}
       --                       Nothing -> throwError (NotInScopeConstr n)) constrs
       let alts' = zipWith substAltConstr alts constrs'

       (es, ts) <- mapAndUnzipM
                   (\(ConstrAlt c ns e2) ->
                        let n = constrName c
                            ts = init $ constrParams c
                        in if length ts == length ns
                           then withLocalVars (zip ns ts) (infer e2)
                           else throwError (General $ text "Constructor" <+> bquotes (text n) <+> text "should have" <+> int (length ts)
                                                                     <+> text "arguments, bus has been given" <+> int (length ns)))
                   alts'

       let resType = ts !! 0
       unless (all (`alphaEq` resType) ts) $
              throwError (General $ text "All the alternatives should be of the same type")

       let allConstrs = Set.fromList ns
       let matchedConstrs = Set.fromList $ map constrName constrs
       let unmatchedConstrs = allConstrs Set.\\ matchedConstrs
       unless (Set.null unmatchedConstrs) $
              throwError (General $ text "Pattern match(es) are non-exhaustive." <+> vcat (intersperse space (map (bquotes . text) (Set.elems unmatchedConstrs))))

       return (Case e' (zipWith substAltExpr alts' es), resType)

    where substAltExpr (ConstrAlt c ns _) expr = ConstrAlt c ns expr
          substAltConstr (ConstrAlt _ ns expr) c = ConstrAlt c ns expr

          isDatatype (Datatype _ _) = True
          isDatatype _ = False

inferAgainst :: Expr Name -> Type -> Checker (Expr (Name,Type), Type)
inferAgainst expr expected_ty
  = do (expr', actual_ty) <- infer expr
       if actual_ty `alphaEq` expected_ty
          then return (expr', actual_ty)
          else throwError (Mismatch expected_ty actual_ty)

inferAgainstAnyJClass :: Expr Name -> Checker (Expr (Name,Type), ClassName)
inferAgainstAnyJClass expr
  = do (expr', ty) <- infer expr
       case dethunk ty of
        JType (JPrim "char") -> return (expr', "java.lang.Character")
        JType (JClass c) -> return (expr', c)
        _ -> throwError $ General (bquotes (pretty expr) <+> text "has type" <+> bquotes (pretty ty) <> comma <+> text "but is expected to be of some Java class")

inferAgainstMaybe :: Expr Name -> Maybe Type -> Checker (Expr (Name,Type), Type)
inferAgainstMaybe e Nothing  = infer e
inferAgainstMaybe e (Just t) = inferAgainst e t

-- f A1 ... An (x1:T1) ... (xn:Tn) = e
inferBind :: Bind Name -> Checker (Name, Type, Expr (Name,Type))
inferBind bind
  = do bind' <- checkBindLHS bind
       -- type_ctxt <- getTypeContext
       -- when True $
       --   throwError (General $ text (show type_ctxt))
       (bindRhs', bindRhsTy) <- withLocalTVars (map (\a -> (a, (Star, TVar a))) (bindTargs bind')) $
                                  do expandedBindArgs <- mapM (\(x,t) -> do { t' <- evalType t; return (x,t') }) (bindArgs bind')
                                     withLocalVars expandedBindArgs (infer (bindRhs bind'))
       (bindRhs', bindRhsTy) <- withLocalTVars (map (\a -> (a, (Star, TVar a))) (bindTargs bind')) $
                                  do expandedBindArgs <- mapM (\(x,t) -> do { t' <- evalType t; return (x,t') }) (bindArgs bind')
                                     withLocalVars expandedBindArgs (infer (bindRhs bind'))
       return ( (bindId bind')
              , wrap Forall (bindTargs bind') (wrap Fun (map snd (bindArgs bind')) bindRhsTy)
              , wrap BLam (bindTargs bind') (wrap Lam (bindArgs bind') bindRhs'))

checkBindLHS :: Bind Name -> Checker (Bind Name)
checkBindLHS bind@Bind{..}
  = do checkDupNames bindTargs
       checkDupNames [x | (x, _) <- bindArgs]
       bindArgs' <-
         forM bindArgs (\(x, t) ->
          do --checkType t
             t' <- evalType t
             return (x,t'))
       -- when True $ throwError (General $ text $ show bindArgs')
       bindArgs' <- withLocalTVars (map (\a -> (a, (Star, TVar a))) bindTargs) $
         forM bindArgs (\(x, t) ->
          do --checkType t
             t' <- evalType t
             return (x,t'))
       return bind { bindArgs = bindArgs' }

collectBindNameSigs :: [Bind Name] -> Checker [(Name, Type)]
collectBindNameSigs
  = mapM (\ Bind{..} ->
            case bindRhsAnnot of
              Nothing    -> throwError MissingRHSAnnot
              Just rhsTy -> return (bindId,
                                    wrap Forall bindTargs $
                                    wrap Fun [ty |  (_,ty) <- bindArgs]
                                    rhsTy))

checkType :: Type -> Checker ()
checkType t
  = case t of
      JType (JClass c) -> checkClassName c
      _        ->
        do type_ctxt <- getTypeContext
           let free_ty_vars = freeTVars t `Set.difference` Set.fromList (map fst (filter (\(_,(k,_)) -> k == Star) (Map.toList type_ctxt)))
           unless (Set.null free_ty_vars) $
             throwError (NotInScopeTVar (head (Set.toList free_ty_vars)))

unlessIO :: (Monad m, MonadIO m) => IO Bool -> m () -> m ()
unlessIO test do_this
  = do ok <- liftIO test
       unless ok do_this

checkClassName :: ClassName -> Checker ()
checkClassName c
  = do memoized_java_classes <- getMemoizedJavaClasses
       unless (c `Set.member` memoized_java_classes) $
         do h  <- getTypeServer
            res <- liftIO (isJvmType h c)
            if res
               then memoizeJavaClass c
               else throwError (NoSuchClass c)

checkNew :: ClassName -> [ClassName] -> Checker ()
checkNew c args
  = do h <- getTypeServer
       unlessIO (hasConstructor h c args) $
         throwError (NoSuchConstructor c args)

checkMethodCall :: JCallee ClassName -> MethodName -> [ClassName] -> Checker ClassName
checkMethodCall callee m args
  = do typeserver <- getTypeServer
       res <- liftIO (methodTypeOf typeserver c (m, static_flag) args)
       case res of
         Nothing           -> throwError (NoSuchMethod callee m args)
         Just return_class -> return return_class
    where
       (static_flag, c) = unwrapJCallee callee

checkFieldAccess :: JCallee ClassName -> FieldName -> Checker ClassName
checkFieldAccess callee f
  = do typeserver <- getTypeServer
       res <- liftIO (fieldTypeOf typeserver c (f, static_flag))
       case res of
         Nothing           -> throwError (NoSuchField callee f)
         Just return_class -> return return_class
    where
       (static_flag, c) = unwrapJCallee callee

evalType :: Type -> Checker Type
evalType (TVar a)
  = do typeContext <- getTypeContext
       case Map.lookup a typeContext of
         Nothing      -> return (TVar a)
         Just (_, t') -> if t' == TVar a then return t' else evalType t'
evalType (JType (JClass c)) = return (JType $ JClass c)
evalType Unit       = return Unit
evalType (Fun t1 t2)
  = do t1' <- evalType t1
       t2' <- evalType t2
       return (Fun t1' t2')
evalType (Forall a t)
  = do t' <- withLocalTVars [(a, (Star, TVar a))] (evalType t)
       return (Forall a t')
evalType (Product ts)
  = do ts' <- mapM evalType ts
       return (Product ts')
evalType (Record fs)
  = do ts' <- mapM (evalType . snd) fs
       return (Record (zip (map fst fs) ts'))
evalType (ListOf t)
  = do t' <- evalType t
       return (ListOf t')
evalType (And t1 t2)
  = do t1' <- evalType t1
       t2' <- evalType t2
       return (And t1' t2')
evalType (Thunk t)
  = do t' <- evalType t
       return (Thunk t')
evalType (OpApp (TVar t1) t2)
  = do typeContext <- getTypeContext
       case Map.lookup t1 typeContext of
         Just (_, OpAbs param t) -> return (fsubstTT (param, t2) t)
evalType t@(Datatype _ _) = return t -- TODO

unwrapJCallee :: JCallee ClassName -> (Bool, ClassName)
unwrapJCallee (NonStatic c) = (False, c)
unwrapJCallee (Static    c) = (True, c)

srcLitType :: Lit -> Type
srcLitType (Int _)    = JType $ JClass "java.lang.Integer"
srcLitType (String _) = JType $ JClass "java.lang.String"
srcLitType (Bool _)   = JType $ JClass "java.lang.Boolean"
srcLitType (Char _)   = JType $ JClass "java.lang.Character"
srcLitType UnitLit    = Unit

checkDupNames :: [Name] -> Checker ()
checkDupNames names
  = case findDup names of
      Nothing   -> return ()
      Just name -> throwError (ConflictingDefinitions name)

findDup :: Ord a => [a] -> Maybe a
findDup xs = go xs Set.empty
  where
    go []      _ = Nothing
    go (x:xs') s = if Set.member x s
                     then Just x
                     else go xs' (Set.insert x s)

foldTypes :: Type -> [Type] -> Type
foldTypes = foldr (\t base -> Fun t base)

unfoldTypes :: Type -> [Type]
unfoldTypes t@(Datatype _ _) = [t]
unfoldTypes (Fun t t') = t : unfoldTypes t'
