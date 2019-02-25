{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Language.Grift.Source.Check where

import Control.Monad.Except (ExceptT, MonadError, runExceptT, throwError)
import Data.Type.Equality

import qualified Language.Grift.Source.Syntax as S
import qualified Language.Grift.Blame.Syntax as B
import Language.Grift.TypeContext
import Language.Grift.Utils


-- | Check the given expression, aborting on type errors. The resulting
-- type and checked expression is given to the provided continuation.
-- This is parameterized over the choice of monad in order to support
-- pure operation during testing. 'GriftE' is the canonical choice for the
-- monad.
check :: MonadError String m
      => Fix (S.ExpF S.Type)
      -> (forall t . S.SType t -> B.Exp '[] '[] t -> m r)
      -> m r
check (Fix e) = go SCtxNil SCtxNil e
  where
    go :: (MonadError String m)
       => SCtx ctx
       -> SStoreTyping storeTy
       -> S.ExpF S.Type (Fix (S.ExpF S.Type))
       -> (forall t. S.SType t -> B.Exp storeTy ctx t -> m r)
       -> m r

    go ctx storeTy (S.LamF _ (Fix body) ty) k
      = B.refineTy ty $ \sty ->
        go ctx storeTy body $ \res_ty body' ->
                                case sty of
                                  (S.SFunTy args_ty ret_ty) ->
                                    case B.consist res_ty ret_ty of
                                      _ -> k (args_ty `S.SFunTy` res_ty) (B.Lam body')

    go ctx storeTy (S.LamF (t : ts) (Fix body) ty) k
      = undefined

    go ctx storeTy (S.PF (S.Var x n)) k
      = check_var ctx storeTy n $ \ty elem ->
        k ty $ B.Var x elem

    go ctx storeTy e@(S.AppF (Fix e1) (Fix e2:[])) k
      = go ctx storeTy e1 $ \ty1 e1' ->
        go ctx storeTy e2 $ \ty2 e2' ->
        case (unHFix ty1, ty2) of
          (S.SFunTy arg_ty res_ty, arg_ty')
            |  Just Refl <- arg_ty `B.eqSTy` arg_ty'
            -> k res_ty (B.App e1' e2')
          _ -> undefined -- typeError e $
               -- ("Bad function application. Function type: " ++ show ty1 ++ " Argument type: " ++ show ty2)

-- typeError :: MonadError String m => S.ExpF (B.FType) (Fix (S.ExpF (B.FType))) -> String -> m a
-- typeError e doc = throwError (doc ++ "in the expression" ++ (show e))
                  
check_var :: MonadError String m
          => SCtx ctx
          -> Int
          -> (forall t. S.SType t -> Elem ctx t -> m r)
          -> m r
check_var SCtxNil           _ _ = throwError "unbound variable" -- shouldn't happen. caught by parser.
check_var (SCtxCons ty _)   0 k = k ty EZ
check_var (SCtxCons _  ctx) n k = check_var ctx (n-1) $ \ty elem ->
                               k ty (ES elem)

newtype Grift a = Grift { unGrift :: Maybe a }
  deriving (Monad, Functor, Applicative, Show)

newtype GriftE a = GriftE { unGriftE :: ExceptT String Grift a }
  deriving (Monad, Functor, Applicative, MonadError String)

runGriftE :: GriftE a -> Grift (Either String a)
runGriftE g = runExceptT $ unGriftE g

ex :: Grift (Either String S.Type)
ex = runGriftE $ check (Fix (S.LamF ["x"] (Fix (S.PF (S.Var "x" 0))) (Fix S.IntTy))) $ \x y ->
  return $ B.unrefineTy x
