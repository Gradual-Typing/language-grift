{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Blame.Syntax where

import Data.Type.Equality

import Language.Grift.Source.Syntax hiding (Unit)
import Language.Grift.TypeContext

import Data.Singletons
import Data.Singletons.Prelude hiding (Elem)
import Data.Singletons.Decide


unrefineTy :: SType ty -> Type
unrefineTy = fromSing

refineTy :: forall r. Type -> (forall ty. SType ty -> r) -> r
refineTy t k = case toSing t of
  SomeSing st -> k st

eqSTy :: forall ty1 ty2. SType ty1 -> SType ty2 -> Maybe (ty1 :~: ty2)
eqSTy t1 t2 = case t1 %~ t2 of
  Proved Refl -> Just Refl
  Disproved _ -> Nothing

data ConsistList :: [Type] -> [Type] -> * where
  CLNil  :: ConsistList '[] '[]
  CLCons :: Consist t t'
          -> ConsistList ts ts'
          -> ConsistList (t ': ts) (t' ': ts')

data Consist :: Type -> Type -> * where
  DynL  :: Consist 'Dyn t
  DynR  :: Consist t 'Dyn
  Char  :: Consist 'CharTy 'CharTy
  Float :: Consist 'FloatTy 'FloatTy
  Int   :: Consist 'IntTy 'IntTy
  Bool  :: Consist 'BoolTy 'BoolTy
  Unit  :: Consist 'UnitTy 'UnitTy
  Fun   :: Consist ret1 ret2
        -> ConsistList args1 args2
        -> Consist ('FunTy args1 ret1) ('FunTy args2 ret2)
  Arr   :: Consist ret1 ret2
        -> ConsistList args1 args2
        -> Consist ('ArrTy args1 ret1) ('ArrTy args2 ret2)
  Ref   :: Consist t t' -> Consist ('RefTy t) ('RefTy t')
  GRef  :: Consist t t' -> Consist ('GRefTy t) ('GRefTy t')
  MRef  :: Consist t t' -> Consist ('MRefTy t) ('MRefTy t')
  Vect  :: Consist t t' -> Consist ('VectTy t) ('VectTy t')
  GVect :: Consist t t' -> Consist ('GVectTy t) ('GVectTy t')
  MVect :: Consist t t' -> Consist ('MVectTy t) ('MVectTy t')
  Tuple :: ConsistList args1 args2
        -> Consist ('TupleTy args1) ('TupleTy args2)

consistList :: SList l1 -> SList l2 -> Maybe (ConsistList l1 l2)
consistList SNil SNil = Just CLNil
consistList SNil _ = Nothing
consistList _ SNil = Nothing
consistList (SCons t ts) (SCons t' ts') = do
  x  <- consist t t'
  xs <- consistList ts ts'
  return (CLCons x xs)


consist :: SType ty1 -> SType ty2 -> Maybe (Consist ty1 ty2)
consist SDyn _ = Just DynL
consist _ SDyn = Just DynR
consist SIntTy SIntTy = Just Int
consist SFloatTy SFloatTy = Just Float
consist SBoolTy SBoolTy = Just Bool
consist SUnitTy SUnitTy = Just Unit
consist (SFunTy args1 ret1) (SFunTy args2 ret2) = do
  x  <- consist ret1 ret2
  xs <- consistList args1 args2
  return (Fun x xs)
consist (SArrTy args1 ret1) (SArrTy args2 ret2) = do
  x  <- consist ret1 ret2
  xs <- consistList args1 args2
  return (Arr x xs)
consist (SRefTy t) (SRefTy t') = do
  x  <- consist t t'
  return (Ref x)
consist (SGRefTy t) (SGRefTy t') = do
  x  <- consist t t'
  return (GRef x)
consist (SMRefTy t) (SMRefTy t') = do
  x  <- consist t t'
  return (MRef x)
consist (SVectTy t) (SVectTy t') = do
  x  <- consist t t'
  return (Vect x)
consist (SGVectTy t) (SGVectTy t') = do
  x  <- consist t t'
  return (GVect x)
consist (SMVectTy t) (SMVectTy t') = do
  x  <- consist t t'
  return (MVect x)
consist (STupleTy ts) (STupleTy ts') = do
  x  <- consistList ts ts'
  return (Tuple x)
consist _ _ = Nothing

type Context     = [Type]
type StoreTyping = [Type]

data Args  :: StoreTyping -> Context -> [Type] -> * where
  ArgsNil  :: Args storeTy ctx '[]
  ArgsCons :: Exp storeTy ctx t
           -> Args storeTy ctx ts
           -> Args storeTy ctx (t ': ts)

data Exp :: StoreTyping -> Context -> Type -> * where
  -- DConst Name t e
  -- | DLam Name Args e t
  -- | Lam Args e t
  Lam :: Exp storeTy (args ++ ctx) res
      -> Exp storeTy ctx ('FunTy args res)
  Var :: String -> Elem ctx ty -> Exp storeTy ctx ty
  App :: Exp storeTy ctx ('FunTy args res)
      -> Args storeTy ctx args
      -> Exp storeTy ctx res
  -- | Bind Name t e
  -- | As e t
  -- | Repeat Name Name e e e e t
  -- | Op Operator [e]
  -- | TopLevel [e] [e]
  -- | If e e e
  -- | App e [e]
  -- | Ref e
  -- | DeRef e
  -- | Assign e e
  -- | GRef e
  -- | GDeRef e
  -- | GAssign e e
  -- | MRef e
  -- | MDeRef e
  -- | MAssign e e
  -- | Vect e e -- length value
  -- | VectRef e e -- vect pos
  -- | VectSet e e e -- vect pos value
  -- | GVect e e -- length value
  -- | GVectRef e e -- vect pos
  -- | GVectSet e e e -- vect pos value
  -- | MVect e e
  -- | MVectRef e e
  -- | MVectSet e e e
  -- | Tuple [e]
  -- | TupleProj e Int
  -- | Let [e] e
  -- | Letrec [e] e
  -- | Begin [e] e
  -- | Time e
  -- P Prim


deriving instance Show (Args storeTy ctx ts)
deriving instance Show (Exp storeTy ctx t)
