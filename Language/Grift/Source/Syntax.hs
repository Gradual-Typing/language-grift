{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE DefaultSignatures    #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE NoStarIsType         #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Source.Syntax(
  Name
  , Operator(..)
  , Type(..)
  , TypeF(..)
  , SType
  , Sing (..)
  , ExpF(..)
  , Prim(..)
  , Ann(..)
  , (⊑)) where

import           Data.Functor.Foldable.TH
import           Data.Singletons.TH

import           Algebra.Lattice
import           Data.Bifunctor.TH

type Name = String
type Args = [Name]

data Operator = Plus | Minus | Mult | Div | Eq | Ge | Gt | Le | Lt
              | ShiftR | ShiftL | BAnd | BOr
              | PlusF | MinusF | MultF | DivF| ModuloF | AbsF | LtF
              | LeF | EqF | GtF | GeF | MinF | MaxF | RoundF | FloorF
              | CeilingF | TruncateF | SinF | CosF | TanF | AsinF
              | AcosF | AtanF | LogF | ExpF | SqrtF | ExptF
              | FloatToInt | IntToFloat | CharToInt | ReadInt
              | ReadFloat | ReadChar | DisplayChar
                deriving (Eq,Show)

data Exp t =
  DConst Name t (Exp t)
  | DLam Name Args (Exp t) t
  | Lam Args (Exp t) t
  | Bind Name t (Exp t)
  | As (Exp t) t
  | Repeat Name Name (Exp t) (Exp t) (Exp t) (Exp t) t
  | Op Operator [Exp t]
  | TopLevel [Exp t] [Exp t]
  | If (Exp t) (Exp t) (Exp t)
  | App (Exp t) [Exp t]
  | Ref (Exp t)
  | DeRef (Exp t)
  | Assign (Exp t) (Exp t)
  | GRef (Exp t)
  | GDeRef (Exp t)
  | GAssign (Exp t) (Exp t)
  | MRef (Exp t)
  | MDeRef (Exp t)
  | MAssign (Exp t) (Exp t)
  | Vect (Exp t) (Exp t) -- length value
  | VectRef (Exp t) (Exp t) -- vect pos
  | VectSet (Exp t) (Exp t) (Exp t) -- vect pos value
  | GVect (Exp t) (Exp t) -- length value
  | GVectRef (Exp t) (Exp t) -- vect pos
  | GVectSet (Exp t) (Exp t) (Exp t) -- vect pos value
  | MVect (Exp t) (Exp t)
  | MVectRef (Exp t) (Exp t)
  | MVectSet (Exp t) (Exp t) (Exp t)
  | Tuple [Exp t]
  | TupleProj (Exp t) Int
  | Let [Exp t] (Exp t)
  | Letrec [Exp t] (Exp t)
  | Begin [Exp t] (Exp t)
  | Time (Exp t)
  | P Prim

data Prim =
  Var String Int
  | Global String
  | N Integer
  | F Double String
  | B Bool
  | Unit
  | C String
  deriving (Eq, Show)

makeBaseFunctor ''Exp

$(deriveBifunctor ''ExpF)
$(deriveBifoldable ''ExpF)
$(deriveBitraversable ''ExpF)

$(singletons [d|
               data Type =
                 BlankTy
                 | Dyn
                 | CharTy
                 | IntTy
                 | FloatTy
                 | BoolTy
                 | UnitTy
                 | FunTy [Type] Type
                 | ArrTy [Type] Type
                 | RefTy Type
                 | GRefTy Type
                 | MRefTy Type
                 | VectTy Type
                 | GVectTy Type
                 | MVectTy Type
                 | TupleTy [Type]
                 deriving (Eq,Show)
  |])

makeBaseFunctor ''Type

deriving instance (Show a, Show (e (Ann a e))) => Show (Ann a e)
deriving instance (Show a, Show (t (Ann a t))) => Show (ExpF (Ann a t) (Ann a (ExpF (Ann a t))))
deriving instance (Show a, Show (t (Ann a t))) => Show (TypeF (Ann a t))

instance MeetSemiLattice Type where
  Dyn /\ t                           = t
  t /\ Dyn                           = t
  CharTy /\ CharTy                   = CharTy
  IntTy /\ IntTy                     = IntTy
  FloatTy /\ FloatTy                 = FloatTy
  BoolTy /\ BoolTy                   = BoolTy
  UnitTy /\ UnitTy                   = UnitTy
  (FunTy ts1 rt1) /\ (FunTy ts2 rt2) =
    FunTy (zipWith (/\) ts1 ts2) $ (/\) rt1 rt2
  (ArrTy ts1 rt1) /\ (ArrTy ts2 rt2) =
    ArrTy (zipWith (/\) ts1 ts2) $ (/\) rt1 rt2
  (RefTy t1) /\ (RefTy t2)           = RefTy $ (/\) t1 t2
  (GRefTy t1) /\ (GRefTy t2)         = GRefTy $ (/\) t1 t2
  (MRefTy t1) /\ (MRefTy t2)         = MRefTy $ (/\) t1 t2
  (VectTy t1) /\ (VectTy t2)         = VectTy $ (/\) t1 t2
  (GVectTy t1) /\ (GVectTy t2)       = GVectTy $ (/\) t1 t2
  (MVectTy t1) /\ (MVectTy t2)       = MVectTy $ (/\) t1 t2
  (TupleTy t1) /\ (TupleTy t2)       = TupleTy $ zipWith (/\) t1 t2
  t1 /\ t2                             =
    error ("/\\: undefined on " ++ show t1 ++ " and " ++ show t2)

instance JoinSemiLattice Type where
  Dyn \/ _                           = Dyn
  _ \/ Dyn                           = Dyn
  CharTy \/ CharTy                   = CharTy
  IntTy \/ IntTy                     = IntTy
  FloatTy \/ FloatTy                 = FloatTy
  BoolTy \/ BoolTy                   = BoolTy
  UnitTy \/ UnitTy                   = UnitTy
  (FunTy ts1 rt1) \/ (FunTy ts2 rt2) =
    FunTy (zipWith (\/) ts1 ts2) $ (\/) rt1 rt2
  (ArrTy ts1 rt1) \/ (ArrTy ts2 rt2) =
    ArrTy (zipWith (\/) ts1 ts2) $ (\/) rt1 rt2
  (RefTy t1) \/ (RefTy t2)           = RefTy $ (\/) t1 t2
  (GRefTy t1) \/ (GRefTy t2)         = GRefTy $ (\/) t1 t2
  (MRefTy t1) \/ (MRefTy t2)         = MRefTy $ (\/) t1 t2
  (VectTy t1) \/ (VectTy t2)         = VectTy $ (\/) t1 t2
  (GVectTy t1) \/ (GVectTy t2)       = GVectTy $ (\/) t1 t2
  (MVectTy t1) \/ (MVectTy t2)       = MVectTy $ (\/) t1 t2
  (TupleTy t1) \/ (TupleTy t2)       = TupleTy $ zipWith (\/) t1 t2
  t1 \/ t2                           =
    error ("\\/: undefined on " ++ show t1 ++ " and " ++ show t2)

instance Lattice Type where

(⊑) :: Type -> Type -> Bool
(⊑) = joinLeq

data Ann a e = Ann a (e (Ann a e))
