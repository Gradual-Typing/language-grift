{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Source.Syntax(
  Name
  , Operator(..)
  , Type(..)
  , ExpF(..)
  , Prim(..)
  , Ann(..)
  , (⊑)) where

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

-- base functor (two-level types trick)
-- structure operator
data ExpF t e =
  DConst Name t e
  | DLam Name Args e t
  | Lam Args e t
  | Bind Name t e
  | As e t
  | Repeat Name Name e e e e t
  | Op Operator [e]
  | TopLevel [e] [e]
  | If e e e
  | App e [e]
  | Ref e
  | DeRef e
  | Assign e e
  | GRef e
  | GDeRef e
  | GAssign e e
  | MRef e
  | MDeRef e
  | MAssign e e
  | Vect e e -- length value
  | VectRef e e -- vect pos
  | VectSet e e e -- vect pos value
  | GVect e e -- length value
  | GVectRef e e -- vect pos
  | GVectSet e e e -- vect pos value
  | MVect e e
  | MVectRef e e
  | MVectSet e e e
  | Tuple [e]
  | TupleProj e Int
  | Let [e] e
  | Letrec [e] e
  | Begin [e] e
  | Time e
  | P Prim

data Prim =
  Var Name
  | N Integer
  | F Double String
  | B Bool
  | Unit
  | C String
  deriving (Eq, Show)

deriving instance Functor (ExpF t)
deriving instance Foldable (ExpF t)
deriving instance Traversable (ExpF t)

$(deriveBifunctor ''ExpF)
$(deriveBifoldable ''ExpF)
$(deriveBitraversable ''ExpF)

data Type t =
  BlankTy
  | Dyn
  | CharTy
  | IntTy
  | FloatTy
  | BoolTy
  | UnitTy
  | FunTy [t] t
  | ArrTy [t] t
  | RefTy t
  | GRefTy t
  | MRefTy t
  | VectTy t
  | GVectTy t
  | MVectTy t
  | TupleTy [t]
  deriving (Eq,Show,Functor)

deriving instance (Show a, Show (e (Ann a e))) => Show (Ann a e)
deriving instance (Show a, Show (t (Ann a t))) => Show (ExpF (Ann a t) (Ann a (ExpF (Ann a t))))

instance (MeetSemiLattice t, Show t) => MeetSemiLattice (Type t) where
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

instance (JoinSemiLattice t, Show t) => JoinSemiLattice (Type t) where
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

instance (JoinSemiLattice t, MeetSemiLattice t, Show t) => Lattice (Type t) where

(⊑) :: (Eq t, Show t, JoinSemiLattice t) => Type t -> Type t -> Bool
(⊑) = joinLeq

data Ann a e = Ann a (e (Ann a e))
