{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

module Language.Grift.TypeContext where

import Language.Grift.Source.Syntax

-- | Singleton for a typing context
data SCtx :: [Type] -> * where
  SCtxNil  :: SCtx '[]
  SCtxCons :: SType ty -> SCtx tys -> SCtx (ty ': tys)
infixr 5 `SCtxCons`

type SStoreTyping = SCtx

-- | @Elem xs x@ is evidence that @x@ is in the list @xs@.
-- @EZ :: Elem xs x@ is evidence that @x@ is the first element of @xs@.
-- @ES ev :: Elem xs x@ is evidence that @x@ is one position later in
-- @xs@ than is indicated in @ev@
data Elem :: [a] -> a -> * where
  EZ :: Elem (x ': xs) x
  ES :: Elem xs x -> Elem (y ': xs) x

deriving instance Show (Elem l a)
