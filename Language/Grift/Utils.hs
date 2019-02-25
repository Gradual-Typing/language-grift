{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Utils where

newtype HFix h a = HFix { unHFix :: h (HFix h) a }
newtype Fix f = Fix {unFix :: f (Fix f)}

deriving instance (Show (t (Fix t))) => Show (Fix t)
