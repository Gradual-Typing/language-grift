module Language.Grift.Source.Parser.WithSourcePos( TypeWithLoc
                                                 , ExpF1
                                                 , L1) where

import           Text.Parsec.Pos (SourcePos)

import           Language.Grift.Source.Syntax

type WithLoc a = Ann SourcePos a

type TypeWithLoc = WithLoc TypeF
type ExpF1 = ExpF TypeWithLoc
type L1 = WithLoc ExpF1
