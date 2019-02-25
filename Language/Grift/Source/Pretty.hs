{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Grift.Source.Pretty (
  codeGen
  , Pretty
  ) where

import           Prelude hiding ((<>))
import           Text.PrettyPrint

import           Language.Grift.Source.Syntax

indent :: Doc -> Doc
indent = nest 2

vcat' :: [Doc] -> Doc
vcat' = foldr ($+$) empty

class Pretty p where
  ppe :: p -> Doc

instance Pretty Name where
  ppe = text

instance Pretty Prim where
  ppe (Var x _) = text x
  ppe (Global x) = text x
  ppe (N a)   = integer a
  ppe (F _ s) = text s
  ppe (B b)   = ppe b
  ppe Unit    = text "()"
  ppe (C c)   = text "#\\" <> ppe c

instance Pretty (e (Ann a e)) => Pretty (Ann a e) where
  ppe (Ann _ e) = ppe e

pparg :: Name -> Ann a TypeF -> Doc
pparg a (Ann _ BlankTyF) = ppe a
pparg a t               = lbrack <> ppe a <+> char ':' <+> ppe t <> rbrack

instance (Pretty e, Show a) => Pretty (ExpF (Ann a TypeF) e) where
  ppe (OpF op es)                 = parens $ ppe op <+> hsep (map ppe es)
  ppe (IfF e1 e2 e3)              = parens $ text "if" <+> ppe e1 $+$ indent (ppe e2) $+$ indent (ppe e3)
  ppe (AppF e1 es)                = parens $ ppe e1 <+> hsep (map ppe es)
  ppe (TopLevelF d es)            = vcat' (map ppe d) $+$ indent (vcat' $ map ppe es)
  ppe (LamF xs e (Ann _ (ArrTyF ts (Ann _ t))))    =
    parens (text "lambda" <+> parens
            (vcat' (zipWith pparg xs ts)) <+>
            (case t of
               BlankTyF -> empty
               _       -> char ':' <+> ppe t)
            $+$ indent (ppe e))
  ppe (LamF _ _ t)                = error ("defined as lambda but has type" ++ show t)
  ppe (DConstF x (Ann _ t) e)     = parens $ text "define" <+> text x <+>
    (case t of
        BlankTyF -> ppe e
        _       -> char ':' <+> ppe t <+> ppe e)
  ppe (DLamF x xs e (Ann _ (ArrTyF ts (Ann _ t)))) = parens $ text "define" <+>
    parens (text x <+> vcat' (zipWith pparg xs ts)) <+>
    (case t of
       BlankTyF -> empty
       _       -> char ':' <+> ppe t)
    $+$ indent (ppe e)
  ppe (DLamF x _ _ (Ann _ t))     = error (x ++ " is defined as lambda but has type: " ++ show t)
  ppe (BindF x (Ann _ BlankTyF) e) = brackets (text x $+$ indent (ppe e))
  ppe (BindF x t e)               =
    brackets (text x <+> char ':' <+> ppe t $+$ indent (ppe e))
  ppe (RefF e)                    = parens $ text "box" <+> ppe e
  ppe (DeRefF e)                  = parens $ text "unbox" <+> ppe e
  ppe (AssignF e1 e2)             = parens $ text "box-set!" <+> ppe e1 <+> ppe e2
  ppe (GRefF e)                   = parens $ text "gbox" <+> ppe e
  ppe (GDeRefF e)                 = parens $ text "gunbox" <+> ppe e
  ppe (GAssignF e1 e2)            = parens $ text "gbox-set!" <+> ppe e1 <+> ppe e2
  ppe (MRefF e)                   = parens $ text "mbox" <+> ppe e
  ppe (MDeRefF e)                 = parens $ text "munbox" <+> ppe e
  ppe (MAssignF e1 e2)            = parens $ text "mbox-set!" <+> ppe e1 <+> ppe e2
  ppe (VectF e1 e2)               = parens $ text "vector" <+> ppe e1 <+> ppe e2
  ppe (VectRefF e1 e2)            = parens $ text "vector-ref" <+> ppe e1 <+> ppe e2
  ppe (VectSetF e1 e2 e3)         = parens $ text "vector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (GVectF e1 e2)              = parens $ text "gvector" <+> ppe e1 <+> ppe e2
  ppe (GVectRefF e1 e2)           = parens $ text "gvector-ref" <+> ppe e1 <+> ppe e2
  ppe (GVectSetF e1 e2 e3)        = parens $ text "gvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (MVectF e1 e2)              = parens $ text "mvector" <+> ppe e1 <+> ppe e2
  ppe (MVectRefF e1 e2)           = parens $ text "mvector-ref" <+> ppe e1 <+> ppe e2
  ppe (MVectSetF e1 e2 e3)        = parens $ text "mvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (TupleF es)                 = parens $ text "tuple" <+> hsep (map ppe es)
  ppe (TupleProjF e i)            = parens $ text "tuple-proj" <+> ppe e <+> int i
  ppe (LetF bs e)                 = parens $ text "let" <+> parens (vcat' (map ppe bs)) $+$ indent (ppe e)
  ppe (LetrecF bs e)              = parens $ text "letrec" <+> parens (vcat' (map ppe bs)) $+$ indent (ppe e)
  ppe (AsF e t)                   = parens $ ppe e <+> char ':' <+> ppe t
  ppe (BeginF es e)               = parens $ text "begin" $+$ indent (vcat' $ map ppe es) $+$ indent (ppe e)
  ppe (RepeatF x a e1 e2 e b (Ann _ t)) =
    parens $ text "repeat" <+> parens (text x <+> ppe e1 <+> ppe e2)
    <+> parens (case t of
                   BlankTyF -> text a <+> ppe b
                   _       -> text a <+> (char ':' <+> ppe t) <+> ppe b)
    $+$ ppe e
  ppe (TimeF e)                   = parens $ text "time" <+> ppe e
  ppe (PF p)                      = ppe p

instance Pretty Operator where
  ppe Plus        = char '+'
  ppe Minus       = char '-'
  ppe Mult        = char '*'
  ppe Eq          = char '='
  ppe Ge          = text ">="
  ppe Gt          = char '>'
  ppe Le          = text "<="
  ppe Lt          = char '<'
  ppe ShiftR      = text "%>>"
  ppe ShiftL      = text "%<<"
  ppe BAnd        = text "binary-and"
  ppe BOr         = text "binary-or"
  ppe Div         = text "%/"
  ppe PlusF       = text "fl+"
  ppe MinusF      = text "fl-"
  ppe MultF       = text "fl*"
  ppe DivF        = text "fl/"
  ppe ModuloF     = text "flmodulo"
  ppe AbsF        = text "flabs"
  ppe LtF         = text "fl<"
  ppe LeF         = text "fl<="
  ppe EqF         = text "fl="
  ppe GtF         = text "fl>"
  ppe GeF         = text "fl>="
  ppe MinF        = text "flmin"
  ppe MaxF        = text "flmax"
  ppe RoundF      = text "flround"
  ppe FloorF      = text "flfloor"
  ppe CeilingF    = text "flceiling"
  ppe TruncateF   = text "fltruncate"
  ppe SinF        = text "flsin"
  ppe CosF        = text "flcos"
  ppe TanF        = text "fltan"
  ppe AsinF       = text "flasin"
  ppe AcosF       = text "flacos"
  ppe AtanF       = text "flatan"
  ppe LogF        = text "fllog"
  ppe ExpF        = text "flexp"
  ppe SqrtF       = text "flsqrt"
  ppe ExptF       = text "flexpt"
  ppe FloatToInt  = text "float->int"
  ppe IntToFloat  = text "int->float"
  ppe CharToInt   = text "char->int"
  ppe ReadInt     = text "read-int"
  ppe ReadFloat   = text "read-float"
  ppe ReadChar    = text "read-char"
  ppe DisplayChar = text "display-char"

instance Pretty Bool where
  ppe True  = text "#t"
  ppe False = text "#f"

instance Pretty t => Pretty (TypeF t) where
  ppe BlankTyF      = error "blank type should not be prettied"
  ppe DynF          = text "Dyn"
  ppe CharTyF       = text "Char"
  ppe IntTyF        = text "Int"
  ppe FloatTyF      = text "Float"
  ppe BoolTyF       = text "Bool"
  ppe UnitTyF       = text "()"
  ppe (FunTyF ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  ppe (ArrTyF ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  -- ppe (ArrTyF _ _) = error "arrow type should not be prettied"
  ppe (RefTyF t)    = parens $ text "Ref" <+> ppe t
  ppe (GRefTyF t)   = parens $ text "GRef" <+> ppe t
  ppe (MRefTyF t)   = parens $ text "MRef" <+> ppe t
  ppe (VectTyF t)   = parens $ text "Vect" <+> ppe t
  ppe (GVectTyF t)  = parens $ text "GVect" <+> ppe t
  ppe (MVectTyF t)  = parens $ text "MVect" <+> ppe t
  ppe (TupleTyF ts) = parens $ text "Tuple" <+> hsep (map ppe ts)

codeGen :: Pretty p => p -> String
codeGen = render . ppe
