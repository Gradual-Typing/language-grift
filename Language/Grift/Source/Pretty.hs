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
  ppe (Var x) = text x
  ppe (N a)   = integer a
  ppe (F _ s) = text s
  ppe (B b)   = ppe b
  ppe Unit    = text "()"
  ppe (C c)   = text "#\\" <> ppe c

instance Pretty (e (Ann a e)) => Pretty (Ann a e) where
  ppe (Ann _ e) = ppe e

pparg :: Name -> Ann a Type -> Doc
pparg a (Ann _ BlankTy) = ppe a
pparg a t               = lbrack <> ppe a <+> char ':' <+> ppe t <> rbrack

instance (Pretty e, Show a) => Pretty (ExpF (Ann a Type) e) where
  ppe (Op op es)                 = parens $ ppe op <+> hsep (map ppe es)
  ppe (If e1 e2 e3)              = parens $ text "if" <+> ppe e1 $+$ indent (ppe e2) $+$ indent (ppe e3)
  ppe (App e1 es)                = parens $ ppe e1 <+> hsep (map ppe es)
  ppe (TopLevel d es)            = vcat' (map ppe d) $+$ indent (vcat' $ map ppe es)
  ppe (Module name imports exports defs es) = 
    parens (text "module" <+> text name $+$ 
            (parens (text "imports") $+$ vcat' (map ppe imports)) $+$
            (if null exports then empty
             else parens (text "exports") $+$ vcat' (map ppe exports)) $+$
            vcat' (map ppe defs) $+$ indent (vcat' $ map ppe es))
  ppe (Lam xs e (Ann _ (ArrTy ts (Ann _ t))))    =
    parens (text "lambda" <+> parens
            (vcat' (zipWith pparg xs ts)) <+>
            (case t of
               BlankTy -> empty
               _       -> char ':' <+> ppe t)
            $+$ indent (ppe e))
  ppe (Lam _ _ t)                = error ("defined as lambda but has type" ++ show t)
  ppe (DConst x (Ann _ t) e)     = parens $ text "define" <+> text x <+>
    (case t of
        BlankTy -> ppe e
        _       -> char ':' <+> ppe t <+> ppe e)
  ppe (DLam x xs e (Ann _ (ArrTy ts (Ann _ t)))) = parens $ text "define" <+>
    parens (text x <+> vcat' (zipWith pparg xs ts)) <+>
    (case t of
       BlankTy -> empty
       _       -> char ':' <+> ppe t)
    $+$ indent (ppe e)
  ppe (DLam x _ _ (Ann _ t))     = error (x ++ " is defined as lambda but has type: " ++ show t)
  ppe (Bind x (Ann _ BlankTy) e) = brackets (text x $+$ indent (ppe e))
  ppe (Bind x t e)               =
    brackets (text x <+> char ':' <+> ppe t $+$ indent (ppe e))
  ppe (Ref e)                    = parens $ text "box" <+> ppe e
  ppe (DeRef e)                  = parens $ text "unbox" <+> ppe e
  ppe (Assign e1 e2)             = parens $ text "box-set!" <+> ppe e1 <+> ppe e2
  ppe (GRef e)                   = parens $ text "gbox" <+> ppe e
  ppe (GDeRef e)                 = parens $ text "gunbox" <+> ppe e
  ppe (GAssign e1 e2)            = parens $ text "gbox-set!" <+> ppe e1 <+> ppe e2
  ppe (MRef e)                   = parens $ text "mbox" <+> ppe e
  ppe (MDeRef e)                 = parens $ text "munbox" <+> ppe e
  ppe (MAssign e1 e2)            = parens $ text "mbox-set!" <+> ppe e1 <+> ppe e2
  ppe (Vect e1 e2)               = parens $ text "vector" <+> ppe e1 <+> ppe e2
  ppe (VectRef e1 e2)            = parens $ text "vector-ref" <+> ppe e1 <+> ppe e2
  ppe (VectSet e1 e2 e3)         = parens $ text "vector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (GVect e1 e2)              = parens $ text "gvector" <+> ppe e1 <+> ppe e2
  ppe (GVectRef e1 e2)           = parens $ text "gvector-ref" <+> ppe e1 <+> ppe e2
  ppe (GVectSet e1 e2 e3)        = parens $ text "gvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (MVect e1 e2)              = parens $ text "mvector" <+> ppe e1 <+> ppe e2
  ppe (MVectRef e1 e2)           = parens $ text "mvector-ref" <+> ppe e1 <+> ppe e2
  ppe (MVectSet e1 e2 e3)        = parens $ text "mvector-set!" <+> ppe e1 <+> ppe e2 <+> ppe e3
  ppe (Tuple es)                 = parens $ text "tuple" <+> hsep (map ppe es)
  ppe (TupleProj e i)            = parens $ text "tuple-proj" <+> ppe e <+> int i
  ppe (Let bs e)                 = parens $ text "let" <+> parens (vcat' (map ppe bs)) $+$ indent (ppe e)
  ppe (Letrec bs e)              = parens $ text "letrec" <+> parens (vcat' (map ppe bs)) $+$ indent (ppe e)
  ppe (As e t)                   = parens $ char ':' <+> ppe e <+> ppe t
  ppe (Begin es e)               = parens $ text "begin" $+$ indent (vcat' $ map ppe es) $+$ indent (ppe e)
  ppe (Repeat x a e1 e2 e b (Ann _ t)) =
    parens $ text "repeat" <+> parens (text x <+> ppe e1 <+> ppe e2)
    <+> parens (case t of
                   BlankTy -> text a <+> ppe b
                   _       -> text a <+> (char ':' <+> ppe t) <+> ppe b)
    $+$ ppe e
  ppe (Time e)                   = parens $ text "time" <+> ppe e
  ppe (P p)                      = ppe p

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

instance Pretty t => Pretty (Type t) where
  ppe BlankTy      = error "blank type should not be prettied"
  ppe Dyn          = text "Dyn"
  ppe CharTy       = text "Char"
  ppe IntTy        = text "Int"
  ppe FloatTy      = text "Float"
  ppe BoolTy       = text "Bool"
  ppe UnitTy       = text "()"
  ppe (FunTy ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  ppe (ArrTy ts t) = parens $ hsep (map ppe ts) <> text " -> " <> ppe t
  -- ppe (ArrTy _ _) = error "arrow type should not be prettied"
  ppe (RefTy t)    = parens $ text "Ref" <+> ppe t
  ppe (GRefTy t)   = parens $ text "GRef" <+> ppe t
  ppe (MRefTy t)   = parens $ text "MRef" <+> ppe t
  ppe (VectTy t)   = parens $ text "Vect" <+> ppe t
  ppe (GVectTy t)  = parens $ text "GVect" <+> ppe t
  ppe (MVectTy t)  = parens $ text "MVect" <+> ppe t
  ppe (TupleTy ts) = parens $ text "Tuple" <+> hsep (map ppe ts)
  ppe (VarTy x)    = text x
  ppe (RecTy x t)  = parens $ text "Rec" <+> text x <+> ppe t

codeGen :: Pretty p => p -> String
codeGen = render . ppe
