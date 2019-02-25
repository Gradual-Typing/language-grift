{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# OPTIONS_GHC -fno-warn-unused-do-bind #-}

module Language.Grift.Source.Parser (parser) where

import           Control.Arrow as Arrow                     (left)
import           Control.Monad                              (void)
import           Control.Monad.Reader
import           Data.List                                  (elemIndex)
import           Text.Parsec

import           Language.Grift.Source.Parser.WithSourcePos
import           Language.Grift.Source.Syntax

--type Parser = ParsecT String () Identity
type Parser = ParsecT String () (Reader [String])

-- | Bind a name over an expression
bind :: [String] -> Parser a -> Parser a
bind bound_vars thing_inside = local (bound_vars ++) thing_inside

-- sorted
reservedNames :: [String]
reservedNames =
  ["%/","%<<","%>>","*","+","-",":","<","<=",
   "=",">",">=","binary-and","binary-or","gbox",
   "gbox-set!","gunbox","gvector","gvector-ref",
   "gvector-set!","if","lambda","let","letrec",
   "mbox","mbox-set!","munbox","mvector",
   "mvector-ref","mvector-set!","box",
   "box-set!","unbox","vector","vector-ref",
   "vector-set!","repeat","time",
   "read-int"]

-- Utilities

isReservedName :: String -> Bool
isReservedName = isReserved reservedNames

isReserved :: Ord a => [a] -> a -> Bool
isReserved names name
  = scan names
  where
    scan []       = False
    scan (r:rs)   = case compare r name of
                     LT -> scan rs
                     EQ -> True
                     GT -> False

-- Expression Parsers

annotate :: Monad m =>
            ParsecT s u m (e (Ann SourcePos e))
            -> ParsecT s u m (Ann SourcePos e)
annotate a = Ann <$> getPosition <*> a

whitespace :: Parser ()
whitespace =
    choice [simpleWhitespace *> whitespace,lineComment *> whitespace,return ()]
  where
    lineComment = try (string ";;") *>
                  manyTill anyChar (void (char '\n') <|> eof)
    simpleWhitespace = void $ many1 (oneOf " \t\n")

integer :: Parser Integer
integer =  fmap read integer1

-- (<++>) :: Applicative f => f [a] -> f [a] -> f [a]
-- (<++>) a b = (++) <$> a <*> b

(<:>) :: Applicative f => f a -> f [a] -> f [a]
(<:>) a b = (:) <$> a <*> b

number,plus,minus,integer1 :: Parser String

number = many1 digit

plus = char '+' *> number

minus = char '-' <:> number

integer1 = plus <|> minus <|> number

opnParser :: Int -> String -> Operator -> Parser L1
opnParser n s op = do
  src <- getPosition
  try (string ('(':s))
  whitespace
  es <- count n (expParser <* whitespace)
  char ')'
  return $ Ann src $ OpF op es

c1Parser :: String -> (L1 -> ExpF1 (Ann SourcePos ExpF1)) -> Parser L1
c1Parser s op = do
  src <- getPosition
  try (string ('(':s))
  e <- expParser
  char ')'
  return $ Ann src $ op e

c2Parser :: String -> (L1 -> L1 -> ExpF1 (Ann SourcePos ExpF1)) -> Parser L1
c2Parser s op = do
  src <- getPosition
  try (string ('(':s))
  e1 <- expParser
  whitespace
  e2 <- expParser
  char ')'
  return $ Ann src $ op e1 e2

c3Parser :: String -> (L1 -> L1 -> L1 -> ExpF1 (Ann SourcePos ExpF1)) -> Parser L1
c3Parser s op = do
  src <- getPosition
  try (string ('(':s))
  e1 <- expParser
  whitespace
  e2 <- expParser
  whitespace
  e3 <- expParser
  char ')'
  return $ Ann src $ op e1 e2 e3

specialChar :: Parser Char
specialChar = fstSpecChar -- <|> oneOf "!"

fstSpecChar :: Parser Char
fstSpecChar = oneOf "_#%*+-!^"

idParser :: Parser String
idParser = do
  name <- (:) <$> (letter <|> specialChar) <*> many (alphaNum <|> specialChar)
  if isReservedName name
    then unexpected ("reserved word " ++ show name)
    else return name

argParser :: Parser (Name,TypeWithLoc)
argParser =
  (,) <$ char '[' <*> idParser <* string " : " <*> typeParser <* char ']'
  <|> (,) <$> idParser <*> annotate (return BlankTyF)

ifParser,varParser,appParser,opsParser,intParser,boolParser
  ,lambdaParser,letParser,letrecParser,refParser,derefParser
  ,refsetParser,grefParser,gderefParser,grefsetParser,mrefParser,
   mderefParser,mrefsetParser,vectParser,vectrefParser,
   vectsetParser,gvectParser,gvectrefParser,
   gvectsetParser,mvectParser,mvectrefParser,mvectsetParser,asParser,
   beginParser,repeatParser,unitParser,timeParser,topLevParser,
   floatParser,charParser,tupleParser,tupleProjParser, dconstParser,
   dlamParser,bindParser :: Parser L1

bindParser = do
  src <- getPosition
  c <- char '[' <|> char '('
  x <- idParser
  whitespace
  tsrc <- getPosition
  t <- option (Ann tsrc BlankTyF) (id <$ char ':' <* whitespace <*> typeParser <* whitespace)
  e <- expParser
  if c == '[' then char ']' else char ')'
  return $ Ann src $ BindF x t e

unitParser = Ann <$> getPosition <*> (PF Unit <$ try (string "()"))

floatParser = do
  i <- option "" (string "#i")
  int <- integer1
  dec <- decimal
  ex  <- expon
  let s = int ++ dec ++ ex
  annotate $ return $ PF $ F (rd s) (i ++ s)
    where rd       = read :: String -> Double
          decimal  = option "" $ char '.' <:> number
          expon = option "" $ oneOf "eE" <:> integer1

ifParser = do
  src <- getPosition
  try (string "(if ")
  e1 <- expParser
  whitespace
  e2 <- expParser
  whitespace
  e3 <- expParser
  char ')'
  return $ Ann src $ IfF e1 e2 e3

varParser = do
  src <- getPosition
  x <- idParser
  m_i <- asks $ elemIndex x
  return $ Ann src $ PF $ case m_i of
    Nothing -> Global x
    Just i  -> Var x i

appParser = do
  src <- getPosition
  char '('
  e <- expParser
  whitespace
  es <- sepEndBy expParser whitespace
  char ')'
  return $ Ann src $ AppF e es

tupleParser = do
  src <- getPosition
  try (string "(tuple ")
  whitespace
  es <- sepEndBy expParser whitespace
  char ')'
  return $ Ann src $ TupleF es

tupleProjParser = do
  src <- getPosition
  try (string "(tuple-proj ")
  whitespace
  e <- expParser
  whitespace
  i <- integer
  char ')'
  return $ Ann src $ TupleProjF e $ fromIntegral i

op0Parser,op1Parser,op2Parser :: String -> Operator -> Parser L1
op0Parser = opnParser 0
op1Parser = opnParser 1
op2Parser = opnParser 2

opsParser = op2Parser "+ " Plus
            <|> op2Parser "- " Minus
            <|> op2Parser "* " Mult
            <|> op2Parser "%/ " Div
            <|> op2Parser "= " Eq
            <|> op2Parser ">= " Ge
            <|> op2Parser "> " Gt
            <|> op2Parser "<= " Le
            <|> op2Parser "< " Lt
            <|> op2Parser "%>> " ShiftR
            <|> op2Parser "%<< " ShiftL
            <|> op2Parser "binary-and " BAnd
            <|> op2Parser "binary-or " BOr
            <|> op2Parser "fl+ " PlusF
            <|> op2Parser "fl- " MinusF
            <|> op2Parser "fl* " MultF
            <|> op2Parser "fl/ " DivF
            <|> op1Parser "flmodulo " ModuloF
            <|> op1Parser "flabs " AbsF
            <|> op2Parser "fl< " LtF
            <|> op2Parser "fl<= " LeF
            <|> op2Parser "fl= " EqF
            <|> op2Parser "fl> " GtF
            <|> op2Parser "fl>= " GeF
            <|> op2Parser "flmin " MinF
            <|> op2Parser "flmax " MaxF
            <|> op1Parser "flfloor " RoundF
            <|> op1Parser "flround " FloorF
            <|> op1Parser "flceiling " CeilingF
            <|> op1Parser "fltruncate " TruncateF
            <|> op1Parser "flsin " SinF
            <|> op1Parser "flcos " CosF
            <|> op1Parser "fltan " TanF
            <|> op1Parser "flasin " AsinF
            <|> op1Parser "flacos " AcosF
            <|> op1Parser "flatan " AtanF
            <|> op1Parser "fllog " LogF
            <|> op1Parser "flexp " ExpF
            <|> op1Parser "flsqrt " SqrtF
            <|> op2Parser "flexpt " ExptF
            <|> op1Parser "float->int " FloatToInt
            <|> op1Parser "int->float " IntToFloat
            <|> op1Parser "char->int " CharToInt
            <|> op0Parser "read-int" ReadInt
            <|> op0Parser "read-float" ReadFloat
            <|> op0Parser "read-char" ReadChar
            <|> op1Parser "display-char" DisplayChar

intParser = annotate $ (PF . N) <$> try integer

boolParser = annotate $ (\x -> (PF . B) $ x == 't') <$ char '#' <*> (char 't' <|> char 'f')

charParser = annotate $ (PF . C) <$ string "#\\" <*> (try (string "newline") <|> try (string "space") <|> try ((: []) <$> anyChar))

lambdaParser = do
  src <- getPosition
  try (string "(lambda (")
  args <- sepEndBy argParser whitespace
  char ')'
  whitespace
  tsrc <- getPosition
  rt <- option (Ann tsrc BlankTyF) (id <$ char ':' <* whitespace <*> typeParser <* whitespace)
  b <- bind (mapM fst args) expParser
  char ')'
  return $ Ann src $ LamF (map fst args) b $ Ann src $ ArrTyF (map snd args) rt

letParser = do
  src <- getPosition
  try (string "(let")
  whitespace
  char '('
  binds <- sepEndBy bindParser whitespace
  char ')'
  whitespace
  e <- expParser
  char ')'
  return $ Ann src $ LetF binds e

letrecParser = do
  src <- getPosition
  try (string "(letrec")
  whitespace
  char '('
  binds <- sepEndBy bindParser whitespace
  char ')'
  whitespace
  e <- expParser
  char ')'
  return $ Ann src $ LetrecF binds e

timeParser = c1Parser "time " TimeF
refParser = c1Parser "box " RefF
derefParser = c1Parser "unbox " DeRefF
refsetParser = c2Parser "box-set! " AssignF
grefParser = c1Parser "gbox " GRefF
gderefParser = c1Parser "gunbox " GDeRefF
grefsetParser = c2Parser "gbox-set! " GAssignF
mrefParser = c1Parser "mbox " MRefF
mderefParser = c1Parser "munbox " MDeRefF
mrefsetParser = c2Parser "mbox-set! " MAssignF
vectParser = c2Parser "vector " VectF
vectrefParser = c2Parser "vector-ref " VectRefF
vectsetParser = c3Parser "vector-set! " VectSetF
gvectParser = c2Parser "gvector " GVectF
gvectrefParser = c2Parser "gvector-ref " GVectRefF
gvectsetParser = c3Parser "gvector-set! " GVectSetF
mvectParser = c2Parser "mvector " MVectF
mvectrefParser = c2Parser "mvector-ref " MVectRefF
mvectsetParser = c3Parser "mvector-set! " MVectSetF

asParser = do
  src <- getPosition
  try (string "(: ")
  e <- expParser
  space
  t <- typeParser
  char ')'
  return $ Ann src $ AsF e t

dconstParser = do
  src <- getPosition
  try $ do string "(define"
           whitespace
  x <- idParser
  whitespace
  tsrc <- getPosition
  t <- option (Ann tsrc BlankTyF) (string ": " *> typeParser <* whitespace)
  e <- expParser
  char ')'
  return $ Ann src $ DConstF x t e

dlamParser = do
  src <- getPosition
  try $ do string "(define"
           whitespace
           char '('
  x <- idParser
  whitespace
  args <- sepEndBy argParser whitespace
  char ')'
  whitespace
  tsrc <- getPosition
  rt <- option (Ann tsrc BlankTyF) (id <$ char ':' <* whitespace <*> typeParser)
  whitespace
  b <- expParser
  whitespace
  char ')'
  return $ Ann src $ DLamF x (map fst args) b $ Ann src $ ArrTyF (map snd args) rt

beginParser = do
  src <- getPosition
  try (string "(begin")
  whitespace
  es <- sepEndBy1 expParser whitespace
  char ')'
  return $ Ann src $ BeginF (init es) $ last es

repeatParser = do
  src <- getPosition
  try (string "(repeat")
  whitespace
  char '('
  x <- idParser
  whitespace
  start <- expParser
  whitespace
  end <- expParser
  char ')'
  whitespace
  char '('
  acci <- idParser
  whitespace
  tsrc <- getPosition
  acct <- option (Ann tsrc BlankTyF) (id <$ char ':' <* whitespace <*> typeParser <* whitespace)
  acce <- expParser
  char ')'
  whitespace
  b <- expParser
  char ')'
  return $ Ann src $ RepeatF x acci start end b acce acct

topLevParser = do
  src <- getPosition
  ds <- sepEndBy (dlamParser <|> dconstParser) whitespace
  es <- sepEndBy expParser whitespace
  return $ Ann src $ TopLevelF ds es

expParser :: Parser L1
expParser = try floatParser
            <|> intParser
            <|> try boolParser
            <|> try charParser
            <|> unitParser
            <|> try varParser
            <|> opsParser
            <|> ifParser
            <|> lambdaParser
            <|> refParser
            <|> derefParser
            <|> refsetParser
            <|> grefParser
            <|> gderefParser
            <|> grefsetParser
            <|> mrefParser
            <|> mderefParser
            <|> mrefsetParser
            <|> vectParser
            <|> vectrefParser
            <|> vectsetParser
            <|> gvectParser
            <|> gvectrefParser
            <|> gvectsetParser
            <|> mvectParser
            <|> mvectrefParser
            <|> mvectsetParser
            <|> tupleProjParser
            <|> tupleParser
            <|> timeParser
            <|> letrecParser
            <|> letParser
            <|> asParser
            <|> beginParser
            <|> repeatParser
            <|> try appParser

-- Type Parsers

refTyParser,vectTyParser,grefTyParser,mrefTyParser,gvectTyParser
  ,mvectTyParser,intTyParser,boolTyParser,dynTyParser,unitTyParser
  ,funTyParser,floatTyParser,charTyParser,tupleTyParser,typeParser
   :: Parser TypeWithLoc

charTyParser   = annotate $ CharTyF <$ try (string "Char")
intTyParser    = annotate $ IntTyF <$ try (string "Int")
floatTyParser  = annotate $ FloatTyF <$ try (string "Float")
boolTyParser   = annotate $ BoolTyF <$ try (string "Bool")
dynTyParser    = annotate $ DynF <$ try (string "Dyn")
unitTyParser   = annotate $ UnitTyF <$ try (string "()" <|> string "Unit")
funTyParser    = do
  src <- getPosition
  char '('
  ts <- sepEndBy typeParser whitespace
  string "-> "
  rt <- typeParser
  char ')'
  return $ Ann src $ FunTyF ts rt

tupleTyParser = do
  src <- getPosition
  string "(Tuple "
  ts <- sepEndBy typeParser whitespace
  char ')'
  return $ Ann src $ TupleTyF ts

refTyParser   = annotate $ RefTyF <$ try (string "(Ref ") <*> typeParser <* char ')'
vectTyParser  = annotate $ VectTyF <$ try (string "(Vect ") <*> typeParser <* char ')'
grefTyParser  = annotate $ GRefTyF <$ try (string "(GRef ") <*> typeParser <* char ')'
mrefTyParser  = annotate $ MRefTyF <$ try (string "(MRef ") <*> typeParser <* char ')'
gvectTyParser = annotate $ GVectTyF <$ try (string "(GVect ") <*> typeParser <* char ')'
mvectTyParser = annotate $ MVectTyF <$ try (string "(MVect ") <*> typeParser <* char ')'

typeParser = charTyParser
             <|> intTyParser
             <|> floatTyParser
             <|> boolTyParser
             <|> dynTyParser
             <|> unitTyParser
             <|> try funTyParser
             <|> refTyParser
             <|> vectTyParser
             <|> grefTyParser
             <|> mrefTyParser
             <|> gvectTyParser
             <|> mvectTyParser
             <|> tupleTyParser

schmlParser :: Parser L1
schmlParser = id <$ whitespace <*> topLevParser <* whitespace <* eof

parser :: String -> Either String L1
parser input = Arrow.left show $ runReader (runParserT schmlParser () "" input) []

-- main :: IO ()
-- main = parseTest schmlParser "(letrec ([x : (Int Int -> Int) (lambda ([x : Int] [y : Int]) : Int (* x (: -2 Int)))] [y : Bool #f]) (let ([z : Int 5] [t : () ()]) (if (> 3 1) (x z) 0)))"
