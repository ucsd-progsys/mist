{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE FlexibleContexts      #-}

module Language.Mist.Parser ( parse, parseFile ) where

import qualified Text.Printf as Printf 
import qualified Control.Exception          as Ex 
import           Control.Monad (void)
import           Text.Megaparsec hiding (parse)
import           Data.List.NonEmpty         as NE
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Char
import           Text.Megaparsec.Expr
import qualified Data.List as L
import           Language.Mist.Types

--------------------------------------------------------------------------------
parse :: FilePath -> Text -> IO Bare
--------------------------------------------------------------------------------
parse = parseWith (topExprs <* eof)

parseWith  :: Parser a -> FilePath -> Text -> IO a
parseWith p f s = case runParser (whole p) f s of
                    Left err -> Ex.throw [parseUserError err]
                    Right e  -> return e

parseUserError :: ParseError Char SourcePos -> UserError 
parseUserError err = mkError msg sp 
  where 
    msg            = "parse error\n" ++ parseErrorTextPretty err 
    sp             = posSpan . NE.head . errorPos $ err

instance ShowErrorComponent SourcePos where
  showErrorComponent = sourcePosPretty 

-- instance Located ParseError where
--  sourceSpan = posSpan . errorPos

-- instance PPrint ParseError where
--   pprint = show

--------------------------------------------------------------------------------
parseFile :: FilePath -> IO Bare
--------------------------------------------------------------------------------
parseFile f = parse f =<< readFile f

type Parser = Parsec SourcePos Text

-- https://mrkkrp.github.io/megaparsec/tutorials/parsing-simple-imperative-language.html

-- | Top-level parsers (should consume all input)
whole :: Parser a -> Parser a
whole p = sc *> p <* eof

-- RJ: rename me "space consumer"
sc :: Parser ()
sc = L.space (void spaceChar) lineComment blockCmnt
  where 
    blockCmnt = L.skipBlockComment "{-" "-}"

lineComment :: Parser ()
lineComment = L.skipLineComment "--"

-- | `symbol s` parses just the string s (and trailing whitespace)
symbol :: String -> Parser String
symbol = L.symbol sc

comma :: Parser String
comma = symbol ","

dcolon :: Parser String
dcolon = symbol "::"

colon :: Parser String
colon = symbol ":"

-- | 'parens' parses something between parenthesis.
parens :: Parser a -> Parser a
parens = betweenS "(" ")"

-- | 'brackets' parses something between parenthesis.
brackets :: Parser a -> Parser a
brackets = betweenS "[" "]"

betweenS :: String -> String -> Parser a -> Parser a
betweenS l r = between (symbol l) (symbol r)

-- | `lexeme p` consume whitespace after running p
lexeme :: Parser a -> Parser (a, SourceSpan)
lexeme p = L.lexeme sc (withSpan p)

-- | 'integer' parses an integer.
integer :: Parser (Integer, SourceSpan)
integer = lexeme L.decimal


-- | `rWord`
rWord   :: String -> Parser SourceSpan
rWord w = snd <$> (withSpan (string w) <* notFollowedBy alphaNumChar <* sc)


-- | list of reserved words
keywords :: [Text]
keywords =
  [ "if"      , "else"
  , "true"    , "false"
  , "let"     , "in"
  -- , "add1"    , "sub1"  , "isNum"   , "isBool",   "print"
  -- , "def"     , "lambda"
  , "Int"     , "Bool"  , "forall"  , "as"
  ]

-- | `identifier` parses identifiers: lower-case alphabets followed by alphas or digits
identifier :: Parser (String, SourceSpan)
identifier = identStart lowerChar

identStart:: Parser Char -> Parser (String, SourceSpan)
identStart start = lexeme (p >>= check)
  where
    p       = (:) <$> start <*> many alphaNumChar
    check x = if x `elem` keywords
                then fail $ "keyword " ++ show x ++ " cannot be an identifier"
                else return x

-- | `binder` parses BareBind, used for let-binds and function parameters.
binder :: Parser BareBind
binder = uncurry Bind <$> identifier


stretch :: (Monoid a) => [Expr a] -> a
stretch = mconcat . fmap extract

withSpan' :: Parser (SourceSpan -> a) -> Parser a
withSpan' p = do
  p1 <- getPosition
  f  <- p
  p2 <- getPosition
  return (f (SS p1 p2))

withSpan :: Parser a -> Parser (a, SourceSpan)
withSpan p = do
  p1 <- getPosition
  x  <- p
  p2 <- getPosition
  return (x, SS p1 p2)

topExprs :: Parser Bare 
topExprs = defsExpr <$> topDefs 

topDefs :: Parser [BareDef] 
topDefs = many topDef 

topDef :: Parser BareDef 
topDef = do 
  f  <- binder 
  s  <- typeSig
  f' <- binder <* symbol "="
  e  <- expr 
  return (f, s, e) -- (mkDef f s f' [e]) 
 
{- 
topDef :: Parser BareDef 
topDef = L.nonIndented scn (L.indentBlock scn p) 
  where 
    p = do 
      f  <- binder 
      s  <- typeSig
      f' <- binder <* symbol "="
      return (L.IndentMany Nothing (mkDef f s f') expr)
    
-}      

mkDef f s f' es 
  | okBind    = case es of 
                  [e] -> return (f, s, e)
                  es  -> fail $ Printf.printf "Invalid body with multiple expressions %s for %s " 
                                  (pprintMany es) (pprint f) --show (bindId f)
  | otherwise = fail $ "Definition for " ++ show f ++ " must follow its type signature."
  where 
    okBind    = bindId f == bindId f' 


{- 
defExpr :: Parser Bare
defExpr = withSpan' $ do
  rWord "def"
  f  <- binder
  xs <- parens (sepBy binder comma)
  t  <- typeSig <* colon
  e1 <- expr
  rWord "in"
  e2 <- expr
  return (dec f t xs e1 e2)
-}


expr :: Parser Bare
expr = makeExprParser expr0 binops

expr0 :: Parser Bare
expr0 =  try letExpr
     <|> try ifExpr
     <|> try lamExpr
     -- <|> try defExpr
    -- <|> try getExpr
     <|> try constExpr
    -- <|> try tupExpr
     <|> try idExpr
     <|> try (mkApps <$> parens (sepBy1 expr sc)) 

exprs :: Parser [Bare]
exprs = parens (sepBy expr comma)

getExpr :: Parser Bare
getExpr = withSpan' (GetItem <$> funExpr <*> brackets field)
  where
  field =  (symbol "0" *> pure Zero)
       <|> (symbol "1" *> pure One)

-- appExpr :: Parser Bare
-- appExpr  = apps <$> funExpr <*> sepBy exprs sc

mkApps :: [Bare] -> Bare
mkApps = L.foldl1' (\e1 e2 -> App e1 e2 (stretch [e1, e2])) 


funExpr :: Parser Bare
funExpr = try idExpr <|> tupExpr

tupExpr :: Parser Bare
tupExpr = withSpan' (mkTuple <$> exprs)

mkTuple :: [Bare] -> SourceSpan -> Bare
mkTuple [e] _      = e
mkTuple [e1, e2] l = Tuple e1 e2 l
mkTuple _  l       = panic "Mist only supports pairs!" l

binops :: [[Operator Parser Bare]]
binops =
  [ [ InfixL (symbol "*"  *> pure (op Times))
    ]
  , [ InfixL (symbol "+"  *> pure (op Plus))
    , InfixL (symbol "-"  *> pure (op Minus))
    ]
  , [ InfixL (symbol "==" *> pure (op Equal))
    , InfixL (symbol ">"  *> pure (op Greater))
    , InfixL (symbol "<"  *> pure (op Less))
    ]
  ]
  where
    op o e1 e2 = Prim2 o e1 e2 (stretch [e1, e2])

idExpr :: Parser Bare
idExpr = uncurry Id <$> identifier

constExpr :: Parser Bare
constExpr
   =  (uncurry Number <$> integer)
  <|> (Boolean True   <$> rWord "True")
  <|> (Boolean False  <$> rWord "False")

letExpr :: Parser Bare
letExpr = withSpan' $ do
  rWord "let"
  bs <- sepBy1 bind comma
  rWord "in"
  e  <- expr
  return (bindsExpr bs e)

bind :: Parser (BareBind, Bare)
bind = (,) <$> binder <* symbol "=" <*> expr

ifExpr :: Parser Bare
ifExpr = withSpan' $ do
  rWord "if"
  b  <- expr
  e1 <- between (rWord "then") (rWord "else") expr
  e2 <- expr
  return (If b e1 e2)

lamExpr :: Parser Bare
lamExpr = withSpan' $ do
  -- rWord "lambda"
  char '\\' <* sc
  -- xs    <- parens (sepBy binder comma) <* symbol "->" 
  xs    <- sepBy binder sc <* symbol "->" 
  e     <- expr
  return (Lam xs e)


typeSig :: Parser Sig
typeSig
  =   try (Assume <$> (rWord "as" *> scheme))
  <|> try (Check  <$> (dcolon     *> scheme))
  <|> pure Infer

scheme :: Parser Poly
scheme
  =  try (Forall    <$> (rWord "forall" *> sepBy tvar comma <* symbol ".") <*> typeType)
 <|>     (Forall [] <$> typeType)

typeType :: Parser Type
typeType = mkArrow <$> sepBy1 baseType (symbol "->")

--  <|> try ((:=>) <$> types <* symbol "->" <*> typeType)

baseType :: Parser Type 
baseType 
  =  try (rWord "Int"   *> pure TInt)
 <|> try (rWord "Bool"  *> pure TBool)
 <|> try (TVar <$> tvar)
 <|> try (withSpan' (mkPairType <$> types))
 <|> ctorType


mkArrow :: [Type] -> Type 
mkArrow ts = case L.reverse ts of 
               [t]   -> t
               t:ts' -> L.reverse ts' :=> t 
               _     -> error "impossible: mkArrow"

tvar :: Parser TVar
tvar = TV . fst <$> identifier

types :: Parser [Type]
types = parens (sepBy1 typeType comma)

ctorType :: Parser Type
ctorType = TCtor <$> ctor <*> brackets (sepBy typeType comma)

ctor :: Parser Ctor
ctor = CT . fst <$> identStart upperChar

mkPairType :: [Type] -> SourceSpan -> Type
mkPairType [t]      _ = t
mkPairType [t1, t2] _ = TPair t1 t2
mkPairType _        l = panic "Mist only supports pairs types" l
