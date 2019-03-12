{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE FlexibleContexts      #-}

module Language.Mist.Parser
  (
    parse
  , parseFile
  , BareExpr
  , BareRefinement
  ) where

import qualified Control.Exception          as Ex
import           Control.Monad (void)
import           Control.Monad.State.Strict
import           Text.Megaparsec hiding (parse, State)
import           Data.List.NonEmpty         as NE
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Char
import           Text.Megaparsec.Expr
import qualified Data.List as L
import           Language.Mist.Types


-- TODO: use Fixpoint Expr parser for refinements


-- | parsed syntax elements with parsed expressions as the refinement
-- | Top level expressions
type Bare t = Expr t SourceSpan
type BareRefinement = Bare ()
type BareExpr = Bare (ParsedType BareRefinement SourceSpan)
type BareDef = ParsedDef BareRefinement SourceSpan
type BareType = ParsedType BareRefinement SourceSpan
type BareRType = RType BareRefinement SourceSpan
type BareBind = Bind SourceSpan

instance Unannotated () where
  missingAnnotation = ()

--------------------------------------------------------------------------------
parse :: FilePath -> Text -> IO BareExpr
--------------------------------------------------------------------------------
parse = parseWith (topExprs <* eof)

parseWith  :: Parser a -> FilePath -> Text -> IO a
parseWith p f s = case flip evalState 0 $ runParserT (whole p) f s of
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
parseFile :: FilePath -> IO BareExpr
--------------------------------------------------------------------------------
parseFile f = parse f =<< readFile f

type Parser = ParsecT SourcePos Text (State Integer)

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

suchthat :: Parser String
suchthat = symbol "|"

-- | 'parens' parses something between parenthesis.
parens :: Parser a -> Parser a
parens = betweenS "(" ")"

-- | 'brackets' parses something between square brackets
brackets :: Parser a -> Parser a
brackets = betweenS "[" "]"

-- | 'braces' parses something between braces
braces :: Parser a -> Parser a
braces = betweenS "{" "}"

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

-- | `binder` parses BareAnnBind, used for let-binds and function parameters.
binder :: Parser BareBind
binder = uncurry Bind <$> identifier

freshBinder :: Parser BareBind
freshBinder = uncurry Bind <$> (lexeme $ ("fresh" ++) . show <$> lift get)

stretch :: (Monoid a) => [Expr t a] -> a
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

topExprs :: Parser BareExpr
topExprs = defsExpr <$> topDefs

topDefs :: Parser [BareDef]
topDefs = many topDef

topDef :: Parser BareDef
topDef = do
  f  <- binder
  ann <- typeSig
  _f' <- binder <* symbol "="
  e <- expr
  return (annotateBinding f ann, e)

expr :: (Unannotated a) => Parser (Bare a)
expr = makeExprParser expr0 binops

expr0 :: (Unannotated a) => Parser (Bare a)
expr0 =  try letExpr
     <|> try ifExpr
     <|> try lamExpr
     <|> try constExpr
     <|> try idExpr
     <|> try (mkApps <$> parens (sepBy1 expr sc))

mkApps :: (Unannotated a) => [(Bare a)] -> (Bare a)
mkApps = L.foldl1' (\e1 e2 -> App e1 e2 (stretch [e1, e2]))

binops :: (Unannotated a) => [[Operator Parser (Bare a)]]
binops =
  [ [ InfixL (symbol "*"  *> pure (op Times))
    ]
  , [ InfixL (symbol "+"  *> pure (op Plus))
    , InfixL (symbol "-"  *> pure (op Minus))
    ]
  , [ InfixL (symbol "==" *> pure (op Equal))
    , InfixL (symbol ">"  *> pure (op Greater))
    , InfixL (symbol "<=" *> pure (op Lte))
    , InfixL (symbol "<"  *> pure (op Less))
    ]
  ]
  where
    op o e1 e2 = Prim2 o e1 e2 (stretch [e1, e2])

idExpr :: (Unannotated a) => Parser (Bare a)
idExpr = uncurry Id <$> identifier

constExpr :: (Unannotated a) => Parser (Bare a)
constExpr
   =  (uncurry Number <$> integer)
  <|> (Boolean True   <$> rWord "True")
  <|> (Boolean False  <$> rWord "False")

letExpr :: (Unannotated a) => Parser (Bare a)
letExpr = withSpan' $ do
  rWord "let"
  bs <- sepBy1 bind comma
  rWord "in"
  e  <- expr
  return (bindsExpr bs e)

bind :: (Unannotated a) => Parser (BareBind, (Bare a))
bind = (,) <$> binder <* symbol "=" <*> expr

ifExpr :: (Unannotated a) => Parser (Bare a)
ifExpr = withSpan' $ do
  rWord "if"
  b  <- expr
  e1 <- between (rWord "then") (rWord "else") expr
  e2 <- expr
  return (If b e1 e2)

lamExpr :: (Unannotated a) => Parser (Bare a)
lamExpr = withSpan' $ do
  -- rWord "lambda"
  char '\\' <* sc
  -- xs    <- parens (sepBy binder comma) <* symbol "->"
  xs    <- sepBy binder sc <* symbol "->"
  e     <- expr
  return (\span -> (foldr (\x e -> Lam (annotateBinding x missingAnnotation) e span) e xs))

typeSig :: Parser BareType
typeSig
  =   try (ParsedAssume <$> (rWord "as" *> scheme))
  <|> try (ParsedCheck <$> (dcolon *> scheme))
  <|> pure ParsedInfer

scheme :: Parser BareRType
scheme
  =  try schemeForall
 <|>     typeRType

schemeForall :: Parser BareRType
schemeForall = do
  tvars <- rWord "forall" *> sepBy tvar comma <* symbol "."
  bodyType <- typeRType
  pure $ foldr (\tvar t -> RForall tvar t) bodyType tvars

typeType :: Parser Type
typeType = mkArrow <$> sepBy1 baseType (symbol "->")

{- | [NOTE:RTYPE-PARSE] Fundamentally, a type is of the form

      comp -> comp -> ... -> comp

So

  rt = comp
     | comp '->' rt

  comp = circle
       | '(' rt ')'

  circle = { v : t | r }
         | t

Each 'comp' should have a variable to refer to it,
either a parser-assigned one or given explicitly. e.g.

  xs : [Int]

-}

typeRType :: Parser BareRType
typeRType = try rfun <|> try rifun <|> unrefined <|> rbase

rifun :: Parser BareRType
rifun = do id <- (binder <* colon) <|> freshBinder
           tin <- (unrefined <|> rbase <|> parens typeRType) <* (symbol "~>")
           RIFun id tin <$> typeRType

rfun :: Parser BareRType
rfun = do id <- (binder <* colon) <|> freshBinder
          tin <- (unrefined <|> rbase <|> parens typeRType) <* (symbol "->")
          RFun id tin <$> typeRType

unrefined :: Parser BareRType
unrefined = RBase <$> freshBinder <*> baseType <*> pure (Boolean True mempty)

rbase :: Parser BareRType
rbase = braces $ RBase
    <$> binder <* colon
    <*> baseType <* suchthat
    <*> expr

baseType :: Parser Type
baseType
  =  try (rWord "Int"   *> pure TInt)
 <|> try (rWord "Bool"  *> pure TBool)
 <|> try (TVar <$> tvar)
 -- <|> try (withSpan' (mkPairType <$> types))
 <|> ctorType

mkArrow :: [Type] -> Type
mkArrow [t] = t
mkArrow ts@(_:_) = foldr (:=>) t ts'
  where t:ts' = L.reverse ts
mkArrow _  = error "impossible: mkArrow"

tvar :: Parser TVar
tvar = TV . fst <$> identifier

_types :: Parser [Type]
_types = parens (sepBy1 typeType comma)

ctorType :: Parser Type
ctorType = TCtor <$> ctor <*> brackets (sepBy typeType comma)

ctor :: Parser Ctor
ctor = CT . fst <$> identStart upperChar

-- mkPairType :: [Type] -> SourceSpan -> Type
-- mkPairType [t]      _ = t
-- mkPairType [t1, t2] _ = TPair t1 t2
-- mkPairType _        l = panic "Mist only supports pairs types" l

defsExpr :: [BareDef] -> BareExpr
defsExpr [] = error "list of defintions is empty"
defsExpr bs@((b,_):_)   = go (bindLabel b) bs
  where
    go l [] = Unit l
    go _ ((b, e) : ds) = Let b e (go l ds) l
      where l = bindLabel b
