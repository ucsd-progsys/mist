{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE LambdaCase         #-}

module Language.Mist.Parser
  (
    parse
  , parseFile

  , SSParsedExpr
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
import qualified Data.Map.Strict as M
import           Language.Mist.Types

-- | parsed syntax elements with parsed expressions as the refinement
-- | Refinement expressions are Bare*, Mist expressions are SSParsed*
type BareExpr = Expr () SourceSpan
type BareBind = Bind () SourceSpan

type SSParsedExpr = ParsedExpr BareExpr SourceSpan
type SSParsedBind = ParsedBind BareExpr SourceSpan
type SSParsedDef = (SSParsedBind, SSParsedExpr)
type SSParsedAnnotation = ParsedAnnotation BareExpr SourceSpan
type SSParsedRType = RType BareExpr SourceSpan

--------------------------------------------------------------------------------
parse :: FilePath -> Text -> IO (Measures, SSParsedExpr)
--------------------------------------------------------------------------------
parse = parseWith ((,) <$> measures <*> topExprs <* eof)

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

--------------------------------------------------------------------------------
parseFile :: FilePath -> IO (Measures, SSParsedExpr)
--------------------------------------------------------------------------------
parseFile f = parse f =<< readFile f

type Parser = ParsecT SourcePos Text (State Integer)

-- https://mrkkrp.github.io/megaparsec/tutorials/parsing-simple-imperative-language.html
--------------------------------------------------------------------------------
-- | "Lexing"
--------------------------------------------------------------------------------

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

-- | `rWord` parses reserved words
rWord   :: String -> Parser SourceSpan
rWord w = snd <$> (withSpan (string w) <* notFollowedBy alphaNumChar <* sc)

-- | list of reserved words
keywords :: [Text]
keywords =
  [ "if"      , "else"  , "then"
  , "true"    , "false"
  , "let"     , "in"
  , "Int"     , "Bool"  , "forall"  , "as", "rforall"
  ]

-- | `identifier` parses identifiers: lower-case alphabets followed by alphas or digits
identifier :: Parser (String, SourceSpan)
identifier = identStart lowerChar
          <?> "identifier"

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

--------------------------------------------------------------------------------
-- | Locations
--------------------------------------------------------------------------------

stretch :: (Monoid a) => [Expr t a] -> a
stretch = mconcat . fmap extractLoc

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

exprAddParsedInfers :: Expr t a -> ParsedExpr r a
exprAddParsedInfers = goE
  where
    goE (AnnNumber n _ l) = Number n l
    goE (AnnBoolean b _ l) = Boolean b l
    goE (AnnUnit _ l) = Unit l
    goE (AnnId var _ l) = Id var l
    goE (AnnPrim op _ l) = Prim op l
    goE (AnnIf e1 e2 e3 _ l) = If (goE e1) (goE e2) (goE e3) l
    goE (AnnLet x e1 e2 _ l) = Let (goB x) (goE e1) (goE e2) l
    goE (AnnApp e1 e2 _ l) = App (goE e1) (goE e2) l
    goE (AnnLam x e _ l) = Lam (goB x) (goE e) l
    goE (AnnTApp e typ _ l) = TApp (goE e) typ l
    goE (AnnTAbs tvar e _ l) = TAbs tvar (goE e) l

    goB (AnnBind x _ l) = AnnBind x (Just ParsedInfer) l


--------------------------------------------------------------------------------
-- | Measures
--------------------------------------------------------------------------------

measures :: Parser Measures
measures = M.fromList <$> many measure

measure :: Parser (Id, Type)
measure = do
  _ <- L.nonIndented sc (rWord "measure")
  (id, _) <- identifier
  _ <- dcolon
  typ <- unrefinedScheme
  pure (id, typ)

--------------------------------------------------------------------------------
-- | Parsing Definitions
--------------------------------------------------------------------------------
topExprs :: Parser SSParsedExpr
topExprs = defsExpr <$> topDefs

topDefs :: Parser [SSParsedDef]
topDefs = many topDef

topDef :: Parser SSParsedDef
topDef = do
  Bind id tag <- L.nonIndented sc binder
  ann <- typeSig
  _ <- L.nonIndented sc $ lexeme (string id) <* symbol "="
  e <- expr
  let annBind = AnnBind id (Just ann) tag
  return (annBind, exprAddParsedInfers e)

defsExpr :: [SSParsedDef] -> SSParsedExpr
defsExpr [] = error "list of defintions is empty"
defsExpr bs@((b,_):_)   = go (bindTag b) bs
  where
    go l [] = Unit l
    go _ ((b, e) : ds) = Let b e (go l ds) l
      where l = bindTag b

--------------------------------------------------------------------------------
-- | Expressions
--------------------------------------------------------------------------------

-- NOTE: all applications require parentheses, except for operators.

expr :: Parser BareExpr
expr = makeExprParser expr0 binops

expr0 :: Parser BareExpr
expr0 = mkApps <$> sepBy1 simpleExpr sc
            <|> lamExpr  -- starts with \\
            <|> letExpr  -- starts with let
            <|> ifExpr   -- starts with if

-- A simpleExpr is one that has an end deliminator
simpleExpr :: Parser BareExpr
simpleExpr  = try constExpr
            <|> try idExpr
            <|> parens expr

mkApps :: [BareExpr] -> BareExpr
mkApps = L.foldl1' mkApp
mkApp :: BareExpr -> BareExpr -> BareExpr
mkApp e1 e2 = App e1 e2 (stretch [e1, e2])

binops :: [[Operator Parser BareExpr]]
binops =
  [ [ InfixL (pure op <*> primitive Times "*")
    , InfixL (pure op <*> primitive Elem "∈")
    , InfixL (pure op <*> primitive Union "∪")
    ]
  , [ InfixL (pure op <*> primitive Plus "+")
    , InfixL (pure op <*> primitive Minus "-")
    ]
  , [ InfixL (pure op <*> primitive Equal "==")
    , InfixL (pure op <*> primitive Equal "=")
    , InfixL (pure op <*> primitive Greater ">")
    , InfixL (pure op <*> primitive Lte "<=")
    , InfixL (pure op <*> primitive Less "<")
    , InfixL (pure op <*> primitive And "/\\")
    ]
  ]
  where
    op o e1 e2 = App (App o e1 (stretch [e1, o])) e2 (stretch [e1, e2])

primitive :: Prim -> String -> Parser BareExpr
primitive prim primSymbol = do
  p1 <- getPosition
  symbol primSymbol
  p2 <- getPosition
  pure $ Prim prim (SS p1 p2)

idExpr :: Parser BareExpr
idExpr = L.indentGuard sc GT pos1 *> flip fmap identifier (\case
   ("setPlus", l) -> Prim SetAdd l
   ("setMinus", l) -> Prim SetDel l
   (id,l) -> Id id l)

constExpr :: Parser BareExpr
constExpr
   =  (uncurry Number <$> integer)
  <|> (Boolean True   <$> rWord "True")
  <|> (Boolean False  <$> rWord "False")

letExpr :: Parser BareExpr
letExpr = withSpan' $ do
  rWord "let"
  bs <- sepBy1 bind comma
  rWord "in"
  e  <- expr
  return (bindsExpr bs e ())

bindsExpr :: [(Bind t a, Expr t a)] -> Expr t a -> t -> a -> Expr t a
bindsExpr bs e t l = foldr (\(x, e1) e2 -> AnnLet x e1 e2 t l) e bs

bind :: Parser (BareBind, BareExpr)
bind = (,) <$> binder <* symbol "=" <*> expr

ifExpr :: Parser BareExpr
ifExpr = withSpan' $ do
  rWord "if"
  b  <- expr
  e1 <- between (rWord "then") (rWord "else") expr
  e2 <- expr
  return (If b e1 e2)

lamExpr :: Parser BareExpr
lamExpr = withSpan' $ do
  char '\\' <* sc
  xs    <- sepBy binder sc <* symbol "->"
  e     <- expr
  return (\span -> (foldr (\x e -> Lam x e span) e xs))

--------------------------------------------------------------------------------
-- | Types
--------------------------------------------------------------------------------

typeSig :: Parser SSParsedAnnotation
typeSig
  =   (ParsedAssume <$> (rWord "as" *> scheme))
  <|> (ParsedCheck <$> (dcolon *> scheme))
  <|> pure ParsedInfer
  <?> "Type Signature"

unrefinedScheme :: Parser Type
unrefinedScheme = do
  tvars <- option [] $ rWord "forall" *> sepBy tvar comma <* symbol "."
  bodyType <- typeType
  pure $ foldr TForall bodyType tvars


scheme :: Parser SSParsedRType
scheme = do
  rvars <- option [] $ rWord "rforall" *> sepBy tvar comma <* symbol "."
  tvars <- option [] $ rWord "forall" *> sepBy tvar comma <* symbol "."
  bodyType <- typeRType
  pure $ foldr RForallP (foldr RForall bodyType tvars) rvars

typeType :: Parser Type
typeType = mkArrow <$> sepBy1 baseType (symbol "->")
        <?> "Unrefined Type"

typeRType :: Parser SSParsedRType
typeRType = try rfun <|>  try rbase <|> try unrefined <|> unrefinedRApp
         <?> "Refinement Type"

rapp :: Parser SSParsedRType
rapp = do
  c <- ctor
  ts <- many ((,) <$> variance <*> typeRType)
  pure $ RApp c ts

variance :: Parser Variance
variance =  char '>' *> pure Covariant
        <|> char '<' *> pure Contravariant
        <|> char '^' *> pure Invariant
        <|> char 'v' *> pure Bivariant


arrow :: Parser (BareBind -> SSParsedRType -> SSParsedRType -> SSParsedRType)
arrow = symbol "~>" *> pure RIFun <|> symbol "->" *> pure RFun

rfun :: Parser SSParsedRType
rfun = do id <- (binder <* colon) <|> freshBinder
          tin <- (unrefined <|> rbase <|> parens typeRType)
          arrow <*> pure id <*> pure tin <*> typeRType

unrefined :: Parser SSParsedRType
unrefined = RBase <$> freshBinder <*> baseType <*> pure (Boolean True mempty)

unrefinedRApp :: Parser SSParsedRType
unrefinedRApp = RRTy <$> freshBinder <*> rapp <*> pure (Boolean True mempty)

rbase :: Parser SSParsedRType
rbase = braces $ do
  b <- binder <* colon
  rbaseOrRrtype b

  where
    rbaseOrRrtype bind =
      try (RRTy bind <$> (try rapp <|> rbase) <* suchthat <*> expr)
      <|> (RBase bind <$> baseTypeNoCtor <* suchthat <*> expr)

baseTypeNoCtor :: Parser Type
baseTypeNoCtor
  =  (rWord "Int"   *> pure TInt)
 <|> (rWord "Bool"  *> pure TBool)
 <|> (rWord "Set"   *> pure TSet)
 <|> (TVar <$> tvar)

baseType :: Parser Type
baseType
  =  baseTypeNoCtor
 <|> ctorType
 <?> "Base Type"

mkArrow :: [Type] -> Type
mkArrow [t] = t
mkArrow ts@(_:_) = foldr (:=>) t ts'
  where t:ts' = L.reverse ts
mkArrow _  = error "impossible: mkArrow"

tvar :: Parser TVar
tvar = TV . fst <$> identifier
    <?> "Type Variable"

ctorType :: Parser Type
ctorType = TCtor <$> ctor <*> brackets (sepBy ((,) <$> variance <*> typeType) comma)
        <?> "Type Constructor"

ctor :: Parser Ctor
ctor = CT . fst <$> identStart upperChar
