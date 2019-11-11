{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE LambdaCase         #-}

module Language.Mist.Parser
  (
    parse
  , parseFile
  ) where

import qualified Control.Exception          as Ex
import           Control.Monad (void)
import           Control.Monad.State.Strict
import           Text.Megaparsec hiding (parse, State)
import           Data.List.NonEmpty         as NE
import qualified Text.Megaparsec.Char.Lexer as L
import           Text.Megaparsec.Char
import           Control.Monad.Combinators.Expr
import qualified Data.List as L
import qualified Data.Map.Strict as M
import           Language.Mist.Types

-- | parsed syntax elements with parsed expressions as the refinement
-- | Refinement expressions are Bare*, Mist expressions are SSParsed*
type SSParsedExpr = ParsedExpr SourceSpan
type SSParsedBind = ParsedBind SSParsedExpr SourceSpan
type SSParsedDef = (SSParsedBind, SSParsedExpr)
type SSParsedAnnotation = ParsedAnnotation SSParsedExpr SourceSpan
type SSParsedRType = RType SSParsedExpr SourceSpan

--------------------------------------------------------------------------------
parse :: FilePath -> Text -> IO (Measures, SSParsedExpr)
--------------------------------------------------------------------------------
parse = parseWith ((,) <$> measures <*> topExprs <* eof)

parseWith  :: Parser a -> FilePath -> Text -> IO a
parseWith p f s = case flip evalState 0 $ runParserT (whole p) f s of
                    Left err -> Ex.throw [parseUserError err]
                    Right e  -> return e

parseUserError :: ParseErrorBundle Text SourcePos -> UserError
parseUserError err = mkError msg sp
  where
    msg            = "parse error\n" ++ parseErrorTextPretty (NE.head (bundleErrors err))
    sp             = posSpan . snd . NE.head . fst $ attachSourcePos errorOffset (bundleErrors err) (bundlePosState err)

instance ShowErrorComponent SourcePos where
  showErrorComponent = sourcePosPretty

-- Megaparsec 7.0 changes
-- https://markkarpov.com/post/megaparsec-7.html
getPosition :: MonadParsec e s m => m SourcePos
getPosition = do
  st <- getParserState
  -- We're not interested in the line at which the offset is located in
  -- this case, but the same 'reachOffset' function is used in
  -- 'errorBundlePretty'.
  let (pos, _, pst) = reachOffset (stateOffset st) (statePosState st)
  setParserState st { statePosState = pst }
  return pos

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
  [ "if", "else", "then"
  , "true", "false"
  , "let", "in"
  , "Int", "Bool"
  , "forall", "as", "rforall", "exists"
  , "unpack"
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
binder :: Parser SSParsedBind
binder = uncurry Bind <$> identifier

freshBinder :: Parser SSParsedBind
freshBinder = uncurry Bind <$> (lexeme $ ("fresh" ++) . show <$> lift get)

freshBareBinder :: Parser (Bind () SourceSpan)
freshBareBinder = eraseBind <$> freshBinder

iLamBinder :: Parser (Bind (Maybe Type) SourceSpan)
iLamBinder = uncurry Bind <$> identifier

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

exprAddParsedInfers :: RefinedExpr (ParsedExpr a) a -> ParsedExpr a
exprAddParsedInfers = goE
  where
    goE (AnnNumber n _ l)    = ParsedExpr $ Number n l
    goE (AnnBoolean b _ l)   = ParsedExpr $ Boolean b l
    goE (AnnUnit _ l)        = ParsedExpr $ Unit l
    goE (AnnId var _ l)      = ParsedExpr $ Id var l
    goE (AnnPrim op _ l)     = ParsedExpr $ Prim op l
    goE (AnnIf e1 e2 e3 _ l) = ParsedExpr $ If (goUn e1) (goUn e2) (goUn e3) l
    goE (AnnLet x e1 e2 _ l) = ParsedExpr $ Let (goB x) (goUn e1) (goUn e2) l
    goE (AnnApp e1 e2 _ l)   = ParsedExpr $ App (goUn e1) (goUn e2) l
    goE (AnnLam x e _ l)     = ParsedExpr $ Lam (goB x) (goUn e) l
    goE (AnnILam x e _ l)    = ParsedExpr $ ILam x (goUn e) l
    goE (AnnTApp e typ _ l)  = ParsedExpr $ TApp (goUn e) typ l
    goE (AnnTAbs tvar e _ l) = ParsedExpr $ TAbs tvar (goUn e) l
    goE (AnnUnpack b1 b2 e1 e2 _ l) = ParsedExpr $ Unpack b1 (goB b2) (goUn e1) (goUn e2) l

    goUn = unParsedExpr . goE

    goB (AnnBind x Nothing l) = AnnBind x (Just ParsedInfer) l
    goB (AnnBind x t l) = AnnBind x t l


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
topExprs = defsExpr (ParsedExpr . Unit) <$> topDefs

topDefs :: Parser [SSParsedDef]
topDefs = many topDef

topDef :: Parser SSParsedDef
topDef = do
  Bind id tag <- L.nonIndented sc binder
  ann <- typeSig
  depth <- L.indentLevel
  if depth > pos1 then fail $ "Expected start of binding for `" <> id <> "' here" else pure ()
  _ <- lexeme (string id) <* symbol "="
  e <- expr
  let annBind = AnnBind id (Just ann) tag
  return (annBind, exprAddParsedInfers $ unParsedExpr e)

defsExpr :: (SourceSpan -> SSParsedExpr) -> [SSParsedDef] -> SSParsedExpr
defsExpr _ [] = error "list of defintions is empty"
defsExpr base bs@((b,_):_) = ParsedExpr $ go (bindTag b) bs
  where
    go l [] = unParsedExpr $ base l
    go _ ((b, ParsedExpr e) : ds) = Let b e (go l ds) l
      where l = bindTag b

--------------------------------------------------------------------------------
-- | Expressions
--------------------------------------------------------------------------------

-- NOTE: all applications require parentheses, except for operators.

expr :: Parser SSParsedExpr
expr = makeExprParser expr0 binops

expr0 :: Parser SSParsedExpr
expr0 = mkApps <$> sepBy1 simpleExpr sc
            <|> try lamExpr  -- starts with \\
            <|> try iLamExpr -- starts with \\
            <|> letExpr  -- starts with let
            <|> ifExpr   -- starts with if
            <|> unpackExpr -- starts with unpack

-- A simpleExpr is one that has an end deliminator
simpleExpr :: Parser SSParsedExpr
simpleExpr = try constExpr
         <|> try idExpr
         <|> parens expr

mkApps :: [SSParsedExpr] -> SSParsedExpr
mkApps = L.foldl1' mkApp
mkApp :: SSParsedExpr -> SSParsedExpr -> SSParsedExpr
mkApp (ParsedExpr e1) (ParsedExpr e2) = ParsedExpr $ App e1 e2 (stretch [e1, e2])

binops :: [[Operator Parser SSParsedExpr]]
binops =
  [ [ InfixL (pure op <*> primitive Times "*")
    , InfixL (pure op <*> primitive Elem "∈")
    , InfixL (pure op <*> primitive Union "∪")
    ]
  , [ InfixL (pure op <*> primitive Plus "+")
    , InfixL (pure op <*> primitive Minus "-")
    ]
  , [ InfixL (pure op <*> primitive NEqual "/=")
    , InfixL (pure op <*> primitive NEqual "≠")
    , InfixL (pure op <*> primitive Implies "=>")
    , InfixL (pure op <*> primitive Equal "==")
    , InfixL (pure op <*> primitive Equal "=")
    , InfixL (pure op <*> primitive Greater ">")
    , InfixL (pure op <*> primitive Lte "<=")
    , InfixL (pure op <*> primitive Less "<")
    , InfixL (pure op <*> primitive And "/\\")
    , InfixL (pure op <*> primitive Or "\\/")
    ]
  ]
  where
    op o e1 e2 = mkApps [o, e1, e2]

primitive :: Prim -> String -> Parser SSParsedExpr
primitive prim primSymbol = do
  p1 <- getPosition
  symbol primSymbol
  p2 <- getPosition
  pure $ ParsedExpr $ Prim prim (SS p1 p2)

idExpr :: Parser SSParsedExpr
idExpr = L.indentGuard sc GT pos1 *> (ParsedExpr <$> (\case
   ("setPlus", l) -> Prim SetAdd l
   ("setMinus", l) -> Prim SetDel l
   ("setSubset", l) -> Prim SetSub l
   ("store", l) -> Prim Store l
   ("select", l) -> Prim Select l
   (id,l) -> Id id l) <$> identifier)

constExpr :: Parser SSParsedExpr
constExpr
   = fmap ParsedExpr $
      (uncurry Number <$> integer)
  <|> (Boolean True   <$> rWord "True")
  <|> (Boolean False  <$> rWord "False")
  <|> (Unit           <$> rWord "Unit")

letExpr :: Parser SSParsedExpr
letExpr = fmap ParsedExpr $ withSpan' $ do
  rWord "let"
  bs <- fmap (fmap unParsedExpr) <$> sepBy1 bind comma
  rWord "in"
  ParsedExpr e <- expr
  return (bindsExpr bs e $ Just ParsedInfer)

unpackExpr :: Parser SSParsedExpr
unpackExpr = fmap ParsedExpr $ withSpan' $ do
  rWord "unpack"
  symbol "("
  bx <- uncurry Bind <$> identifier
  symbol ","
  be <- letBinder
  symbol ")"
  symbol "="
  ParsedExpr e1 <- expr
  rWord "in"
  ParsedExpr e2 <- expr
  pure $ AnnUnpack bx be e1 e2 (Just ParsedInfer)

bindsExpr :: [(Bind t a, Expr t a)] -> Expr t a -> t -> a -> Expr t a
bindsExpr bs e t l = foldr (\(x, e1) e2 -> AnnLet x e1 e2 t l) e bs

bind :: Parser (SSParsedBind, SSParsedExpr)
bind = (,) <$> letBinder <* symbol "=" <*> expr

letBinder :: Parser SSParsedBind
letBinder = do
    (x, a) <- identifier
    t <- optional $ dcolon *> scheme
    pure $ AnnBind x (ParsedCheck <$> t) a

ifExpr :: Parser SSParsedExpr
ifExpr = fmap ParsedExpr $ withSpan' $ do
  rWord "if"
  ParsedExpr b  <- expr
  ParsedExpr e1 <- between (rWord "then") (rWord "else") expr
  ParsedExpr e2 <- expr
  return (If b e1 e2)

lamExpr :: Parser SSParsedExpr
lamExpr = fmap ParsedExpr $ withSpan' $ do
  char '\\' <* sc
  xs <- sepBy binder sc <* symbol "->"
  ParsedExpr e <- expr
  return (\span -> (foldr (\x e -> Lam x e span) e xs))

iLamExpr :: Parser SSParsedExpr
iLamExpr = fmap ParsedExpr $ withSpan' $ do
  char '\\' <* sc
  xs <- sepBy iLamBinder sc <* symbol "~>"
  ParsedExpr e <- expr
  return (\span -> (foldr (\x e -> ILam x e span) e xs))

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

-- exists x:t. e
sigma :: Parser SSParsedRType
sigma = do
  rWord "exists"
  id <- eraseBind <$> binder <* colon
  tin <- (try unrefined <|> rbase <|> parens typeRType <|> unrefinedRApp)
  symbol "."
  bodyType <- typeRType
  pure $ RIExists id tin bodyType

typeType :: Parser Type
typeType = mkArrow <$> sepBy1 baseType (symbol "->")
        <?> "Unrefined Type"

typeRType :: Parser SSParsedRType
typeRType = try rfun <|> try rbase <|> try unrefined <|> try (parens sigma) <|> try (parens scheme) <|> unrefinedRApp

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


arrow :: Parser (SSParsedBind -> SSParsedRType -> SSParsedRType -> SSParsedRType)
arrow = symbol "~>" *> pure (RIFun . eraseBind) <|> symbol "->" *> pure (RFun . eraseBind)

rfun :: Parser SSParsedRType
rfun = do id <- (binder <* colon) <|> freshBinder
          tin <- (try unrefined <|> rbase <|> try (parens sigma) <|> parens typeRType <|> unrefinedRApp)
          arrow <*> pure id <*> pure tin <*> typeRType

unrefined :: Parser SSParsedRType
unrefined = RBase <$> freshBareBinder <*> baseType <*> pure (ParsedExpr $ Boolean True mempty)

unrefinedRApp :: Parser SSParsedRType
unrefinedRApp = RRTy <$> freshBareBinder <*> rapp <*> pure (ParsedExpr $ Boolean True mempty)

rbase :: Parser SSParsedRType
rbase = braces $ do
  b <- binder <* colon
  rbaseOrRrtype $ eraseBind b

  where
    rbaseOrRrtype b =
      try (RRTy b <$> (try rapp <|> rbase) <* suchthat <*> expr)
      <|> (RBase b <$> baseTypeNoCtor <* suchthat <*> expr)

baseTypeNoCtor :: Parser Type
baseTypeNoCtor
  =  (rWord "Int"   *> pure TInt)
 <|> (rWord "Bool"  *> pure TBool)
 <|> (rWord "Unit"  *> pure TUnit)
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

-- discard types in refinements, maybe change RType to not do this?
eraseBind :: SSParsedBind -> Bind () SourceSpan
eraseBind (Bind id s) = Bind id s
