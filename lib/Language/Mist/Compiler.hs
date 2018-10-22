{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Mist.Compiler ( compiler, compile ) where

import           Prelude                  hiding (compare)
import           Control.Arrow            ((>>>))
import           Data.Maybe
import           Data.Bits                       (shift)
import qualified Data.Set                as S
-- import           Language.Mist.Utils
import           Language.Mist.Types      hiding (Tag)
import           Language.Mist.Parser     (parse)
import           Language.Mist.Checker    (check, errUnboundVar)
import           Language.Mist.Normalizer (anormal)
import           Language.Mist.Asm        (asm)


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> compile >>> asm

--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Tag@
--------------------------------------------------------------------------------
type Tag   = (SourceSpan, Int)
type AExp  = AnfExpr Tag
type IExp  = ImmExpr Tag
type ABind = Bind    Tag

instance Located Tag where
  sourceSpan = fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

--------------------------------------------------------------------------------
-- | @tag@ annotates each AST node with a distinct Int value
--------------------------------------------------------------------------------
tag :: AnfExpr SourceSpan -> AExp
--------------------------------------------------------------------------------
tag = label

--------------------------------------------------------------------------------
compile :: AExp -> [Instruction]
--------------------------------------------------------------------------------
compile e = lambdaBody Nothing [] [] e

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e)  (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0


--------------------------------------------------------------------------------
freeVars :: Expr a -> [Id]
--------------------------------------------------------------------------------
freeVars e = S.toList (free e)

frees :: [Expr a] -> S.Set Id
frees es  = S.unions (map free es)

free :: Expr a -> S.Set Id
free (Number {})       = S.empty
free (Boolean {})      = S.empty
free (Id x _)          = S.singleton x
free (Let x e e' _)    = S.union (free e) (S.delete (bindId x) (free e'))
free (Prim1 _ e _)     = free e
free (Prim2 _ e e' _)  = frees [e, e']
free (If b e e' _)     = frees [b, e, e']
free (Tuple e e' _)    = frees [e, e']
free (GetItem e _ _)   = free e
free (App e es _)      = frees (e:es)
free (Lam xs e _)      = S.difference (free e) (S.fromList (bindId <$> xs))
free (Fun f _ xs e _)  = S.difference (free e) (S.fromList (bindId <$> f:xs))

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@(Number {})     = [ compileImm env v  ]

compileEnv env v@(Boolean {})    = [ compileImm env v  ]

compileEnv env v@(Id {})         = [ compileImm env v  ]

compileEnv env e@(Let {})        = is ++ compileEnv env' body
  where
    (env', is)                   = compileBinds env [] binds
    (binds, body)                = exprBinds e

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = assertType env v TBoolean
                                ++ IMov (Reg EAX) (immArg env v)
                                 : ICmp (Reg EAX) (repr False)
                                 : branch l IJe i1s i2s
  where
    i1s                          = compileEnv env e1
    i2s                          = compileEnv env e2


compileEnv env (Tuple e1 e2 _)   = tupleAlloc  2
                                ++ tupleWrites (immArg env <$> [e1, e2])
                                ++ [ IOr  (Reg EAX) (typeTag TTuple) ]

compileEnv env (GetItem vE f _) = tupleRead env vE f

compileEnv env (Lam xs e l)      = lambda l env Nothing xs  e
compileEnv env (Fun f _ xs e l)  = lambda l env (Just f) xs e
compileEnv env (App v vs l)      = apply  l env v vs

compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg EAX) (immArg env v)

compileBinds :: Env -> [Instruction] -> [(ABind, AExp)] -> (Env, [Instruction])
compileBinds env is []     = (env, is)
compileBinds env is (b:bs) = compileBinds env' (is ++ is') bs
  where
    (env', is')            = compileBind env b

compileBind :: Env -> (ABind, AExp) -> (Env, [Instruction])
compileBind env (x, e) = (env', is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg EAX)]
    (i, env')          = pushEnv x env

compilePrim1 :: Tag -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1   v = compilePrim2 l env Plus  v (Number 1 l)
compilePrim1 l env Sub1   v = compilePrim2 l env Minus v (Number 1 l)
-- compilePrim1 l env IsNum  v = isType l env v TNumber
-- compilePrim1 l env IsBool v = isType l env v TBoolean
compilePrim1 _ env Print  v = call (builtin "print") [param env v]

compilePrim2 :: Tag -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus    = arith     env addOp
compilePrim2 _ env Minus   = arith     env subOp
compilePrim2 _ env Times   = arith     env mulOp
compilePrim2 l env Less    = compare l env IJl (Just TNumber)
compilePrim2 l env Greater = compare l env IJg (Just TNumber)
compilePrim2 l env Equal   = compare l env IJe Nothing

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " ++ show (strip e)

strip = fmap (const ())

--------------------------------------------------------------------------------
-- | Arithmetic
--------------------------------------------------------------------------------
arith :: Env -> AOp -> IExp -> IExp  -> [Instruction]
--------------------------------------------------------------------------------
arith env aop v1 v2
  =  assertType env v1 TNumber
  ++ assertType env v2 TNumber
  ++ IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : aop (Reg EAX) (Reg EBX)

addOp :: AOp
addOp a1 a2 = [ IAdd a1 a2
              , overflow
              ]

subOp :: AOp
subOp a1 a2 = [ ISub a1 a2
              , overflow
              ]

mulOp :: AOp
mulOp a1 a2 = [ IMul a1 a2
              , overflow
              , ISar a1 (Const 1)
              ]

overflow :: Instruction
overflow = IJo (DynamicErr ArithOverflow)

--------------------------------------------------------------------------------
-- | Dynamic Tests
--------------------------------------------------------------------------------
-- | @assertType t@ tests if EAX is a value of type t and exits with error o.w.
assertType :: Env -> IExp -> Ty -> [Instruction]
assertType env v ty = []
 -- =   cmpType env v ty
 -- ++ [ IJne (DynamicErr (TypeError ty))    ]

cmpType :: Env -> IExp -> Ty -> [Instruction]
cmpType env v ty
  = [ IMov (Reg EAX) (immArg env v)
    , IMov (Reg EBX) (Reg EAX)
    , IAnd (Reg EBX) (typeMask ty)
    , ICmp (Reg EBX) (typeTag  ty)
    ]

assertArity :: Env -> IExp -> Int -> [Instruction]
assertArity env v n
  = tupleReadRaw (immArg env v) (repr (0 :: Int))        -- 0-th tuple element is the arity
 ++ [ ICmp (Reg EAX) (repr n)
    , IJne (DynamicErr ArityError)
    ]

--------------------------------------------------------------------------------
-- | Comparisons
--------------------------------------------------------------------------------
-- | @compare v1 v2@ generates the instructions at the
--   end of which EAX is TRUE/FALSE depending on the comparison
--------------------------------------------------------------------------------
compare :: Tag -> Env -> COp -> Maybe Ty -> IExp -> IExp -> [Instruction]
compare l env j t v1 v2
  =  compareCheck env t v1 v2
  ++ compareVal l env j v1 v2

compareCheck :: Env -> Maybe Ty -> IExp -> IExp -> [Instruction]
compareCheck _   Nothing  _  _
  =  []
compareCheck env (Just t) v1 v2
  =  assertType env v1 t
  ++ assertType env v2 t

compareVal :: Tag -> Env -> COp -> IExp -> IExp -> [Instruction]
compareVal l env j v1 v2
   = IMov (Reg EAX) (immArg env v1)
   : IMov (Reg EBX) (immArg env v2)
   : ICmp (Reg EAX) (Reg EBX)
   : boolBranch l j

--------------------------------------------------------------------------------
-- | Apply (Function Call)
--------------------------------------------------------------------------------
apply :: Tag -> Env -> IExp -> [IExp] -> [Instruction]
apply _ env v vs
  = assertType    env v TClosure
 ++ assertArity   env v (length vs)
 ++ tupleReadRaw  (immArg env v) (repr (1 :: Int))  -- load v[1] (code-pointer) into EAX
 ++ call (Reg EAX) (param env <$> (v:vs))           -- call EAX with closure + params

--------------------------------------------------------------------------------
-- | Lambda (Function Definition)
--------------------------------------------------------------------------------
lambda :: Tag -> Env -> Maybe ABind -> [ABind] -> AExp -> [Instruction]
lambda l env f xs e
  = IJmp   (LamEnd   i)
  : ILabel (LamStart i)
  : lambdaBody f ys xs e
 ++ ILabel (LamEnd   i)
  : lambdaClosure l env arity ys
  where
    ys    = freeVars (fun f xs e l)
    arity = length xs
    i     = snd l

-- | Constructing a function expression
fun :: Maybe (Bind a) -> [Bind a] -> Expr a -> a -> Expr a
fun (Just f) = Fun f Infer
fun Nothing  = Lam

-- | @lambdaClosure l env arity ys@ returns a sequence of instructions,
--   that have the effect of writing into EAX the value of the closure
--   corresponding to the lambda-functiion l. To do so we must:
--
--   1. allocate space on the tuple for a "tuple" of
--        (arity, LamStart l, y1, y2, ... , yn) + padding
--   2. write the values of arity, y1...yn into the above
--   3. adjust the address bits to ensure 101-ending

lambdaClosure :: Tag -> Env -> Int -> [Id] -> [Instruction]
lambdaClosure l env arity ys
  =  tupleAlloc (1 + 1 + length ys)
  ++ tupleWrites (nV : ptrV : yVs)
  ++ [ IOr  (Reg EAX) (typeTag TClosure) ]
  where
    nV   = repr arity
    ptrV = CodePtr (LamStart (snd l))
    yVs  = [immArg env (Id y l) | y <- ys]


-- | @lambdaBody name ys xs e@ returns the instructions corresponding to the
--   body of the function (lambda (xs): e) where `ys` are the free variables
--   that occur in the lambda.  The instructions should:
--   1. Get the closure value (address) from the stack (at EBP+8)
--   2. Use the above to restore the free-variables onto the stack
--   3. Evaluate the body @e@ in the resulting stack.
--   In addition, we must take care to appropriately manage the stack, and
--   base-pointers (esp, ebp), by wrapping everything in @funInstrs@.
--   @name@ is the (optional) name of the function,
--   When it is defined i.e. is @Just f@, we should add @f@ to the params of the
--   lambda and extract its value from EBP+4.

lambdaBody :: Maybe ABind -> [Id] -> [ABind] -> AExp -> [Instruction]
lambdaBody f ys xs e = funInstrs maxStack (restore ys ++ compileEnv env e)
  where
    maxStack         = envMax env + countVars e
    env              = lambdaEnv f ys xs

lambdaEnv :: Maybe ABind -> [Id] -> [ABind] -> Env
lambdaEnv f ys xs = fromListEnv bs
  where
    xs'           = bindId <$> xs
    bs            = [ (me, -2) | (Bind me _) <- maybeToList f ]
                 ++ zip xs' [-3,-4..]
                 ++ zip ys  [1..]

-- | @restore ys@ uses the closure passed in at [EBP+8] to
--   copy the free-vars 'ys' onto the stack.
restore :: [Id] -> [Instruction]
restore ys = concat [ copy i | (_,i) <- zip ys [1..]]
  where
    closV  = RegOffset 8 EBP
    copy i = tupleReadRaw closV (repr (i + 1))
          ++ [ IMov (stackVar i) (Reg EAX) ]

-- | @funInstrs n body@ returns the instructions of `body` wrapped
--   with code that sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return.

funInstrs :: Int -> [Instruction] -> [Instruction]
funInstrs n instrs = funEntry n ++ instrs ++ funExit

-- FILL: insert instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = [ IPush (Reg EBP)                       -- save caller's ebp
             , IMov  (Reg EBP) (Reg ESP)             -- set callee's ebp
             , ISub  (Reg ESP) (Const (4 * n))       -- allocate n local-vars
             , IAnd  (Reg ESP) (HexConst 0xFFFFFFF0) -- MacOS stack alignment
             ]

-- FILL: clean up stack & labels for jumping to error
funExit :: [Instruction]
funExit   = [ IMov (Reg ESP) (Reg EBP)          -- restore callee's esp
            , IPop (Reg EBP)                    -- restore callee's ebp
            , IRet                              -- jump back to caller
            ]
--------------------------------------------------------------------------------
-- | Assignment
--------------------------------------------------------------------------------
assign :: (Repr a) => Reg -> a -> Instruction
assign r v = IMov (Reg r) (repr v)

--------------------------------------------------------------------------------
-- | Function call
--------------------------------------------------------------------------------
call :: Arg -> [Arg] -> [Instruction]
call f args
  =    ISub (Reg ESP) (Const (4 * k))
  :  [ IPush a | a <- reverse args ]
  ++ [ ICall f
     , IAdd (Reg ESP) (Const (4 * (n + k)))  ]
  where
    n = length args
    k = 4 - (n `mod` 4)

param :: Env -> IExp -> Arg
param env v = Sized DWordPtr (immArg env v)

--------------------------------------------------------------------------------
-- | Branching
--------------------------------------------------------------------------------
branch :: Tag -> COp -> [Instruction] -> [Instruction] -> [Instruction]
branch l j falseIs trueIs = concat
  [ [ j lTrue ]
  , falseIs
  , [ IJmp lDone
    , ILabel lTrue  ]
  , trueIs
  , [ ILabel lDone ]
  ]
  where
    lTrue = (BranchTrue i)
    lDone = (BranchDone i)
    i     = snd l

boolBranch :: Tag -> COp -> [Instruction]
boolBranch l j = branch l j [assign EAX False] [assign EAX True]

type AOp = Arg -> Arg -> [Instruction]
type COp = Label -> Instruction

stackVar :: Int -> Arg
stackVar i = RegOffset (-4 * i) EBP


--------------------------------------------------------------------------------
-- | tuple Manipulation
--------------------------------------------------------------------------------
tupleAlloc   :: Int -> [Instruction]
tupleAlloc n = [ IMov (Reg EAX) (Reg ESI)
              , IMov (Sized DWordPtr (RegOffset 0 EAX)) (repr n)
              , IAdd (Reg ESI) (Const size)
              ]
  where
    size    = 4 * roundToEven (n + 1)

tupleWrites :: [Arg] -> [Instruction]
tupleWrites args = concat (zipWith tupleWrite [1..] args)
  where
    tupleWrite i a = [ IMov (Reg EBX) a
                     , IMov (Sized DWordPtr (tupleLoc i)) (Reg EBX)
                     ]

tupleLoc :: Int -> Arg
tupleLoc i = RegOffset (4 * i) EAX

tupleRead :: Env -> IExp -> Field -> [Instruction]
tupleRead env vE fld
  = tupleReadRaw (immArg env vE) (repr fld)

tupleReadRaw :: Arg -> Arg -> [Instruction]
tupleReadRaw aE aI
  =  loadAddr aE
  ++ [ IMov (Reg EBX) aI
     , IShr (Reg EBX) (Const 1)
     , IAdd (Reg EBX) (Const 1)
     , IMov (Reg EAX) (RegIndex EAX EBX)
     ]

-- | `loadAddr env vE` assigns to EAX the "base address" of tuple `vE`
loadAddr :: Arg -> [Instruction]
loadAddr a
  = [ IMov (Reg EAX) a                        -- compute address
    -- , ISub (Reg EAX) (typeTag ty)          -- drop tag bits
    , IAnd (Reg EAX) (HexConst 0xfffffff8)    -- set last three bits to 0
    ]

roundToEven :: Int -> Int
roundToEven n
  | n `mod` 2 == 0 = n
  | otherwise      = n + 1

--------------------------------------------------------------------------------
-- | Representing Values
--------------------------------------------------------------------------------

class Repr a where
  repr :: a -> Arg

instance Repr Bool where
  repr True  = HexConst 0xffffffff
  repr False = HexConst 0x7fffffff

instance Repr Int where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Integer where
  repr n = Const (fromIntegral (shift n 1))

instance Repr Field where
  repr Zero = repr (0 :: Int)
  repr One  = repr (1 :: Int)

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001
typeTag TClosure  = HexConst 0x00000005

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
typeMask TClosure = HexConst 0x00000007
