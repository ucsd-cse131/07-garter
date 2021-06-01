{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

--------------------------------------------------------------------------------
-- | The entry point for the compiler: a function that takes a Text
--   representation of the source and returns a (Text) representation
--   of the assembly-program string representing the compiled version
--------------------------------------------------------------------------------

module Language.Garter.Compiler ( compiler, compile ) where

import           Control.Arrow                    ((>>>))
import           Prelude                  hiding (compare)
import           Control.Monad                   (void)
import           Data.Maybe
import           Data.Bits                       (shift)
import           Language.Garter.Types      hiding (Tag)
import           Language.Garter.Parser     (parse)
import           Language.Garter.Checker    (check, errUnboundVar)
import           Language.Garter.Normalizer (anormal)
import           Language.Garter.Asm        (asm)


--------------------------------------------------------------------------------
compiler :: FilePath -> Text -> Text
--------------------------------------------------------------------------------
compiler f = parse f >>> check >>> anormal >>> tag >>> compile >>> asm

--------------------------------------------------------------------------------
-- | The compilation (code generation) works with AST nodes labeled by @Tag@
--------------------------------------------------------------------------------
type Ann   = (SourceSpan, Int)
type AExp  = AnfExpr Ann
type IExp  = ImmExpr Ann
type ABind = Bind    Ann
type ADcl  = Decl    Ann
type APgm  = Program Ann

instance Located Ann where
  sourceSpan = fst

instance Located a => Located (Expr a) where
  sourceSpan = sourceSpan . getLabel

annTag :: Ann -> Int
annTag = snd 


--------------------------------------------------------------------------------
-- | @tag@ annotates each AST node with a distinct Int value
--------------------------------------------------------------------------------
tag :: AnfProgram SourceSpan -> APgm
--------------------------------------------------------------------------------
tag = label

--------------------------------------------------------------------------------
compile :: APgm -> [Instruction]
--------------------------------------------------------------------------------
compile (Prog ds e) = 
     compileDecl (Bind "" ()) [] e
  ++ concat [ compileDecl f xs e | (Decl f xs e _) <- ds ]

-- | @compileDecl f xs body@ returns the instructions of `body` of 
--   a function 'f' with parameters 'xs'
--   wrapped with code that (1) sets up the stack (by allocating space for n local vars)
--   and restores the callees stack prior to return.
compileDecl :: Bind a -> [Bind a] -> AExp -> [Instruction]
compileDecl f xs body = 
    [ ILabel (DefFun (bindId f)) ]
 ++ funEntry n                            -- 1. setup  stack frame RBP/RSP
 ++ [ ILabel (DefFunBody (bindId f)) ] 
 ++ copyArgs xs                           -- 2. copy parameters into stack slots
 ++ compileEnv env body                   -- 3. execute 'body' with result in RAX
 ++ funExit n                             -- 4. teardown stack frame & return 
  where
    env = fromListEnv (zip (bindId <$> xs) [1..])
    n   = length xs + countVars body 

-- | @compileArgs xs@ returns the instructions needed to copy the parameter values
--   FROM the combination of `rdi`, `rsi`, ... INTO this function's "frame".
--   RDI -> [RBP - 8], RSI -> [RBP - 16] 
copyArgs :: [a] -> [Instruction]
copyArgs xs =  
    copyRegArgs   rXs
 ++ copyStackArgs (length rXs) sXs
  where
    (rXs, sXs) = splitAt 6 xs

copyRegArgs :: [a] -> [Instruction]
copyRegArgs xs = 
  [ IMov (stackVar i) (Reg r) | (r, (i,_)) <- zip paramRegs (zip [1..] xs) ]

copyStackArgs :: Int -> [a] -> [Instruction]
copyStackArgs n xs = concat (zipWith3 copy xs [-2,-3..] [(n+1)..])
  where 
    copy _ src dst = [IMov (Reg RAX) (stackVar src), IMov (stackVar dst) (Reg RAX)] 

-- insert instructions for setting up stack for `n` local vars
funEntry :: Int -> [Instruction]
funEntry n = 
   [ IPush (Reg RBP)                       -- save caller's RBP
   , IMov  (Reg RBP) (Reg RSP)             -- set callee's RBP
   , ISub  (Reg RSP) (Const (argBytes n))  -- allocate n local-vars
   ] ++ 
   [ clearStackVar i | i <- [1..n] ]       -- zero out stack-vars

-- clean up stack & labels for jumping to error
funExit :: Int -> [Instruction]
funExit n = 
   [ IAdd (Reg RSP) (Const (argBytes n))    -- un-allocate n local-vars
   , IPop (Reg RBP)                         -- restore callee's RBP
   , IRet                                   -- return to caller
   ]

argBytes :: Int -> Int
argBytes n = 8 * roundUp n 

roundUp :: Int -> Int
roundUp n = if even n then n else n + 1

clearStackVar :: Int -> Instruction
clearStackVar i = IMov (Sized QWordPtr (stackVar i)) (Const 0)

--------------------------------------------------------------------------------
-- | @countVars e@ returns the maximum stack-size needed to evaluate e,
--   which is the maximum number of let-binds in scope at any point in e.
--------------------------------------------------------------------------------
countVars :: AnfExpr a -> Int
--------------------------------------------------------------------------------
countVars (Let _ e b _)  = max (countVars e) (1 + countVars b)
countVars (If v e1 e2 _) = maximum [countVars v, countVars e1, countVars e2]
countVars _              = 0

--------------------------------------------------------------------------------
compileEnv :: Env -> AExp -> [Instruction]
--------------------------------------------------------------------------------
compileEnv env v@Number {}       = [ compileImm env v  ]

compileEnv env v@Boolean {}      = [ compileImm env v  ]

compileEnv env v@Id {}           = [ compileImm env v  ]

compileEnv env (Let x e1 e2 _)   = error "fill this in" 

compileEnv env (Prim1 o v l)     = compilePrim1 l env o v

compileEnv env (Prim2 o v1 v2 l) = compilePrim2 l env o v1 v2

compileEnv env (If v e1 e2 l)    = error "fill this in"

compileEnv env (App f vs _)      = call (DefFun f) (immArg env <$> vs)

compileEnv env (Tuple es l)      = tupleCtor env es l 

compileEnv env (GetItem vE vI _) = error "fill this in"

compileImm :: Env -> IExp -> Instruction
compileImm env v = IMov (Reg RAX) (immArg env v)

compileBind :: Env -> (ABind, AExp) -> (Env, Int, [Instruction])
compileBind env (x, e) = (env', i, is)
  where
    is                 = compileEnv env e
                      ++ [IMov (stackVar i) (Reg RAX)]
    (i, env')          = pushEnv x env

compilePrim1 :: Ann -> Env -> Prim1 -> IExp -> [Instruction]
compilePrim1 l env Add1   v = error "fill this in"
compilePrim1 l env Sub1   v = error "fill this in"
compilePrim1 l env IsNum  v = error "fill this in"
compilePrim1 l env IsBool v = error "fill this in"
compilePrim1 _ env Print  v = call (Builtin "print") [immArg env v]
compilePrim1 l env IsTuple v = error "fill this in"

compilePrim2 :: Ann -> Env -> Prim2 -> IExp -> IExp -> [Instruction]
compilePrim2 _ env Plus    = error "fill this in"
compilePrim2 _ env Minus   = error "fill this in"
compilePrim2 _ env Times   = error "fill this in"
compilePrim2 l env Less    = error "fill this in"
compilePrim2 l env Greater = error "fill this in"
compilePrim2 l env Equal   = error "fill this in"

immArg :: Env -> IExp -> Arg
immArg _   (Number n _)  = repr n
immArg _   (Boolean b _) = repr b
immArg env e@(Id x _)    = stackVar (fromMaybe err (lookupEnv x env))
  where
    err                  = abort (errUnboundVar (sourceSpan e) x)
immArg _   e             = panic msg (sourceSpan e)
  where
    msg                  = "Unexpected non-immExpr in immArg: " ++ show (void e)

stackVar :: Int -> Arg
stackVar i = RegOffset i RBP

--------------------------------------------------------------------------------
-- | tuple Manipulation
--------------------------------------------------------------------------------
tupleCtor :: Env -> [IExp] -> Ann -> [Instruction]
tupleCtor env es l 
  =   tupleReserve l (tupleSize n)
   ++ error "fill this in with allocation code from egg-eater" 
  where
    n = length es

tupleSize :: Int -> Int
tupleSize n = 8 * (n + 2) -- add 2 slots for size, GC-Word

-- `tupleReserve l bytes` checks if R15 <= HEAP_END - bytes 
--  if so, continues, and otherwise calls `try_gc` to make some space
tupleReserve :: Ann -> Int -> [Instruction]
tupleReserve l bytes
  = [ IMov (Reg RAX) reg_HEAP_END
    , ISub (Reg RAX) (Const bytes)    -- RAX = HEAP_END - bytes
    , ICmp regData   (Reg RAX)        -- cmp R15 RAX
    , IJl  (MemCheck (snd l))         -- if R15 <  RAX then OK
    , IJe  (MemCheck (snd l))         -- if R15 == RAX then ok
    , IMov (Reg RBX) (Reg RSP)        -- set params for calling try_gc
    ]
 ++ call (Builtin "try_gc") [ regData, Const bytes, Reg RBP, Reg RBX ]  -- call try_gc
 ++ [ -- assume gc success if here; RAX holds new regData (R15)
      IMov regData (Reg RAX)          -- update R15 with new heap_start
    , ILabel (MemCheck (snd l))       -- continue ...
    ]



--------------------------------------------------------------------------------
-- | Function call
--------------------------------------------------------------------------------
-- `call f args` should generate the code for calling a function that starts at 
-- label `l` with the arguments `args` ...
call :: Label -> [Arg] -> [Instruction]
call f args =
    pushRegArgs   rArgs 
 ++ pushStackArgs sArgs
 ++ [ICall f]
 ++ popStackArgs  (length sArgs)
  where
    (rArgs, sArgs) = splitAt 6 args

pushRegArgs :: [Arg] -> [Instruction]
pushRegArgs args = [ IMov (Reg r) a | (r, a) <- zip paramRegs args ]

paramRegs :: [Reg]
paramRegs = [RDI, RSI, RDX, RCX, R8, R9] 

pushStackArgs :: [Arg] -> [Instruction]
pushStackArgs args 
  = ISub (Reg RSP) (Const (8 * k))
  : [ IPush a | a <- reverse args ]
  where
    n = length args
    k = (roundUp n) - n

popStackArgs :: Int -> [Instruction]
popStackArgs n = [ IAdd (Reg RSP) (Const (argBytes n)) ]


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

typeTag :: Ty -> Arg
typeTag TNumber   = HexConst 0x00000000
typeTag TBoolean  = HexConst 0x7fffffff
typeTag TTuple    = HexConst 0x00000001

typeMask :: Ty -> Arg
typeMask TNumber  = HexConst 0x00000001
typeMask TBoolean = HexConst 0x7fffffff
typeMask TTuple   = HexConst 0x00000007
