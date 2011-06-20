> {-# LANGUAGE StandaloneDeriving, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances #-}

A Non-Monadic interface to SAT/SMT/LP solvers
=============================================
  
> module Solve where

> import Control.Monad.State
> import Data.Functor.Identity
> import qualified Data.Map as M

> import qualified Yices.Easy as Y
> import qualified Yices.Easy.Sugar as Y
> import qualified Yices.Easy.Build as Y
> import Yices.Easy.Types (Value(..))

There are quite a few SAT, SMT and LP packages available on hackage, but many of them
have a monadic flavor. So I will again try to provide a clean abstraction layer
suitable for complex SAT/LP formulations, sticking to the design decisions outlined
below.

Decision 1: We want a pure, simple interface, and believe that to this end, the performance
overhead of deep embeddings is worth it.

Decision 2: The most natural way to use variables in a pure expression language is to allow
arbitrary haskell values to identify variables, and establish a mapping for use in the solver
using the standard Map moodule.

Decision 3: We want a dead-simple interface for simple optimization and SAT problems. The
interface should look something like this:

> --  solve     :: (Ord v) => [Assertion v] -> Maybe (Map v Value)

----

Here is one example from the modeling problem which motivated this module:

(a) Informal Specification:

We have two sets of integer variables: Input and Output ports for each switch, direction and phase.

(a) Formalization:

> {-
> type Phase = Int
> type Switch = (Int,Int)
> type Direction = Int
>
> data SwitchVar =  In  Phase Switch Direction
>                 | Out Phase Switch Direction deriving (Eq,Ord,Show,Read)
> instance Variable SwitchVar
> -}

(a) Informal Specification:

For phase p, the following is true:

> {-
> Foreach switch s, direction d and direction d' /= d
>   out_p,s,d /= out_p,s,d' v out_p,s,d == 0 v out_p,s,d' == 0
> -}

(b) Formalization:

> {-
> propertyOut :: Phase -> [Assertion SwitchVar]
> propertyOut p =
>   [ v =/= v' .||. v === integer 0 .||.  v' === integer 0
>   | s <- switches
>   , d <- directions
>   , d' <- directions, d' /= d
>   , let (v,v') = map (var . Out p s) [ d, d' ] 
>   ]
> -}

------------------------------------------------------------------------------------------------

> type Assertion v = Expression v Bool

We try to avoid polymorphic data constructors as far as possible, as, in my opinion
they complicate writing the backend a lot.

> data Expression v t where
>   Variable  :: (Variable v, ModelType t) => v -> Expression v t
>   Constant  :: (ModelType t) => t -> Expression v t
>   Not       :: Expression v Bool -> Expression v Bool
>   BoolT     :: BoolExpr v t -> Expression v t
>   IntegerT  :: IntegerExpr v t -> Expression v t

> deriving instance Show (Expression v t)

> data CmpOp = Eq | LtEq | Gt deriving (Eq,Ord,Show,Read)
> data FoldOp = Sum | Product deriving (Eq,Ord,Show,Read)

> data BoolExpr v t where
>   CmpB  :: CmpOp -> Expression v Bool -> Expression v Bool -> BoolExpr v Bool
>   FoldB :: FoldOp -> [Expression v Bool] -> BoolExpr v Bool

> deriving instance Show (BoolExpr v t)

> data IntegerExpr v t where
>   CmpI  :: CmpOp  -> Expression v Integer -> Expression v Integer -> IntegerExpr v Bool
>   FoldI :: FoldOp -> [Expression v Integer] -> IntegerExpr v Integer

> deriving instance Show (IntegerExpr v t)

> data Type = TyInt | TyBool deriving (Eq,Ord,Show,Read)
> class (Show v, Ord v) => Variable v
> data Constant =  ConstInt Integer | ConstBool Bool
> class (Show t) => ModelType t where
>   typeOf       :: t -> Type -- must not use first argument
>   toConstant   :: t -> Constant
>   fromConstant :: Constant -> Maybe t
> instance ModelType Bool where
>   typeOf _ = TyBool
>   toConstant = ConstBool
>   fromConstant c = case c of ConstBool b -> Just b; _ -> Nothing
> instance ModelType Integer where
>   typeOf _ = TyInt
>   toConstant = ConstInt
>   fromConstant c = case c of ConstInt i -> Just i; _ -> Nothing

> class Solver s where
>   solve :: (Variable v) => s -> [Assertion v] -> IO (Maybe (M.Map v Value))

> fromIntValue :: Value -> Integer
> fromIntValue v = case v of ValInt l -> fromIntegral l ; _ -> error ( "fromIntValue: " ++ show v )

Here starts the library:

> var :: (Variable v, ModelType t) => v -> Expression v t
> var = Variable

> integer :: (Integral n) => n -> Expression v Integer
> integer = Constant . fromIntegral

> true :: Expression v Bool
> true = Constant True

> false :: Expression v Bool
> false = Constant False

> class Eq' t where
>   (===) :: Expression v t -> Expression v t -> Expression v Bool
>   (=/=) :: Expression v t -> Expression v t -> Expression v Bool
>   (=/=) e1 e2 = Not (e1 === e2)
> infix 4 ===,=/=
> instance Eq' Bool    where (===) b1 b2 = BoolT    (CmpB Eq b1 b2)
> instance Eq' Integer where (===) i1 i2 = IntegerT (CmpI Eq i1 i2)

> class Ord' t where
>   (.>.) :: Expression v t -> Expression v t -> Expression v Bool
> instance Ord' Integer where (.>.) i1 i2 = IntegerT (CmpI Gt i1 i2)


> (.&&.) :: Expression v Bool -> Expression v Bool -> Expression v Bool
> (.&&.) e1 e2 = all' [e1,e2]
> infixr 1 .&&.
> (.||.) :: Expression v Bool -> Expression v Bool -> Expression v Bool
> (.||.) e1 e2 = any' [e1,e2]
> infixr 2 .||.

> any' :: [Expression v Bool] -> Expression v Bool
> any' = BoolT . FoldB Sum
> all' :: [Expression v Bool] -> Expression v Bool
> all' = BoolT . FoldB Product

> sum' :: [Expression v Integer] -> Expression v Integer
> sum' = IntegerT . FoldI Sum
> product' :: [Expression v Integer] -> Expression v Integer
> product' = IntegerT . FoldI Product

And a backend using yices-easy

> data YicesBackend = YicesBackend
> instance Solver YicesBackend where
>  solve yices = solveYices yices

> solveYices :: (Ord v) => YicesBackend -> [Assertion v] -> IO (Maybe (M.Map v Value))
> solveYices yices assertions = do
>   let (keymap, query) = Y.runBuild $ flip execStateT M.empty $ (mapM_ buildQuery assertions)
>   let rmap = (M.fromList . map (\(x,y) -> (y,x)) . M.toList) keymap
>   mmodel <- Y.solve query
>   return $ case mmodel of
>      Y.Sat model -> Just $ M.mapKeys (rmap M.!) model
>      _           -> Nothing

> buildQuery :: (Ord v) => Expression v Bool -> StateT (M.Map v String) (Y.BuildT Identity) ()
> buildQuery e = buildExpression e >>= (lift . Y.assert)

> buildExpression :: (Ord v) => Expression v t -> StateT (M.Map v String) (Y.BuildT Identity) Y.Expr
> buildExpression (Variable v :: Expression v t) = do
>   vmap <- get
>   case M.lookup v vmap of
>     Nothing -> do
>       ident <- lift (Y.freshName "v_")
>       modify (M.insert v ident)
>       case typeOf (undefined :: t) of
>         TyInt  -> lift$ Y.declInt ident
>         TyBool -> lift$ Y.declBool ident
>     Just ident -> return (Y.Var ident)
> buildExpression (Constant t) = do
>   case toConstant t of
>     ConstInt i  -> return $ Y.LitNum (Y.FromString (show i))
>     ConstBool b -> return $ Y.LitBool b
> buildExpression (Not e) = liftM (Y.Not) (buildExpression e)
> buildExpression (BoolT be) = buildBooleanExpression be
> buildExpression (IntegerT ie) = buildIntegerExpression ie

> buildBooleanExpression (CmpB cmp e1 e2) = do
>   [ye1,ye2] <- mapM buildExpression [e1,e2]
>   return $ case cmp of
>     Eq   -> Y.Compare Y.Eq ye1 ye2
>     LtEq -> Y.Compare Y.Le ye1 ye2
>     Gt   -> Y.Compare Y.Gt ye1 ye2
> buildBooleanExpression (FoldB op es) = do
>   yes <- mapM buildExpression es
>   return $ case op of
>     Sum     -> Y.Logic Y.Or  yes
>     Product -> Y.Logic Y.And yes

> buildIntegerExpression (CmpI cmp e1 e2) = do
>   [ye1,ye2] <- mapM buildExpression [e1,e2]
>   return $ case cmp of
>     Eq   -> Y.Compare Y.Eq ye1 ye2
>     LtEq -> Y.Compare Y.Le ye1 ye2
>     Gt   -> Y.Compare Y.Gt ye1 ye2
> buildIntegerExpression (FoldI op es) = do
>   yes <- mapM buildExpression es
>   return $ case op of
>     Sum     -> Y.Arith Y.Add yes
>     Product -> Y.Arith Y.Mul yes

And finally, simple examples

> instance Variable String

> runDemo = solve YicesBackend 
>     [ true
>     , true
>     , var "b1"
>     , Not (var "b2")
>     , var "x" =/= integer 0 
>     , var "y" =/= (var "z" :: Expression String Integer)
>     , sum' [ var "x" , var "z" ] === integer 42
>     , product' [var "x", integer 4 ] === integer 16
>     , var "b3" .||. var "b4" .||. var "b5"
>     ] >>= print
