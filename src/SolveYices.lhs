> {-# LANGUAGE ScopedTypeVariables, GADTs #-}

Yices Backend for Solve
=======================

> module SolveYices where

> import Control.Monad.State
> import Data.Functor.Identity
> import qualified Data.Map as M

> import qualified Yices.Easy as Y
> import qualified Yices.Easy.Sugar as Y
> import qualified Yices.Easy.Build as Y

> import Solve

> data YicesBackend = YicesBackend
> instance Solver YicesBackend where
>  solve yices = solveYices yices

> solveYices :: (Ord v) => YicesBackend -> [Assertion v] -> IO (Maybe (M.Map v Value))
> solveYices yices assertions = do
>   let (keymap, query) = Y.runBuild $ flip execStateT M.empty $ (mapM_ buildQuery assertions)
>   let rmap = (M.fromList . map (\(x,y) -> (y,x)) . M.toList) keymap
>   mmodel <- Y.solve query
>   return $ case mmodel of
>      Y.Sat model -> Just $ M.map toValue $ M.mapKeys (rmap M.!) model
>      _           -> Nothing

> toValue :: Y.Value -> Value
> toValue (Y.ValInt i) = ValInt (fromIntegral i)
> toValue (Y.ValBool b) = ValBool b
> toValue (Y.ValBitvec bits) = ValBv (Bitvector (fromBits bits) (length bits))

> buildQuery :: (Ord v) => Expression v Bool -> StateT (M.Map v String) (Y.BuildT Identity) ()
> buildQuery e = buildExpression e >>= (lift . Y.assert)

> buildExpression :: (Ord v) => Expression v t -> StateT (M.Map v String) (Y.BuildT Identity) Y.Expr
> buildExpression (Not e) = liftM (Y.Not) (buildExpression e)
> buildExpression (BoolT be) = buildBooleanExpression be
> buildExpression (IntegerT ie) = buildIntegerExpression ie
> buildExpression (BitvectorT bve) = buildBitvectorExpression bve


> buildVarExpression declare var = do
>   vmap <- get
>   case M.lookup var vmap of
>     Nothing -> do
>       ident <- lift (Y.freshName "v_")
>       modify (M.insert var ident)
>       declare ident
>     Just ident -> return (Y.Var ident)

> buildBooleanExpression (VarB v) = buildVarExpression (\ident -> lift $ Y.declBool ident) v
> buildBooleanExpression (ConstB b) = return $ Y.LitBool b
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

> buildIntegerExpression (VarI v) = buildVarExpression (\ident -> lift $ Y.declInt ident) v
> buildIntegerExpression (ConstI i) = return $ Y.LitNum (Y.FromString (show i))
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

> buildBitvectorExpression (VarBv size v) = buildVarExpression (\ident -> lift $ Y.declBitvec size ident) v
> buildBitvectorExpression (ConstBv bv) = return $ Y.LitBitvec (Y.FromBits (integerToBits bv))
> buildBitvectorExpression (CmpBvU cmp e1 e2) = do
>   [ye1,ye2] <- mapM buildExpression [e1,e2]
>   return $ case cmp of
>     Eq   -> Y.BitCompare Y.Unsigned Y.Eq ye1 ye2
>     LtEq -> Y.BitCompare Y.Unsigned Y.Le ye1 ye2
>     Gt   -> Y.BitCompare Y.Unsigned Y.Gt ye1 ye2

Integer to bitvector, least-significant first

> integerToBits :: Bitvector -> [Y.Bit]
> integerToBits (Bitvector v size) = take size $ go v
>   where  go  n = lsb n : go (n `div` 2)
>          lsb n | n `mod` 2 == 1 = Y.B1
>                | otherwise      = Y.B0

> fromBits :: [Y.Bit] -> Integer
> fromBits = foldr (\x y -> toInt x + 2 * y) 0
>   where
>     toInt (Y.B0) = 0
>     toInt (Y.B1) = 1
