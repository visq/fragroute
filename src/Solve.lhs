> {-# LANGUAGE StandaloneDeriving, ScopedTypeVariables, GADTs, TypeFamilies, TypeSynonymInstances, FlexibleInstances #-}

A Non-Monadic interface to SAT/SMT/LP solvers
=============================================
  
> module Solve where

> import Control.Monad.State
> import qualified Data.Map as M

There are quite a few SAT, SMT and LP packages available on hackage, but many of them
have a monadic flavor. In this module we try to provide a clean abstraction layer
suitable for complex SAT/LP formulations, sticking to the design decisions outlined
below.

* Decision 1: We want a *pure*, *non-monadic* and simple interface, and believe that to this end,
  the performance overhead of deep embeddings is worth it.

* Decision 2: The most natural way to use variables in a non-monadic expression language is to allow
  arbitrary haskell values to identify variables, and establish a mapping for use in the solver
  using the standard Map moodule.

* Decision 3: We want a simple interface for running simple optimization and SAT problems.
  For example, solve should take a list of assertions with variable type v, and maybe
  return a solution of type ``Map v Value``.
  
Motivating Example
------------------

Here is one example from the modeling problem which motivated this module:

* Informal Specification:

The problem has the following integer variables: For each switch, direction and phase, there is an
input and an output port.

*  Formalization:

> {-
> data SwitchVar =  In  Phase Switch Direction
>                 | Out Phase Switch Direction deriving (Eq,Ord,Show,Read)
> instance Variable SwitchVar
> -}

* Informal Specification:

For each phase p, the following is true: Foreach switch ``s``, and each pair of distinct direction
``(d,d')``, either the output ports map to different signals, or one of the output ports is
inactive.

* Formalization:

> {-
> propertyOut :: Phase -> [Assertion SwitchVar]
> propertyOut p =
>   [ v =/= v' .||. v === inactive .||.  v' === inactive
>   | s <- switches
>   , d <- directions,  let v = var (Out p s d)
>   , d' <- directions, d' /= d, let v' = var (Out p s d')
>   ]
>   where inactive = integer 0
> -}


Modeling Basics
---------------

> type Assertion v = Expression v Bool

We try to avoid polymorphic data constructors as far as possible, as, in my opinion
they complicate writing the backend a lot.

> data Expression v t where
>   Not       :: Expression v Bool -> Expression v Bool
>   BoolT     :: BoolExpr v t -> Expression v t
>   IntegerT  :: IntegerExpr v t -> Expression v t
>   BitvectorT   :: BitvecExpr v t -> Expression v t
> deriving instance Show (Expression v t)

> data CmpOp = Eq | LtEq | Gt deriving (Eq,Ord,Show,Read)
> data FoldOp = Sum | Product deriving (Eq,Ord,Show,Read)

> data BoolExpr v t where
>   VarB   :: (Variable v) => v -> BoolExpr v Bool
>   ConstB :: Bool -> BoolExpr v Bool
>   CmpB   :: CmpOp -> Expression v Bool -> Expression v Bool -> BoolExpr v Bool
>   FoldB  :: FoldOp -> [Expression v Bool] -> BoolExpr v Bool

> deriving instance Show (BoolExpr v t)

> data IntegerExpr v t where
>   VarI   :: (Variable v) => v -> IntegerExpr v Integer
>   ConstI :: Integer -> IntegerExpr v Integer
>   CmpI   :: CmpOp  -> Expression v Integer -> Expression v Integer -> IntegerExpr v Bool
>   FoldI  :: FoldOp -> [Expression v Integer] -> IntegerExpr v Integer

> deriving instance Show (IntegerExpr v t)

Data type for bitvectors

> data Bitvector = Bitvector Integer {- unsigned value -} Int {- bitwidth -} 
>                  deriving (Eq, Ord, Show, Read)

> bvToInteger :: Bool -> Bitvector -> Integer
> bvToInteger False (Bitvector v _) = v

> data BitvecExpr v t where
>   VarBv   :: (Variable v) => Int -> v -> BitvecExpr v Bitvector
>   ConstBv :: Bitvector -> BitvecExpr v Bitvector
>   CmpBvU  :: CmpOp  -> Expression v Bitvector -> Expression v Bitvector -> BitvecExpr v Bool
>   CmpBvS  :: CmpOp  -> Expression v Bitvector -> Expression v Bitvector -> BitvecExpr v Bool
>   FoldBv  :: FoldOp -> [Expression v Bitvector] -> BitvecExpr v Bitvector

> deriving instance Show (BitvecExpr v t)

> class (Show v, Ord v) => Variable v

Types and Constants
-------------------

> data Constant =  ConstInt Integer | ConstBool Bool | ConstBitvector Bitvector

> data Type = TyInt | TyBool | TyBv Int deriving (Eq,Ord,Show,Read)

> data Value =
>     ValBool Bool
>   | ValInt  Integer
>   | ValBv   Bitvector
>    deriving (Show,Read,Eq,Ord)

> fromIntValue :: Value -> Integer
> fromIntValue v = case v of ValInt l -> fromIntegral l ; _ -> error ( "fromIntValue: " ++ show v )

> fromBvValue :: Value -> Bitvector
> fromBvValue v = case v of ValBv bv  -> bv ; _ -> error ( "fromBvValue: " ++ show v )

Solver Interface
----------------

> class Solver s where
>   solve :: (Variable v) => s -> [Assertion v] -> IO (Maybe (M.Map v Value))


Language for Equality
---------------------

> class Eq' t where
>   (===) :: Expression v t -> Expression v t -> Expression v Bool
>   (=/=) :: Expression v t -> Expression v t -> Expression v Bool
>   (=/=) e1 e2 = Not (e1 === e2)
> infix 4 ===,=/=

> class Ord' t where
>   (.>.) :: Expression v t -> Expression v t -> Expression v Bool

Language for Booleans
---------------------

> boolVar :: (Variable v) => v -> Expression v Bool
> boolVar = BoolT . VarB

> instance Eq' Bool    where (===) b1 b2 = BoolT    (CmpB Eq b1 b2)

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

> true :: Expression v Bool
> true = BoolT $ ConstB True

> false :: Expression v Bool
> false = BoolT $ ConstB False

Language for Numeric Types
--------------------------

> sum' :: [Expression v Integer] -> Expression v Integer
> sum' = IntegerT . FoldI Sum

> product' :: [Expression v Integer] -> Expression v Integer
> product' = IntegerT . FoldI Product

Language for Integral Types
---------------------------

> class (Eq' t) => Integral' t where
>  integral ::  (Integral n) => n -> Expression v t

Language for Unbounded Integers
-------------------------------

> intVar :: (Variable v) => v -> Expression v Integer
> intVar = IntegerT . VarI

> instance Eq' Integer where (===) i1 i2 = IntegerT (CmpI Eq i1 i2)
> instance Ord' Integer where (.>.) i1 i2 = IntegerT (CmpI Gt i1 i2)
> instance Integral' Integer where integral = integer . fromIntegral

> integer :: Integer -> Expression v Integer
> integer = IntegerT . ConstI

Language for Bounded Integers
-----------------------------

> bvVar :: (Variable v) => Int -> v -> Expression v Bitvector
> bvVar width = BitvectorT . VarBv width

> instance Eq' Bitvector where (===) i1 i2  = BitvectorT (CmpBvU Eq i1 i2)
> instance Ord' Bitvector where (.>.) i1 i2 = BitvectorT (CmpBvU Gt i1 i2)

> bitvector :: Int -> Integer -> Expression v Bitvector
> bitvector sz n | n < 0     = error "construction of negative bitvectors is not supported (error prone)"
>                | otherwise = BitvectorT $ ConstBv $ Bitvector n sz

Utilities
---------

Number of bits needed to represent an unsigned integer

> bitWidthUnsigned :: Integer -> Int
> bitWidthUnsigned n | n < 0     = error "bitWidthUnsigned: negative"
>                    | otherwise = go n 1
>  where go 0 l = l
>        go 1 l = l
>        go k l = go (k `div` 2) (l + 1)

Backends
--------

See

* `SolveYices.lhs <SolveYices.html>`_ for the yices-easy backend.


Simple Example
--------------

> instance Variable String

> demo =
>     [ true
>     , true
>     , boolVar "b1"
>     , Not (boolVar "b2")
>     , intVar "x" =/= integer 0 
>     , intVar "y" =/= (intVar "z" :: Expression String Integer)
>     , sum' [ intVar "x" , intVar "z" ] === integer 42
>     , product' [intVar "x", integer 4 ] === integer 16
>     , boolVar "b3" .||. boolVar "b4" .||. boolVar "b5"
>     ]
