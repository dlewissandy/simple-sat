{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
module Logic.Expression.Internal(
    Internal,
    true, false,
    variable,
    xor, and, ands, xors, or, equals, implies, not, ors,
    -- Satisfiability
    isSat, interpretations, assign, identifiers
    ) where

import qualified Data.Set as S
import qualified Data.Vector as V
import           Data.Bits hiding (xor)
import qualified Data.Bits as B
import           Prelude hiding (and,or,not)
import qualified Prelude as P

{- | The internal representation of a logical expression encodes expresions
in algebraic normal form as a vector of integers.   Each element in the Vector
represents a distinct term in an exclusive disjunction clause.   Each term is
encodes a conjunction of variables as an integer, indicating the presence of
variable i as a factor by setting the ith bit in the integer.  The literal
True is encoded as any vector consisting of all zeros, while false is encoded
as the empty vector. -}
type Internal = V.Vector Integer

-- | O(1) - construct the expression representing logical falsity.
false :: Internal
{-# INLINE false #-}
false = V.empty

-- | O(1) - construct the expression representing logical truth.
true :: Internal
{-# INLINE true #-}
true = V.singleton 0

-- | O(1) - construct an expression representing a logical variable given the
-- integer identifier for the symbol.
variable :: Int -> Internal
{-# INLINE variable #-}
variable = V.singleton . (2^)

-- | O(n^2) - construct the disjunction of two expressions.  Terms will
-- be arranged in descending term order.
or :: Internal -> Internal -> Internal
{-# INLINE or #-}
or p q = (p `and` q) `xor` p `xor` q

-- | O(n) - construct the material equivalence of two expressions.  Terms will
-- be arranged in descending term order.
equals :: Internal -> Internal -> Internal
{-# INLINE equals #-}
equals p q = not (p `xor` q)

-- | O(n^2) - construct the material equivalence of two expressions.  Terms will
-- be arranged in descending term order.
implies :: Internal -> Internal -> Internal
{-# INLINE implies #-}
implies p q = (p `and` q) `xor` p `xor` true

-- | O(n) - construct the logical negation of an expression.  Terms will
-- be arranged in descending term order.
not :: Internal -> Internal
{-# INLINE not #-}
not p = p `xor` true

-- | O(n^2) - construct the n-ary disjunctin of a list of expressions.  Terms
-- will be expressed in descending term order.
ors :: [ Internal ] -> Internal
{-# INLINE ors #-}
ors = foldr or false

-- | O(n) - construct the exclusive disjunction of two expressions.  Terms will
-- be arranged in descending term order.
xor :: Internal -> Internal -> Internal
{-# INLINE xor #-}
xor p q = case V.null p of
    True -> q
    _    -> case V.null q of
        True -> p
        _    -> case compare x y of
            GT -> x `V.cons` xor (V.unsafeTail p) q
            LT -> y `V.cons` xor p (V.unsafeTail q)
            EQ -> xor (V.unsafeTail p) (V.unsafeTail q)
    where
    x = V.unsafeHead p
    y = V.unsafeHead q

-- | O(n^2) - construct the n-ary exclusive disjunction of a list of expressions
xors :: [Internal] -> Internal
{-# INLINE xors #-}
xors = foldr xor false

-- | O(n^2) - construct the logical conjunction of two expressions
and :: Internal -> Internal -> Internal
{-# INLINE and #-}
and p q = foldr xor false [ V.singleton $ (V.unsafeIndex p i) .|.  (V.unsafeIndex q j) | i<-[0..V.length p - 1],j<-[0..V.length q -1] ]

-- | O(n^3) - construct the n-ary logical conjunction of a list of expressions
ands :: [Internal] -> Internal
{-# INLINE ands #-}
ands = foldr and true

--------------------------------------------------------------------------------
-- BOOLEAN SATISFIABILITY
--------------------------------------------------------------------------------

{- | O(2^n). Test for satisfiability. -}
isSat :: [ Internal ] -> Bool
isSat = P.not . S.null . interpretations

{- | Replace all occurances of a set of variables with a boolean literal.  -}
assign :: Internal -> Integer -> Bool ->  Internal
assign expr vars True  =
     V.foldr (xor . V.singleton) false $ V.map (\ x -> (x .&. vars) `B.xor` x)  expr
assign expr vars False =
     V.filter ((==0) . (.&. vars)) expr


{- | O(2^n) Given an expression, p, obtain a list xs of expressions such that
@or xs == p@ and for each x in xs then @x and p@ is true.  This function uses
the DPLL algorithm.   -}
interpretations :: [Internal] -> S.Set (S.Set (Int,Bool))
interpretations (S.fromList->exprs0 ) = aux exprs0
    where
        aux :: S.Set Internal -> S.Set (S.Set (Int,Bool))
        aux exprs = if S.null exprs then S.singleton S.empty
            else case V.length expr of
                0 -> S.empty  -- The expression is False.  Nothing will satisfy it.
                1 -> -- If there is only one term, then all the identifiers in
                    -- it must be true.
                     let poss = S.map (assumeMany (V.unsafeHead expr)) exprs'
                         zs  = S.fromList $ fmap (,True) $ identifiers expr
                     in  S.map (S.union zs) $ aux poss
                _ -> let ident = getIdent expr
                         poss = S.map (assume ident True)  exprs
                         negs = S.map (assume ident False) exprs
                     in  S.map (S.insert (ident,False)) (aux negs)
                         `S.union`
                         S.map (S.insert (ident,True))  (aux poss)
            where (expr,exprs') = S.deleteFindMin exprs
        -- find an identifier to test.
        getIdent :: Internal -> Int
        getIdent x = go (V.unsafeHead x) 0
            where
            go n i = if n `testBit` i then i else go n (i+1)


{- | O(n) Substitute a boolean literal for all occurances of a variable within
    a proposition.  -}
assume :: Int -> Bool -> Internal -> Internal
assume !ident !b expr = if b
    then foldr xor false (fmap (V.singleton.(`clearBit` ident)) expr)
    else V.filter (P.not.(`testBit` ident)) expr

{- | O(n) Set a bunch of variables to true at the same time.  This is faster
than setting them individually with assume.  -}
assumeMany :: Integer -> Internal -> Internal
assumeMany !idents expr =
    foldr xor false (fmap (V.singleton.(.&. complement idents)) expr)

--------------------------------------------------------------------------------
-- Bound variables
--------------------------------------------------------------------------------
{- | O(n).  Return an integer whose bits represent the indicies of the bound
variables an expression. -}
variables :: Internal -> Integer
variables = V.foldr (.|.) 0

{- | O(n).  Return a list whose elements are the indicies of the bound variables
in an expression.  The list will be in ascending order. -}
identifiers :: Internal -> [Int]
identifiers expr =
    let vars = variables expr
    in  [ident | ident <- takeWhile (\i->vars>=2^i) [0..], testBit vars ident]
