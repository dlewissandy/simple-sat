{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
module Logic.Expression.Internal(
    Internal,
    true, false,
    variable,
    xor, and, ands, xors
    ) where

import qualified Data.Vector as V
import Data.Bits hiding (xor)
import Prelude hiding (and,or)

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

-- | O(n) - construct the exclusive disjunction of two expressions
xor :: Internal -> Internal -> Internal
{-# INLINE xor #-}
xor p q = case V.null p of
    True -> q
    _    -> case V.null q of
        True -> p
        _    -> case compare x y of
            LT -> x `V.cons` xor (V.unsafeTail p) q
            GT -> y `V.cons` xor p (V.unsafeTail q)
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
