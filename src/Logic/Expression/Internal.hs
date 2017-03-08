{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TupleSections #-}
module Logic.Expression.Internal(
    Internal,
    true, false,
    variable,
    xor, and, ands, xors,
    -- Satisfiability
    isSat, interpretations, assign,
    ) where

import           Data.Set(Set)
import qualified Data.Set as S
import qualified Data.Vector as V
import           Data.Bits hiding (xor)
import qualified Data.Bits as B
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
isSat = not . S.null . interpretations

{- | Replace all occurances of a set of variables with a boolean literal.  -}
assign :: Internal -> Integer -> Bool ->  Internal
assign expr vars True  =
     V.foldr (xor . V.singleton) false $ V.map (\ x -> (x .&. vars) `B.xor` x)  expr
assign expr vars False =
     V.filter ((==0) . (.&. vars)) expr


{- | O(2^n) Given an expression, p, obtain a list xs of expressions such that
@or xs == p@ and for each x in xs then @x and p@ is true.  This function uses
a modified DPLL algorithm.   -}
interpretations :: [Internal] -> Set (Set (Int,Bool))
interpretations exprs0 = go [([],exprs0)]
    where
    -- | Find the satsifying assignments by backtracking.   The is a list of
    -- variable assignments and a partially reduced set of logical expressions.
    go :: [([(Int,Bool)],[Internal])] -> Set (Set (Int,Bool))
    go xxs =
        case xxs of
            []             -> S.empty
            ((psol,[]):ss) -> S.insert (S.fromList psol) $ go ss
            ((psol,exprss@(expr:exprs)):ss) -> case any (==false) exprss of
                True -> go ss
                _    -> case true == expr of
                    True -> go $ ( psol, exprs ):ss
                    _    -> go $ (next psol exprss) ++ ss
         where
         next _ [] = error "Unexpected empty list of expressions"
         next psol exprss@(expr:exprs) =
             case V.length expr of
             -- When there is only one term left, it must consist of a
             -- single powerproduct (we eliminated the case when it was true
             -- prior to calling next.  all the variables in the power product
             -- must be true.
             1 -> [((fmap ((,True)) idents) ++ psol
                  ,  fmap (\z->assign z (V.unsafeHead expr) True) exprs) ]
             -- When there is more than one term left, we must check
             -- to check the case where all the variables in the term are
             -- True, and then individually the cases where each variable is
             -- false.
             _ -> [ ((i0,False):psol
                  , fmap (\z->assign z (2^i0) False) exprss ) ] ++
                  [ ((i0,True):psol
                  , fmap (\z->assign z (2^i0) True) exprss ) ]
             where
             idents@(i0:_) = identifiers expr

--------------------------------------------------------------------------------
-- Bound variables
--------------------------------------------------------------------------------
{- | O(n).  Return an integer whose bits represent the indicies of the bound
variables an expression. -}
variables :: Internal -> Integer
variables = V.foldr (.|.) 0

{- | O(n).  Return a list whose elements are the indicies of the bound variables
in an expression. -}
identifiers :: Internal -> [Int]
identifiers expr =
    let vars = variables expr
    in  [ident | ident <- takeWhile (\i->vars>=2^i) [0..], testBit vars ident]
