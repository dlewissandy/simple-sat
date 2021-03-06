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
    isSat, interpretations, assign, identifiers,
    ) where

import qualified Data.Set as S
import           Data.Maybe
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
and p q = case V.null p of
    True -> V.empty
    _    -> case V.null q of
        True -> V.empty
        _    -> V.reverse (heapMul Nothing (V.empty) (V.reverse p) q)
    where
        -- Alternately (non-strictly) storing and retreiving elements
        -- in an intermediate heap.  Elements can be retrieved when
        -- either there are no more elements left to store, or when
        -- the element being stored is greater than the least element
        -- in the heap.
        --heapMul :: Maybe BitVec -> M.Map BitVec Int -> V.Vector BitVec -> V.Vector BitVec -> V.Vector BitVec
        {-# INLINE heapMul #-}
        heapMul z h xxs ys =
            if V.null xxs
                then flush h
                else case (Just x > z && P.not (isNothing z)) of
                    True -> case retrieve h of
                        Left (!a,z',h') -> a `V.cons` heapMul z' h' xxs ys
                        Right (z', h') -> heapMul z' h' xxs ys
                    False ->
                        let (z',h') = store h ys x
                        in  heapMul z' h' xs ys
             where x = V.unsafeHead xxs
                   xs = V.unsafeTail xxs
        -- Multiply each term in ys by x, storing the term products in the heap.
        -- update the least element
        store h ys !x =
            let h' = V.foldr (\y z ->
                    let m = y .|. x
                        -- multiplying a two monomials can be achieved by
                        -- bitwise or of their integer encodings
                    in  alter (\ zz -> case zz of
                            Nothing -> Just 1
                            Just cnt -> Just (cnt+1)) m z )  h ys
                --  find the new least element in the heap.   it should be
                -- either the least term in ys * x, or the previous least element
                z' = fst . V.unsafeHead $ h' -- O(log n)
            in  (Just z', h')

        -- O(log(n)) Retrieve the least element from the heap and update the
        -- least elem retrieve
        retrieve h =
            let (m,cnt) = V.unsafeHead h
                h' = V.unsafeTail h
                z' = if V.null h'
                        then Nothing else
                             Just . fst $ V.unsafeHead h' -- O(log(n))
            in  case (cnt `P.mod` 2) of
                    0 -> Right (z',h')
                    _ -> Left (m, z', h')
        -- O(n) Flush the elements from the heap.  Keep only the elements where
        -- the incidence is odd because (x `xor` x = false).
        flush h =V.map fst . (V.filter (\(_,cnt) -> cnt `P.mod` 2 == 1)) $ h

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

-- | O(log n) - insert, delete or modify an element in an ascending list of
-- key value pairs.  This function is used by "and" to store intermediate values
-- but is not exported from this module.
alter :: (Maybe Int -> Maybe Int) -> Integer -> V.Vector (Integer,Int) -> V.Vector (Integer,Int)
{-# INLINE alter #-}
alter f k0 vs = case V.null vs of
    -- Special case for the empty vector.   We know that the element wont be
    -- found, so we don't have to search.
    True -> case f Nothing of
        Just !v' -> V.singleton (k0,v')
        _       -> vs
    -- If the vector is not empty, then we need to search for an existing element
    -- with the specified monomial key and perform the desired alteration on that
    -- element.
    _    -> go 0 (V.length vs - 1)
    where
    {-# INLINE [0] go #-}
    go !l !h = case l==h of
        -- When the upper and lower bounds are equal, then our search is over.
        True  -> let (k,v) = vs `V.unsafeIndex` l
             -- does the found key, k, match the search key, k0.   If it does
             -- then alter the value stored at that location, otherwise,
             -- possibly add a new element
            in case compare k0 k of
                GT -> case f Nothing of
                    -- The search key is less than the found key.   Since we
                    -- are maintining the list in DESCENDING order of the keys,
                    -- we will either add the element after the found element
                    -- or do nothing.
                    Just v' -> let (ls,rs) = V.splitAt (l+1) vs
                               in  ls V.++ (k0,v') `V.cons` rs
                    _       -> vs
                EQ -> case f $ Just v of
                    Just v' -> let (ls,rs) = V.splitAt (l) vs
                               in  ls V.++ (k0,v') `V.cons` (V.tail rs)
                    Nothing -> let (ls,rs) = V.splitAt (l) vs
                               in  ls V.++ V.unsafeTail rs
                LT -> case f Nothing of
                    Just v' -> let (ls,rs) = V.splitAt (l) vs
                               in  ls V.++ (k0,v') `V.cons` rs
                    _       -> vs
        False ->
            let i = (l+h) `div` 2
            in case compare k0 (fst $ vs V.! i) of
                LT -> go l (max (i-1) l)
                EQ -> go i i
                GT -> go (min (i+1) h) h
