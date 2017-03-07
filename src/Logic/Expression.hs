
module Logic.Expression(
    -- * Datatypes
    Expr,
    -- * Constructors
    false,
    true,
    variable,
    and,
    xor,
    ands,
    xors,
    -- * Query
    isTrue,
    isFalse,
    isVariable,
    isDisjunction,
    isConjunction,
    ) where

import Prelude hiding (and)
-- FROM STACKAGE
import           Data.Vector(Vector)
import qualified Data.Vector as V
-- FROM THIS PACKAGE
import           Logic.Expression.Internal(Internal)
import qualified Logic.Expression.Internal as L

-------------------------------------------------------------------------------
-- DATA STRUCTURES
-------------------------------------------------------------------------------

{- |  The datatype Expression represents a finite polynomial over a the finite
field of boolean values (aka a boolean ring).

The expression datatype has been implemented as an opaque datatype and is
parameterized over the type of symbols used for identifiers.  The internal
encoding structure represents the proposition in as a set of integers, whose bits
represent the incidence of each identifier in a term.   The smart constructors
ensure that the internal encoding is always in algebraic normal form.
-}
data Expr a = EXPR [a] Internal deriving (Show)

instance (Eq a, Ord a) => Eq (Expr a) where
    (==) x y =
        let [EXPR _ x', EXPR _ y'] = appendNamespaces [x,y]
        in  x' == y'

instance (Ord a) => Ord (Expr a) where
    compare x y =
        let [EXPR _ x', EXPR _ y'] = appendNamespaces [x,y]
        in  compare x' y'

-- | /O(1)/ - Construct the Boolean literal False.
false :: Expr a
false = EXPR [] V.empty

-- | /O(1)/ - Construct the Boolean literal True.
true :: Expr a
true = EXPR [] (V.singleton 0)

variable :: a -> Expr a
variable a = EXPR [a] (V.singleton 1)

and :: (Ord a)=>Expr a -> Expr a -> Expr a
and = liftBinary L.and

xor :: (Ord a)=>Expr a -> Expr a -> Expr a
xor = liftBinary L.xor

xors :: (Ord a)=>[Expr a]->Expr a
xors = liftNary L.xors

ands :: (Ord a)=>[Expr a]->Expr a
ands = liftNary L.ands

-------------------------------------------------------------------------------
-- QUERY FUNCTIONS
------------------------------------------------------------------------------
isTrue :: (Ord a) => Expr a -> Bool
isTrue (EXPR _ x) = x==V.singleton 0

isFalse :: Expr a -> Bool
isFalse z@(EXPR _ x )= V.null x

isVariable :: Expr a -> Bool
isVariable (EXPR _ x) = let
   x0 = V.unsafeHead x
   in ( 1 == V.length x ) && ( (x0==1) || (0 == mod x0 2) )

isDisjunction :: Expr a -> Bool
isDisjunction (EXPR _ x) = V.length x > 1

isConjunction :: Expr a -> Bool
isConjunction (EXPR _ x) =
    let x0 = V.unsafeHead x
    in  ( x0 > 1 ) -- && ( 0 /= mod x0 2)

-------------------------------------------------------------------------------
-- UTILITIES
-------------------------------------------------------------------------------

{- Add the given set of identifiers to the namespace of an expression.   This
   function is called by the liftBinary and liftNary functions to ensure that
   the operands have consistent namespaces.
 -}
appendNamespace:: (Ord a) => [a] -> Expr a -> Expr a
appendNamespace [] x = x
appendNamespace newnames (EXPR oldnames ms) =
    EXPR names (V.map (rename oldnames names 1) ms)
    where
        names = unionNames oldnames newnames
        -- construct a term using the new namespace
        rename uus vvs n x = case vvs of
            [] -> x -- no new names to apply
            (v:vs) -> case uus of
                []     -> x
                (u:us) -> case u==v of
                    True -> rename us vs (2*n) x
                    False -> rename uus vs (2*n) (2*d*n + m)
            where (d,m) = Prelude.divMod x n
        {- merge to ordered lists of identifiers in linear time.-}
        unionNames [] [] = []
        unionNames xs [] = xs
        unionNames [] ys = ys
        unionNames xxs@(x:xs) yys@(y:ys)  =
            case compare x y of
                LT -> x:unionNames xs yys
                EQ -> x:unionNames xs ys
                GT -> y:unionNames xxs ys

-- | Join the namespaces of a list of expressions, Returning a list of the
-- mutually renamed expressions.
appendNamespaces :: (Ord a) => [Expr a] -> [Expr a]
appendNamespaces xxs = case (xxs) of
    []      -> []
    (x:[])  -> [x]
    (x:xs)   -> reverse (aux [x] xs)
    where
    aux zs@((EXPR vs _):_) yys = case yys of
        []      -> zs
        ((y@(EXPR us _)):ys) ->
            let y'@(EXPR us' _) = appendNamespace vs y
            in  case (us' == vs) of
                True  -> aux (y':zs) ys
                False -> aux (y':map (appendNamespace us) zs) ys
    aux _ _ = error "The unexpected happened"

-- | Given an binary logical operator on the internal representation, lift it
-- to the Expr type.
liftBinary :: (Ord a) => ( Internal -> Internal -> Internal )
   -> Expr a -> Expr a -> Expr a
{-# INLINE liftBinary #-}
liftBinary op x y =
    let [EXPR vs x', EXPR _ y'] = appendNamespaces [x,y]
    in  EXPR vs (x' `op` y')

liftNary :: (Ord a) => ([ Internal ] -> Internal )
   -> [ Expr a ] -> Expr a
liftNary f xs = case xs of
    [] -> EXPR [] (f [])
    _  -> let xs'@((EXPR vs _ ) : _ ) = appendNamespaces xs
          in  EXPR vs $ f $ fmap (\ (EXPR _ z) -> z) xs'
