
module Logic.Expression(
    -- * Datatypes
    Expr,
    -- * Constructors
    false,
    true,
    variable,
    and,
    xor,
    or,
    implies,
    equals,
    not,
    ands,
    xors,
    -- * Query
    isTrue,
    isFalse,
    isVariable,
    isDisjunction,
    isConjunction,
    -- * Satisfiability
    isSat, interpretations, assign, isSolution,
    -- * Utilities
    appendNamespaces, fromAST
    ) where

import qualified Prelude as P
import Prelude hiding (and,or,not)
-- FROM STACKAGE
import qualified Data.Set as S
import qualified Data.Vector as V
import           Data.List(partition)
-- FROM THIS PACKAGE
import           Logic.Expression.Internal(Internal)
import qualified Logic.Expression.Internal as L
import           Logic.Syntax

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

-- | /O(1)/ - Construct a variable from the given symbol.
variable :: a -> Expr a
variable a = EXPR [a] (V.singleton 1)

-- | /O(n^2)/ - Construct an expression representing the binary conjunction of
-- two expressions.
and :: (Ord a)=>Expr a -> Expr a -> Expr a
and = liftBinary L.and

-- | /O(n)/ - Construct an expression representing the binary exclusive
-- disjunction of two expressions.
xor :: (Ord a)=>Expr a -> Expr a -> Expr a
xor = liftBinary L.xor

-- | Construct an expression representing the n-ary exclusive disjunction of
-- a list of expressions.
or :: (Ord a)=>Expr a -> Expr a->Expr a
or = liftBinary L.or

-- | Construct an expression representing the n-ary exclusive disjunction of
-- a list of expressions.
implies :: (Ord a)=>Expr a -> Expr a ->Expr a
implies = liftBinary L.implies

-- | Construct an expression representing the n-ary exclusive disjunction of
-- a list of expressions.
equals :: (Ord a)=>Expr a -> Expr a ->Expr a
equals = liftBinary L.equals

-- | Construct an expression representing the n-ary exclusive disjunction of
-- a list of expressions.
not :: (Ord a)=>Expr a ->Expr a
not = liftUnary L.not

-- | /O(m*n) - Construct an expression representing the n-ary exclusive
-- disjunction of a list of expressions.
xors :: (Ord a)=>[Expr a]->Expr a
xors = liftNary L.xors


-- | /O(m*n^2) - Construct an expression representing the n-ary conjunction of
-- a list of expressions.
ands :: (Ord a)=>[Expr a]->Expr a
ands = liftNary L.ands

-------------------------------------------------------------------------------
-- QUERY FUNCTIONS
------------------------------------------------------------------------------
-- | O(1) - test for logical truth.   Returns True if and only if the
-- Expression is the boolean literal True.
isTrue :: (Ord a) => Expr a -> Bool
isTrue (EXPR _ x) = x==V.singleton 0

-- | O(1) - test for logical falsity.   Returns True if and only if the
-- Expression is the boolean literal False.
isFalse :: Expr a -> Bool
isFalse (EXPR _ x )= V.null x

-- | O(1) - Returns True if and only if the
-- Expression consists of a single variable.
isVariable :: Expr a -> Bool
isVariable (EXPR _ x) = let
   x0 = V.unsafeHead x
   in ( 1 == V.length x ) && ( (x0==1) || (0 == mod x0 2) )

-- | O(1) - Returns True if and only if the Expression is an exclusive
-- disjunction of two or more terms.
isDisjunction :: Expr a -> Bool
isDisjunction (EXPR _ x) = V.length x > 1

-- | O(1) - Returns True if and only if the expression is a conjunction
-- of two or more variables.
isConjunction :: Expr a -> Bool
isConjunction (EXPR _ x) =
    let x0 = V.unsafeHead x
    in  (1 == V.length x) && ( x0 > 1 ) && ( 0 /= mod x0 2)

-------------------------------------------------------------------------------
-- SATISFIABILITY
-------------------------------------------------------------------------------
{- | O(2^n).  Test for satisfiability.  A proposition is satisifiable if
    there is an assignment of variables which makes it "true.   -}
isSat :: (Ord a) => [ Expr a ] -> Bool
isSat  = L.isSat . fmap (\ ( EXPR _ xs) -> xs ) . appendNamespaces

{- | O(n). Replace all the occurances of a given variable with a boolean
literal. -}
assign :: (Ord a) => [(a,Bool)] -> [ Expr a ] -> [ Expr a ]
assign binds exprs = case exprs of
    [] -> []        -- assignment to a trivial equationset
    ((EXPR vars _ ):_)  -> case binds of
        [] -> exprs -- trivial assignments.
        _  ->
            -- partition the list into variables that are to be assigned truth
            -- and falsehood.  Then create a single monomial (power product)
            -- of the partitioned variables.
            let (ts,fs) = partition snd binds
                (EXPR _ tz) = ands [ appendNamespace vars $ variable t | (t,_)<- ts ]
                (EXPR _ fz) = ands [ appendNamespace vars $ variable f | (f,_)<- fs ]
            -- Call the internal routine for assignment of those values
            in  fmap (\ (EXPR _ x) ->
                   EXPR vars $ L.assign (L.assign x (V.unsafeHead fz) False) (V.unsafeHead tz) True) exprs

{- | O(2^n).  Obtain a unique (up to term ordering)
set of expressions for which the given expression
is true.  The set of interpretations must have the
property that @ors (interpretations expr) `implies`
expr@ -}
interpretations :: (Ord a) => [Expr a] -> [[(a,Bool)]]
interpretations [] = [[]]
interpretations xs =
    let xs'@((EXPR vs _ ):_) = appendNamespaces xs
        zs = fmap (\ (EXPR _ a) -> a) xs'
    in  fmap (fmap (\ (i,b)->(vs!!i,b) ) . S.toList ) (S.toList $ L.interpretations zs)

-- | Test if a given set of assignments is a solution
isSolution :: (Ord a)=>[(a,Bool)] ->[Expr a] -> Bool
isSolution binds = all isTrue . assign binds

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

-- | Given an n-ary logical operator on the internal representation, lift it
-- to the Expr type.
liftNary :: (Ord a) => ([ Internal ] -> Internal )
   -> [ Expr a ] -> Expr a
liftNary f xs = case xs of
    [] -> EXPR [] (f [])
    _  -> let xs'@((EXPR vs _ ) : _ ) = appendNamespaces xs
          in  EXPR vs $ f $ fmap (\ (EXPR _ z) -> z) xs'

-- | Given an unary logical operator on the internal representation, lift it
-- to the Expr type.
liftUnary :: (Ord a) => (Internal -> Internal )
   -> Expr a -> Expr a
liftUnary f (EXPR vs e) = EXPR vs $ f e

fromAST :: AST -> Expr String
fromAST (LIT b) = if b==1 then true else false
fromAST (VAR s) = variable s
fromAST (NOT e) = (fromAST e) `xor` true
fromAST (BINOP XOR x y) = (fromAST x) `xor` (fromAST y)
fromAST (BINOP AND x y) = (fromAST x) `and` (fromAST y)
fromAST (BINOP OR  x y) = (fromAST x) `or` (fromAST y)
fromAST (BINOP IMPLIES x y) = (fromAST x) `implies` (fromAST y)
fromAST (BINOP EQUALS x y) = (fromAST x) `equals` (fromAST y)
