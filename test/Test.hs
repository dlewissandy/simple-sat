{-# LANGUAGE FlexibleInstances #-}
module Main(main) where

import qualified Prelude
import Prelude hiding (and)
import Control.Monad
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Logic.Expression

-- | The entry point for bench testing
main :: IO ()
main = defaultMain alltests

alltests :: TestTree
alltests = testGroup "simple-sat" [
    -- Tests for literals.  Verify that the predicate isTrue
    testGroup "true" [
        testCase "isTrue(true)"  $ assertBool "" $ isTrue t,
        testCase "isFalse(true)" $ assertBool "" $ not $ isFalse t
        ],
    -- Verify that the predicate false returns true only for statements that
    -- are false.
    testGroup "false" [
        testCase "isFalse(false)" $ assertBool "" $ isFalse f,
        testCase "isTrue(false)"  $ assertBool "" $ not $ isTrue f
        ],
    testGroup "variable" [],
    -- tests for boolean operators
    testGroup "xor" [
        testCase "xor(true,true)" $ assertBool "" $ isFalse $ t `xor` t,
        testCase "xor(false,true)" $ assertBool "" $ isTrue $ f `xor` t,
        testCase "xor(true,false)" $ assertBool "" $ isTrue $ t `xor` f,
        testCase "xor(false,false)" $ assertBool "" $ isFalse $ f `xor` f,
        isAssociative "isAssociative" xor,
        isCommutative "isCommutative" xor,
        isNeutralElementOf "NeutralElem" false xor,
        areInverseElementsOf "Inverses" id xor false Nothing
        ],
    testGroup "xors" [
        isFold "isFold" xors xor false
        ],
    testGroup "and" [
        testCase "and(true,true)" $ assertBool "" $ isTrue $ t `and` t,
        testCase "and(false,true)" $ assertBool "" $ isFalse $ f `and` t,
        testCase "and(true,false)" $ assertBool "" $ isFalse $ t `and` f,
        testCase "and(false,false)" $ assertBool "" $ isFalse $ f `and` f,
        isAssociative "isAssociative" and,
        isCommutative "isCommutative" and,
        isNeutralElementOf "NeutralElem" true and,
        distributesOver "distributes" and xor,
        isZeroElementOf "zeroElem" false and
        ],
    testGroup "ands" [
        isFold "isFold" ands and true
        ],
    testGroup "isSat" satTests,
    testGroup "interpretations" interpTests
    ]
    where
    t :: Expr Char
    t = true
    f :: Expr Char
    f = false
    -- Verify the semantics of isSat.   A list of expressions is satisfyiable
    -- if and only if there is some non-empty set of interpretations for the
    -- bound variables.
    satTests :: [ TestTree ]
    satTests = [
        testCase "isSat([true])" $ assertBool "" $ isSat [t] == True,
        testCase "isSat([false])" $ assertBool "" $ isSat [f] == False,
        testProperty "isSat<=>not.null.interpretations" $
           forAll (listOf arbitrary :: Gen [Expr Char]) $ \ xs ->
               (isSat xs) == (not $ null $ interpretations xs)
        ]
    -- | Verify that the naive implementation of the sat solver and the actual
    -- sat solver find the same interpretations.
    interpTests :: [ TestTree ]
    interpTests = [
        testProperty "areSolutions" $
           forAll (listOf arbitrary :: Gen [Expr Char]) $ \ xs ->
              let xs' = appendNamespaces xs
                  zs  = interpretations xs'
              in  if (all (\ z -> isSolution z xs' ) zs)
                     then True
                     else error $ "assign (interpretations xs) xs="++show (fmap (\z ->assign z xs') zs) ++
                                  "\n interpretations xs = "++show zs
        ]

isAssociative :: String -> (Expr Char -> Expr Char -> Expr Char) -> TestTree
isAssociative testname op = testProperty testname $
    forAll arbitrary $ \ x ->
    forAll arbitrary $ \ y ->
    forAll arbitrary $ \ z ->
        x `op` (y `op` z) == (x `op` y) `op` z

isCommutative :: String -> (Expr Char -> Expr Char -> Expr Char) ->  TestTree
isCommutative testname op = testProperty testname $
    forAll arbitrary $ \ x ->
    forAll arbitrary $ \ y ->
        x `op` y == y `op` x

isNeutralElementOf :: String -> Expr Char -> (Expr Char -> Expr Char -> Expr Char) ->  TestTree
isNeutralElementOf testname z op = testProperty testname $
    forAll arbitrary $ \ x -> z `op` x == x

areInverseElementsOf :: String -> (Expr Char -> Expr Char) -> (Expr Char -> Expr Char -> Expr Char) -> Expr Char -> Maybe (Expr Char) -> TestTree
areInverseElementsOf testname inv op neutral zero = testProperty testname $
    forAll (arbitrary `suchThat` ((/=zero).Just)) $ \ x ->
            x `op` (inv x) == neutral

distributesOver :: String -> (Expr Char -> Expr Char -> Expr Char) -> (Expr Char -> Expr Char -> Expr Char) -> TestTree
distributesOver testname times plus = testProperty testname $
    forAll arbitrary $ \ x ->
    forAll arbitrary $ \ y ->
    forAll arbitrary $ \ z ->
       x `times` (y `plus` z) == (x `times` y) `plus` (x `times` z)

isZeroElementOf :: String -> Expr Char -> (Expr Char -> Expr Char -> Expr Char) -> TestTree
isZeroElementOf testname zero op = testProperty testname $
    forAll arbitrary $ \ x ->  x `op` zero == zero

isFold :: (Show a, Eq a, Arbitrary a) => String -> ([Expr Char] -> a) -> (Expr Char -> a -> a ) -> a -> TestTree
isFold testname op f b = testProperty testname $
    forAll (listOf arbitrary) $ \ xs -> case xs of
        []      -> op xs == b
        (x:xs') -> op xs == f x (op xs')


{- Build an arbitrary proposition with up to 6 variables -}
instance Arbitrary (Expr Char) where
    arbitrary = sized arbitrary'
        where
            arbitrary' 0 = oneof [return true, return false]
            arbitrary' n = oneof [
               aLiteral, aRef, aAny n, aAll n]
            aLiteral   = oneof [return true, return false]
            aRef       = liftM variable (elements ['A'..'F'])
            aAny n     = liftM xors (subs n)
            aAll n     = liftM ands (subs n)
            subs n = liftM id (vectorOf (n `quot` 2) (arbitrary' (n `div` 2)))
