-- | This module contains the benchmark test to quantify the time
-- performance of the simple-sat library functions.
module Main( main ) where

import Prelude hiding (and,or,not)
import Criterion.Main
-- | This package
import Logic.Expression

-- Run all the benchmark tests
main :: IO ()
main = defaultMain [ interpretationBenchs [1..10] ]

-- | Benchmark interpretations
interpretationBenchs :: [Int] -> Benchmark
interpretationBenchs ns = bgroup "interpretations" [ nQueensBench n | n<-ns  ]

-- | Benchmark computing the interpretations of the nQueens puzzle.
nQueensBench :: Int -> Benchmark
nQueensBench n = bench ("nQueens("++show n++")") $ nf (interpretations . nQueens) n

-- | Construct a list of expressions that are true if and only if the
-- assignment is a solution to the n-queens problem.   Specifically, given an
-- NxN chess board, how can you place N queens on the board such that none of
-- them share the same row (rank), column (file), or diagonal.
nQueens :: Int -> [Expr String]
nQueens n = rankRules ++ fileRules ++ lDiagRules ++ rDiagRules
    where
    files = [1..n]
    ranks = [1..n]
    var (r,f) = variable $ (['a'..'z']!!(f-1)):show r
    -- rank rule - there must be exactly one queen on each rank
    rankRules = [ rankRule r | r<-ranks ]
    rankRule r = (xors [ ands (var (r,f):[ not $ var (r,f') | f'<-files, f'/=f ]) | f<-files ]) `equals` true
    -- file rule - there must be exactly one queen on each file
    fileRules = [ fileRule f | f<-files ]
    fileRule f = (xors [ ands (var(r,f):[ not $ var (r',f) | r'<-ranks, r'/=r ]) | r<-ranks ]) `equals` true
    -- right Diagonal Rules - there is at most one queen on each right diagonal
    rDiagRules  = [ (rDiagRule c) `equals` false | c<-[-(n-2) .. (n-2)]]
    rDiagRule c = ors [var (f+c,f) `and` (ors [var (f'+c,f') | f'<-files,f'>f,c+f'<=n,c+f'>0]) | f<-files, f+c<=n, c+f>0]
    -- right Diagonal Rules - there is at most one queen on each left diagonal
    lDiagRules  = [ (lDiagRule c) `equals` false | c<-[3 .. 2*n-1]]
    lDiagRule c = ors [ var (c-f,f) `and` (ors [var (c-f',f') | f'<-files,f'>f,c-f'<=n,c-f'>0]) | f<-files, c-f<=n, c-f>0]
