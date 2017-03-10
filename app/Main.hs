{-# LANGUAGE RecordWildCards #-}
module Main(main) where

import Logic.Syntax
import Logic.Expression
import Options.Applicative
import Data.Semigroup ((<>))

data Opts = OPTS
  { fpath  :: String
  , showsyntax  :: Bool
  , showanf :: Bool
  , showsolution :: Bool }

opts :: ParserInfo Opts
opts = info (oparse <**> helper)
  ( fullDesc
 <> progDesc "Use the simple-sat solver to process a logic file"
 <> header "simple-sat - Copyright 2017" )

oparse :: Parser Opts
oparse = OPTS
      <$> strOption
          ( long "input"
         <> short 'i'
         <> metavar "file"
         <> value "test.logic"
         <> showDefault
         <> help "Input logic file" )
      <*> switch
          ( long "show-syntax"
         <> short 's'
         <> help "output the parser results" )
      <*> switch
            ( long "show-normal-form"
           <> short 'n'
           <> help "output the algebraic normal form" )
      <*> switch
            ( long "no-show-solutions"
           <> short 'z'
           <> help "Show the interpretations for the model" )


main :: IO ()
main = do
    OPTS{..} <- execParser opts
    ast <- parseFile fpath
    let anf = appendNamespaces $ fmap fromAST ast
        soln = interpretations anf
    case showsyntax of
        True -> do putStrLn "------- SYNTAX --------- "
                   _ <- mapM print ast
                   return ()
        False -> return ()
    case showanf of
        True -> do putStrLn "--------- ANF ----------"
                   _ <- mapM print anf
                   return ()
        _ -> return ()
    case showsolution of
        False -> do putStrLn "--- INTERPRETATIONS ----"
                    print soln
        True -> return ()
