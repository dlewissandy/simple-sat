{-# LANGUAGE OverloadedStrings #-}
module Logic.Syntax( AST(..), Op(..), parseFile, expr ) where

import Data.Attoparsec.Text
import Control.Applicative
import Data.Text as Text
import Data.Text.IO as TIO

data AST
  = LIT Int
  | VAR String
  | NOT AST
  | BINOP Op AST AST
  deriving Show

data Op = AND | OR | XOR | IMPLIES | EQUALS deriving Show

parseFile :: String -> IO [AST]
parseFile fpath = do
    raw <- TIO.readFile fpath
    case parseOnly (many (expr <* (skipSpace >> char ';'))) raw of
      Left str -> error $ "Parsing file failed: "++ str
      Right ast -> return ast

int :: Parser AST
int = do
  skipSpace
  n <- char '0' <|> char '1'
  return $ LIT $ read [n]

neg :: Parser AST
neg = skipSpace >> char '~' >> ( int <|> var <|> parens expr ) >>= return . NOT

parens :: Parser a -> Parser a
parens p = do
    skipSpace
    _ <- char '('
    x<-p
    skipSpace
    _ <- char ')'
    return x

var :: Parser AST
var = do
    skipSpace
    c <- letter
    s <- many' ( letter <|> digit <|> char '_')
    return $ VAR (c:s)

chainl1 :: Parser a -> Parser (a->a->a) -> Parser a
chainl1 p op = do { x<- p; f <- op ; y <- p ; rest (f x y) }
    where
    rest x = do{f <- op;y<-p;rest (f x y)} <|> return x

expr :: Parser AST
expr = choice [ term `chainl1` equals
              , term `chainl1` implies
              , term `chainl1` orop
              , term `chainl1` addop] <|> term

term :: Parser AST
term = factor `chainl1` mulop <|> factor

factor :: Parser AST
factor = int <|> var <|> neg <|> parens expr

infixOp :: Text -> (a -> a -> a) -> Parser (a -> a -> a)
infixOp x f = skipSpace >> string x >> return f

addop :: Parser (AST -> AST -> AST)
addop = infixOp "+" (BINOP XOR)

mulop :: Parser (AST -> AST -> AST)
mulop = infixOp "*" (BINOP AND) <|> infixOp "&&" (BINOP AND)

orop :: Parser (AST -> AST -> AST)
orop = infixOp "||" (BINOP OR)

implies :: Parser (AST -> AST -> AST)
implies = infixOp "=>" (BINOP IMPLIES)

equals :: Parser (AST -> AST -> AST)
equals = infixOp "==" (BINOP EQUALS)
