{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Text.Pretty( Pretty(..)) where

class Pretty m where
    pretty :: m -> String
    pretty = prettyTab 0
    prettyTab :: Int -> m -> String
    prettyPrint :: m -> IO ()
    prettyPrint  = putStrLn . pretty

instance {-# OVERLAPPING #-} Pretty String where
    prettyTab _ s =  s

instance Pretty Char where
    prettyTab _ c =  [c]

instance {-# OVERLAPPABLE #-} (Pretty a, Ord a) => Pretty [a] where
    prettyTab n0 s
        | null s = "[ ]"
        | otherwise = "[ " ++ aux (n0+2) s ++ " ]"
        where aux n (x:[]) = prettyTab n x
              aux n (x:xs) = prettyTab n x ++ '\n':take n (repeat ' ') ++ aux n xs
              aux _ _  = error "The unexpected happened"

instance Pretty a => Pretty (Maybe a) where
    prettyTab _ Nothing = "Nothing"
    prettyTab n (Just a) = "Just " ++ prettyTab (n+5) a

instance Pretty Int where
    prettyTab _ n = show n

instance (Pretty a, Pretty b) => Pretty (a,b) where
    prettyTab n (a, b) = "( "++prettyTab n a ++ " , " ++ prettyTab n b ++" )"
