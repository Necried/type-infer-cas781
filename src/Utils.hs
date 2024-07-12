{-# LANGUAGE FlexibleContexts #-}

module Utils where

import Data.List (find, delete)
import Data.List.Extra
import Data.Function ((&))
import Control.Monad.Error.Class (MonadError, throwError)

lookupVar :: Foldable t => (a -> Bool) -> t a -> s -> Either s a
lookupVar f xs errMsg =
  let lookupRes = find f xs
  in case lookupRes of
    Nothing -> Left errMsg
    Just var -> Right var

find' :: Eq a => [(a, b)] -> a -> Maybe b
find' [] _ = Nothing
find' ((k, v) : rest) lookupKey =
  if k == lookupKey
  then Just v
  else find' rest lookupKey

takeUntilVar :: Eq a => a -> [a] -> [a]
takeUntilVar x = takeWhile (/= x)

splitOnItem :: Eq a => a -> [a] -> ([a],[a])
splitOnItem x xs =
  (takeWhile (/= x) xs, drop 1 $ dropWhile (/= x) xs)

replaceItem :: Eq a => a -> [a] -> [a] -> [a]
replaceItem x xsR xs =
  gammaL ++ xsR ++ gammaR
  where
    (gammaL, gammaR) = splitOnItem x xs

throwErrorWithContext :: MonadError (c, t) m => c -> t -> m a
throwErrorWithContext ctx err = throwError (ctx, err)

removeOldOccurence :: Eq a => a -> [a] -> [a]
removeOldOccurence = delete

infixl 5 <:
(<:) :: [a] -> a -> [a]
(<:) = snoc

infixl 1 |>
(|>) = (&)

infixr 0 <|
(<|) = ($)
