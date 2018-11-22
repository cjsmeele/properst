{-# LANGUAGE TupleSections #-}
{- |
Module      : Text.Polyglot
Description : A simple self-contained parser combinator library
Copyright   : (c) Chris Smeele, 2018
License     : GPL-3
Maintainer  : chris@cjsmeele.nl
Stability   : experimental

Text.Polyglot is a simple self-contained parser combinator library.
-}
module Text.Polyglot (module Text.Polyglot
                     ,(<|>)
                     ,empty
                     ,some
                     ,many
                     ,optional)
                         where

import           Control.Arrow
import           Control.Applicative
import           Control.Monad
import           Data.Char
import           Data.List (intersectBy)
import           Data.Maybe (listToMaybe)

-- * Types

newtype Parser a b = P ([a] -> [(b, [a])])

type SParser = Parser Char

-- * Executing parsers

-- | Executes a parser on an input sequence, producing a list of success.
parse :: Parser a b -> [a] -> [(b, [a])]
parse (P p) = p

-- | Executes a parser on an input sequence, producing a single optional success value.
-- The input string must be completely consumed for a result to be considered.
parse' :: Parser a b -> [a] -> Maybe b
--parse' p = listToMaybe . map fst . filter (null . snd) . parse p
parse' p = parse p
       >>> filter (snd >>> null)
       >>> map fst
       >>> listToMaybe

-- * Combining parsers

-- | Combine the results of parsers.
instance Semigroup s => Semigroup (Parser a s) where
    px <> py = (<>) <$> px <*> py

instance Monoid s => Monoid (Parser a s) where
    mempty = pure mempty

-- | Apply a function to succesful parse results.
instance Functor (Parser a) where
    fmap g p = P (parse p >>> fmap (\(x,rest) -> (g x, rest)))

-- | Apply a function in Parser context to a value in Parser context.
instance Applicative (Parser a) where
    pure x    = P (pure . (x,))
    fg <*> fx = fg >>= (<$> fx)

instance Alternative (Parser a) where
    empty = P (const [])
    px <|> py = P (\xs -> parse px xs ++ parse py xs)

instance MonadPlus (Parser a)

instance Monad (Parser a) where
    p >>= f = P (parse p >>> concatMap (\(y,rest) -> parse (f y) rest))

-- | The intersection of two parsers.
(<&>) :: Eq b => Parser a b -> Parser a b -> Parser a b
pa <&> pb = P (\xs -> let ay = parse pa xs
                          by = parse pb xs
                       in intersectBy (\(ax,ar) (bx,br) ->
                                           ax == bx
                                        && (length ar == length br))
                                       ay
                                       by)

-- * Parser primitives

-- | Consume a single item.
item :: Parser a a
item = P item'
    where item' []     = empty
          item' (x:xs) = pure (x, xs)

-- | Consume a single item fulfilling a given predicate.
sat :: (a -> Bool) -> Parser a a
sat p = item >>= \x -> if p x then pure x else empty

-- | Assert that the next item fulfills the given predicate, without consuming it.
sattert :: (a -> Bool) -> Parser a ()
sattert p = item >>= \x -> P (\xs -> if p x then pure ((),x:xs) else empty)

-- | Assert non-emptiness.
nonempty :: Parser a ()
nonempty = sattert (const True)

-- | Match the given item.
char :: Eq a => a -> Parser a a
char x = sat (== x)

-- | Match the given sequence of items.
string :: Eq a => [a] -> Parser a [a]
string = mapM char

once :: Parser a a -> Parser a [a]
once = fmap pure

-- | Non-greedy version of some.
someq p = (:) <$> p <*> manyq p

-- | Non-greedy version of many.
manyq p = pure []   <|> someq p

-- | Matches a single character that is not contained in the given list.
noneOf :: Eq a => [a] -> Parser a a
noneOf forbidden = sat (not . (`elem` forbidden))
