module Plutonomy.MissingH where

import Control.Applicative ((<|>))

-- | Apply a function until a fixed point is reached.
--
-- /Use with care/.
fixedpoint :: Eq a => (a -> a) -> a -> a
fixedpoint f x
    | x == y    = x
    | otherwise = fixedpoint f y
  where
    y = f x

-- | Iterate function until 'Nothing' result. Return the last 'Just' value.
iterateWhileJust :: (a -> Maybe a) -> a -> a
iterateWhileJust f x = case f x of
    Just x' -> iterateWhileJust f x'
    Nothing -> x

-- | Try first function, if it returns 'Nothing' try second.
(\/) :: (a -> Maybe b) -> (a -> Maybe b) -> (a -> Maybe b)
f \/ g = \x -> f x <|> g x

(\//) :: (a -> b -> Maybe c) -> (a -> b -> Maybe c) -> (a -> b -> Maybe c)
f \// g = \x y -> f x y <|> g x y
