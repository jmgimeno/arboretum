{-# LANGUAGE ExistentialQuantification #-}

module Kahrs2 where

-- Top-Down Typing (changed some types from the article in order to compile)

type Tr t a b = (t a b, a, t a b)
data Red t a b = C (t a b) | R (Tr t a b)
data Black a b = E | B (Tr (Red Black) a [b])

balanceL :: Red (Red Black) a [b] -> a -> Red Black a [b] -> Red Black a b
balanceL (R (R (a, x, b), y, c)) z d = R (B (C a, x, C b), y, B(c, z, d))
balanceL (R (a, x, R (b, y, c))) z d = R (B (a, x, C b), y, B (C c, z, d))
balanceL (R (C a, x, C b)) z d       = C (B (R (a, x, b), z, d))
balanceL (C a) x b                   = C (B (a, x, b))

balanceR :: Red Black a [b] -> a -> Red (Red Black) a [b] -> Red Black a b
balanceR = undefined

insB  :: Ord a => a -> Black a b -> Red Black a b
insB x E = R (E, x, E)
insB x t@(B (a, y, b))
    | x < y = balanceL (insR x a) y b
    | x > y = balanceR a y (insR x b)
    | otherwise = C t

insR :: Ord a => a -> Red Black a b -> Red (Red Black) a b
insR x (C t) = C (insB x t)
insR x t@(R (a, y, b))
    | x < y = R(insB x a, y, C b)
    | x > y = R(C a, y, insB x b)
    | otherwise = C t

data Tree a = forall b. ENC (Black a b)
empty = ENC E

insert :: Ord a => a -> Tree a -> Tree a
insert x (ENC t) = ENC (blacken (insB x t))

blacken :: Red Black a b -> Black a b
blacken (C u) = u
blacken (R (a, x, b)) = B (C (inc a), x, C (inc b))

inc :: Black a b -> Black a [b]
inc = tickB

tickB :: Black a b -> Black a [b]
tickB E = E
tickB (B (a, x, b)) = B (tickR a, x, tickR b)

tickR :: Red Black a b -> Red Black a [b]
tickR (C t) = C (tickB t)
tickR (R (a,x,b)) = R (tickB a, x, tickB b)
