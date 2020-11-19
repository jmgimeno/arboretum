module Kahrs1 where

-- Kahrs's Proper Red-Black Trees

data Unit a          = E
type Tr t a          = (t a, a, t a)
data Red t a         = C (t a) | R (Tr t a)
newtype AddLayer t a = B (Tr (Red t) a)
data RB t a          = Base (t a) | Next (RB (AddLayer t) a)
type Tree a          = RB Unit a

member :: Ord a => a -> Tree a -> Bool
member x t = rbmember x t (const False)

rbmember :: Ord a => a -> RB t a -> (t a -> Bool) -> Bool
rbmember _ (Base t) m = m t
rbmember x (Next u) m = rbmember x u (bmem x m)

bmem :: Ord a => a -> (t a -> Bool) -> AddLayer t a -> Bool
bmem x m (B (l, y, r))
    | x < y = rmem x m l
    | x > y = rmem x m r
    | otherwise = True

rmem :: Ord a => a -> (t a -> Bool) -> Red t a -> Bool
rmem _ m (C t) = m t
rmem x m (R (l, y, r))
    | x < y = m l
    | x > y = m r
    | otherwise = True

--

empty :: Tree a
empty = Base E

singleton :: a -> Tree a
singleton x = Next (Base (B (C E, x, C E)))

