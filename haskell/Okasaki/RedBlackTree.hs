
data Color = R | B
data Tree a = E | T Color (Tree a) a (Tree a)

type Set a = Tree a
empty = E

member :: Ord a => a -> Set a -> Bool
member _ E = False
member x (T _ l y r) 
    | x < y     = member x l
    | x > y     = member x r
    | otherwise = True

insert :: Ord a => a -> Set a -> Set a
insert x s = makeBlack (ins s)
    where
        makeBlack (T _ l y r) = T B l y r 
        ins t@(T c l y r)
            | x < y     = balance c (ins l) y r
            | x > y     = balance c l y (ins r)
            | otherwise = t
        balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
        balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
        balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
        balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
        balance c a x b = T c a x b

