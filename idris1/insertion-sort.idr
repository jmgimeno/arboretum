-- https://stackoverflow.com/questions/24105461/sorted-list-in-idris-insertion-sort
-- https://jerrington.me/posts/2016-11-11-total-order.lidr.html

module InsertionSort

import Data.So
import Decidable.Order

%default total

data NonEmptySortedList :  (a : Type)
                        -> (po : a -> a -> Type)
                        -> (max : a)
                        -> Type where
  SOne   : (el : a) -> NonEmptySortedList a po el
  SMany  :  (el : a)
         -> po el max
         -> NonEmptySortedList a po max
         -> NonEmptySortedList a po el

data SortedList : (a : Type) -> (po : a -> a -> Type) -> Type where
  Empty : SortedList _ _
  NonEmpty : NonEmptySortedList a po _ -> SortedList a po

head : NonEmptySortedList a _ _ -> a
head (SOne a) = a
head (SMany a _ _) = a

tail : NonEmptySortedList a po _ -> SortedList a po
tail (SOne _) = Empty
tail (SMany _ _ xs) = NonEmpty xs

max : {m : a} -> NonEmptySortedList a _ m -> a
max {m} _ = m

newMax : (Ordered a po) => SortedList a po -> a -> a
newMax Empty x = x
newMax (NonEmpty xs) x = either (const x)
                                (const (max xs))
                                (order {to = po} x (max xs))

either' :  {P : Either a b -> Type}
        -> (f : (l : a) -> P (Left l))
        -> (g : (r : b) -> P (Right r))
        -> (e : Either a b) -> P e
either' f g (Left l) = f l
either' f g (Right r) = g r

sinsert :  (Ordered a po)
        => (x : a)
        -> (xs : SortedList a po)
        -> NonEmptySortedList a po (newMax xs x)
sinsert x y with (y)
  | Empty = SOne {po = po} x
  | (NonEmpty xs) = either' { P = NonEmptySortedList a po
                            . either (const x) (const (max xs))
                            }
                            insHead
                            insTail
                            (order {to = po} x (max xs))
  where insHead : po x (max xs) -> NonEmptySortedList a po x
        insHead p = SMany x p xs
        max_lt_newmax : po (max xs) x -> po (max xs) (newMax (tail xs) x)
        max_lt_newmax max_xs_lt_x with (xs)
          | (SOne _) = max_xs_lt_x
          | (SMany _ max_xs_lt_max_xxs xxs)
            = either' { P = po (max xs) . either (const x)
                                                 (const (max xxs))}
                      (const {a = po (max xs) x} max_xs_lt_x)
                      (const {a = po (max xs) (max xxs)} max_xs_lt_max_xxs)
                      (order {to = po} x (max xxs))
        insTail : po (max xs) x -> NonEmptySortedList a po (max xs)
        insTail p = SMany (max xs)
                          (max_lt_newmax p)
                          (sinsert x (assert_smaller y (tail xs)))

insSort :  (Ordered a po) => List a -> SortedList a po
insSort = foldl (\xs, x => NonEmpty (sinsert x xs)) Empty