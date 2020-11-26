-- https://gist.github.com/polendri/98ff11c4d13e701d8bcc0fe04d67e11d
-- https://www.reddit.com/r/Idris/comments/iq2m89/struggling_with_erasure_in_verified_binary_search/

import Data.DPair
import Decidable.Equality
import Decidable.Order

%default total

public export
data BTree : (0 a : Type) -> Type where
  Empty : BTree a
  Tree  : (left : BTree a) ->
          (x : a) ->
          (right : BTree a) ->
          BTree a

mutual
  ||| Invariant for `BTree`
  public export
  data BSTreeInv : {0 a : Type} ->
                   {0 to : a -> a -> Type} ->
                   (0 eq : DecEq a) ->
                   (0 ord : Ordered a to) ->
                   (t : BTree a) ->
                   Type where
    BSEmpty : BSTreeInv eq ord Empty
    ||| Can build a node out of value `x` and two trees which satisfy the invariant, if the left
    ||| tree is strictly less than `x` and the right tree is strictly greater than `x`
    BSNode  : {0 a : Type} ->
              {0 to : a -> a -> Type} ->
              {0 eq : DecEq a} ->
              {0 ord : Ordered a to} ->
              {l : BTree a} ->
              {r : BTree a} ->
              {x : a} ->
              (invL : BSTreeInv eq ord l) ->
              (invR : BSTreeInv eq ord r) ->
              (ordL : BSTreeLT x invL) ->
              (ordR : BSTreeGT x invR) ->
              BSTreeInv eq ord (Tree l x r)

  ||| Proof that a tree is strictly less than some value `x`
  public export
  data BSTreeLT : (x : a) -> BSTreeInv {a} eq ord t -> Type where
    BSEmptyLT : BSTreeLT x BSEmpty
    BSNodeLT  : (invL : BSTreeInv {to} eq ord l) ->
                (inv : BSTreeInv {to} eq ord (Tree l y r)) ->
                (prfNeq : Not (x = y)) ->
                (prfOrd : to x y) ->
                (prfLT : BSTreeLT x invL) ->
                BSTreeLT x inv

  ||| Proof that a tree is strictly greater than some value `x`
  public export
  data BSTreeGT : (x : a) -> BSTreeInv {a} eq ord t -> Type where
    BSEmptyGT : BSTreeGT x BSEmpty
    BSNodeGT  : (invR : BSTreeInv {to} eq ord r) ->
                (inv : BSTreeInv {to} eq ord (Tree l y r)) ->
                (prfNeq : Not (x = y)) ->
                (prfOrd : to y x) ->
                (prfGT : BSTreeGT x invR) ->
                BSTreeGT x inv

||| TODO docs
public export
BSTree : {0 a : Type} ->
         {0 to : a -> a -> Type} ->
         (eq : DecEq a) ->
         (ord : Ordered a to) ->
         Type
BSTree eq ord = Subset.Subset (BTree a) (BSTreeInv eq ord)

||| The empty set.
public export
empty : (eq : DecEq a) => (ord : Ordered a to) => BSTree eq ord
empty = Element Empty BSEmpty

||| Create a singleton set.
public export
singleton : (eq : DecEq a) =>
            (ord : Ordered a to) =>
            (x : a) ->
            BSTree eq ord
singleton x = Element (Tree Empty x Empty) (BSNode BSEmpty BSEmpty BSEmptyLT BSEmptyGT)

||| Proof that `x` is an element of tree `t`.
public export
data Elem : {0 a : Type} ->
            {0 to : a -> a -> Type} ->
            {0 eq : DecEq a} ->
            {0 ord : Ordered a to} ->
            (x : a) ->
            (t : BSTree {a} eq ord) ->
            Type where
  Here    : {0 inv : BSTreeInv eq ord (Tree l x r)} ->
            Elem x (Element (Tree l x r) inv)
  InLeft  : {0 invL : BSTreeInv eq ord l} ->
            {0 invR : BSTreeInv eq ord r} ->
            (0 ordL : BSTreeLT y invL) ->
            (0 ordR : BSTreeGT y invR) ->
            (elemL : Elem x (Element l invL)) ->
            Elem x (Element (Tree l y r) (BSNode invL invR ordL ordR))
  InRight : {0 invL : BSTreeInv eq ord l} ->
            {0 invR : BSTreeInv eq ord r} ->
            (0 ordL : BSTreeLT y invL) ->
            (0 ordR : BSTreeGT y invR) ->
            (elemL : Elem x (Element r invR)) ->
            Elem x (Element (Tree l y r) (BSNode invL invR ordL ordR))


Uninhabited (Elem {eq} {ord} x (Element Empty BSEmpty)) where
  uninhabited Here               impossible
  uninhabited (InLeft _ _ _)     impossible
  uninhabited (InRight _ _ _)    impossible

notInLeaf : (x = y -> Void) ->
            Elem {eq} {ord} x (Element (Tree Empty y Empty) (BSNode BSEmpty BSEmpty ordL ordR)) ->
            Void
notInLeaf contra Here = contra Refl

elemInLeft : (x = z -> Void) ->
             Elem x {eq} {ord} (Element (Tree (Tree ll y lr) z Empty) (BSNode invL BSEmpty ordL ordR)) ->
             Elem x {eq} {ord} (Element (Tree ll y lr) invL)
elemInLeft prfNeq Here = absurd $ prfNeq Refl
elemInLeft prfNeq (InLeft ordL ordR elem) = elem

elemInLeft' : Not (x = y) ->
              to x y ->
              Elem x {a} {to} {eq} {ord} (Element (Tree l y r) (BSNode invL invR ordL ordR)) ->
              (Elem x {a} {to} {eq} {ord} (Element l invL), Not (Elem x {a} {to} {eq} {ord} (Element r invR)))
elemInLeft' prfNeq prfOrd Here = absurd $ prfNeq Refl
elemInLeft' prfNeq prfOrd (InLeft ordL ordR elemL) = (elemL, \prf => ?hole12)
elemInLeft' prfNeq prfOrd (InRight ordL ordR elemR) = ?hole13

-- Work around the compiler's erased constructor matching not working inside the pattern match on Element
-- https://github.com/idris-lang/Idris2/pull/404
isElem' : {eq : DecEq a} ->
          {ord : Ordered a to} ->
          (x : a) ->
          (t : BTree a) ->
          (0 tInv : BSTreeInv {a} eq ord t) ->
          Dec (Elem x (Element t tInv))
isElem' x Empty BSEmpty = No absurd
isElem' x (Tree Empty y Empty) (BSNode BSEmpty BSEmpty ordL ordR) with (decEq @{eq} x y)
  isElem' x (Tree Empty x Empty) (BSNode BSEmpty BSEmpty ordL ordR) | Yes Refl  = Yes Here
  isElem' x (Tree Empty y Empty) (BSNode BSEmpty BSEmpty ordL ordR) | No contra = No $ notInLeaf contra
isElem' x (Tree Empty y (Tree rl z rr)) (BSNode BSEmpty (BSNode invRL invRR ordRL ordRR) ordL ordR) with (decEq @{eq} x y)
  isElem' x (Tree Empty x (Tree rl z rr)) (BSNode BSEmpty (BSNode invRL invRR ordRL ordRR) ordL ordR) | Yes Refl  = Yes Here
  isElem' x (Tree Empty y (Tree rl z rr)) (BSNode BSEmpty (BSNode invRL invRR ordRL ordRR) ordL ordR) | No contra = ?asodimsdf_6_rhs_2
isElem' x (Tree (Tree ll y lr) z Empty) (BSNode (BSNode invLL invLR ordLL ordLR) BSEmpty ordL ordR) with (decEq @{eq} x z)
  isElem' x (Tree (Tree ll y lr) x Empty) (BSNode (BSNode invLL invLR ordLL ordLR) BSEmpty ordL ordR) | Yes Refl = Yes Here -- TODO combine Here cases
  isElem' x (Tree (Tree ll y lr) z Empty) (BSNode (BSNode invLL invLR ordLL ordLR) BSEmpty ordL ordR) | No neqXZ =
    case order @{ord} x z of
      Left  ordXZ => case isElem' x (Tree ll y lr) (BSNode invLL invLR ordLL ordLR) of
        Yes elemL => Yes $ InLeft ordL ordR elemL
        No contra => No $ absurd . contra . (elemInLeft neqXZ)
      Right ordZX => No $ \prf => ?hole1
isElem' x (Tree (Tree ll w lr) y (Tree rl z r)) (BSNode (BSNode invLL invLR ordLL ordLR) (BSNode invRL invRR ordRL ordRR) ordL ordR) = ?asodimsdf_8

isElem : (eq : DecEq a) =>
         (ord : Ordered a to) =>
         (x : a) ->
         (t : BSTree eq ord) ->
         Dec (Elem x t)
isElem x (Element t tInv) = isElem' x t tInv