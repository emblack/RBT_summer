open import Preliminaries 
open import TightBound3
open List using (_++_)

module TightBound3-Sorted3 where


  module Sorted (KeyOrder : FancyOrder.DecidableOrder) (Value : Set) where 

    open FancyOrder.DecidableOrder KeyOrder renaming (A to Key)
    open FancyOrder

    compare' : Key → Key → Order 
    compare' x y with compare x y
    ... | Less _ _ = Less
    ... | Greater _ _ = Greater
    ... | Equal _ = Equal

    open RBT Key compare' Value

    module Model where
      linsert : List (Key × Value) → Key × Value → List (Key × Value)
      linsert [] kv = kv :: []
      linsert ((k' , v') :: xs) (k , v) with compare' k k'
      ...                                  | Less = (k , v) :: (k' , v') :: xs
      ...                                  | Equal = (k' , v') :: xs
      ...                                  | Greater = (k' , v') :: linsert xs (k , v)

      lnode : List (Key × Value) → (Key × Value) → List (Key × Value) → List (Key × Value)
      lnode l x r = l ++ (x :: r)

      postulate
        NoDups : List (Key × Value) → Set

    open Model

    rbttolist : ∀ {n : Nat} {c : RBColor} (t : RBT' n c) → List (Key × Value)
    rbttolist RBT.Empty = []
    rbttolist (RBT.Node t l x r) = lnode (rbttolist l) x (rbttolist r)

    latolist : ∀ {n : Nat} {c : RBColor} (t : LeftARBT n c) → List (Key × Value)
    latolist (RBT.RR l x r) = lnode (rbttolist l) x (rbttolist r)
    latolist (RBT.nv x) = rbttolist x

    ratolist : ∀ {n : Nat} {c : RBColor} (t : RightARBT n c) → List (Key × Value)
    ratolist (RBT.RR l x r) = lnode (rbttolist l) x (rbttolist r)
    ratolist (RBT.nv x) = rbttolist x

    atolist : ∀ {n : Nat} {c : RBColor} (t : ARBT n c) → List (Key × Value)
    atolist (Inl x) = latolist x
    atolist (Inr x) = ratolist x

    irtolist : ∀ c {n} → InsResult c n → List (Key × Value)
    irtolist RBT.Black i = rbttolist (get i)
    irtolist RBT.Red i = atolist (get i)

    ins-sorted : ∀ {m c} (x : Key × Value) (t : RBT' m c) → NoDups (rbttolist t) → 
                 irtolist c (ins x t) == linsert (rbttolist t) x
    ins-sorted x RBT.Empty nd = Refl
    ins-sorted x (RBT.Node t l y r) nd with compare (fst x) (fst y) 
    ins-sorted x (RBT.Node RBT.Black l y r) nd | Less leq neq = {!!}
    ins-sorted x (RBT.Node RBT.Red l y r) nd | Less leq neq = {!!}
    ... | Greater geq neq = {!t!}
    ins-sorted x (RBT.Node RBT.Black l y r) nd | Equal eq = {!!}
    ins-sorted x (RBT.Node RBT.Red l y r) nd | Equal eq = {!!}

