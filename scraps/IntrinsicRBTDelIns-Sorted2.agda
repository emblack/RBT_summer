open import Preliminaries 
open import TightBound3
open List using (_++_)

module TightBound3-Sorted2 where


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
        Sorted : List (Key × Value) → Set
        _l≤_ : List (Key × Value) → Key × Value → Set
        _≤l_ : Key × Value → List (Key × Value) → Set

        []≤ : ∀ {x} → [] l≤ x
        ≤[] : ∀ {x} → x ≤l []

        []-Sorted : Sorted []

        lnode-Sorted  : ∀ {l x r} → Sorted l → l l≤ x → x ≤l r → Sorted r → Sorted (lnode l x r)
        lnode-Sorted' : ∀ {l x r} → Sorted (lnode l x r) → Sorted l × l l≤ x × x ≤l r × Sorted r 


    open Model

    data SortedRBT : {n : Nat} {c : RBColor} → RBT' n c → List (Key × Value) → Set where
      Empty : SortedRBT Empty []
      Node  : ∀ {n m c cl cr bl br b}
                {t : NodeType c m n cl cr}
                {l : RBT' n cl}
                {x : Key × Value}
                {r : RBT' n cr}
             → SortedRBT l bl
             → (bl l≤ x) × (x ≤l br) → b == lnode bl x br
             → SortedRBT r br
             → SortedRBT (Node t l x r) b

    SortedRBT-Sorted : ∀ {n : Nat} {c : RBColor} {t : RBT' n c} {m : List (Key × Value)} → SortedRBT t m → Sorted m
    SortedRBT-Sorted Empty = []-Sorted
    SortedRBT-Sorted (Node sl b Refl sr) = lnode-Sorted (SortedRBT-Sorted sl) (fst b) (snd b) (SortedRBT-Sorted sr)

    data SortedLeftARBT : {n : Nat}{c : RBColor} → LeftARBT n c → List (Key × Value) → Set where
      RR  : ∀ {n cr bl br b} {l : RBT' n Red} {x : Key × Value} {r : RBT' n cr} 
             → SortedRBT l bl
             → (bl l≤ x) × (x ≤l br) → b == lnode bl x br 
             → SortedRBT r br
             → SortedLeftARBT (RR l x r) b
      nv : ∀ {n c b} {t : RBT' n c} → SortedRBT t b → SortedLeftARBT (nv t) b

    data SortedRightARBT : {n : Nat}{c : RBColor} → RightARBT n c → List (Key × Value) → Set where
      RR  : ∀ {n cl bl br b} {l : RBT' n cl} {x : Key × Value} {r : RBT' n Red} 
             → SortedRBT l bl
             → (bl l≤ x) × (x ≤l br) → b == lnode bl x br 
             → SortedRBT r br
             → SortedRightARBT (RR l x r) b
      nv : ∀ {n c b} {t : RBT' n c} → SortedRBT t b → SortedRightARBT (nv t) b

    SortedARBT : {n : Nat}{c : RBColor} → ARBT n c → List (Key × Value) → Set 
    SortedARBT (Inl t) b = SortedLeftARBT t b
    SortedARBT (Inr t) b = SortedRightARBT t b

    SortedInsResult : (c : RBColor) {n : Nat} → InsResult c n → List (Key × Value) → Set
    SortedInsResult Black t b = SortedRBT (get t) b
    SortedInsResult Red t b = SortedARBT (get t) b

    Sorted-LeftARBT-RedNode : ∀ {n cl mn ml mr}  {l :  RBT' n cl} {x : Key × Value} { r :  RBT' n Black} 
                    → SortedRBT l ml
                    → (ml l≤ x) × (x ≤l mr) → mn == lnode ml x mr
                    → SortedRBT r mr
                    → SortedLeftARBT (LeftARBT-RedNode l x r) mn
    Sorted-LeftARBT-RedNode {cl = RBT.Black} sl b Refl sr = nv (Node sl b Refl sr)
    Sorted-LeftARBT-RedNode {cl = RBT.Red} sl b Refl sr = RR sl b Refl sr

    IR-NodeL-Sorted : ∀ {c m n cl cr mn ml mr} {t : NodeType c m n cl cr} {l :  InsResult cl n} {x : Key × Value} { r :  RBT' n cr} 
                    → SortedInsResult cl l ml
                    → (ml l≤ x) × (x ≤l mr) → mn == lnode ml x mr
                    → SortedRBT r mr
                    → SortedInsResult c (IR-NodeL t l x r) mn
    IR-NodeL-Sorted {t = Black} sl b Refl sr = {!!}
    IR-NodeL-Sorted {t = Red} sl b Refl sr = Sorted-LeftARBT-RedNode sl b Refl sr

    ins-sorted : ∀ {m c b} {x : Key × Value} {t : RBT' m c} → SortedRBT t b → SortedInsResult c (ins x t) (linsert b x)
    ins-sorted Empty = Node Empty ([]≤ , ≤[]) Refl Empty
    ins-sorted {c = c} {x = k , v} (Node {bl = ml} {br = mr} {t = t} {x = k' , v'} sl b Refl sr) with compare k k'
    ... | Less le neq = transport (SortedInsResult c _) {!!}
                          (IR-NodeL-Sorted {ml = linsert ml (k , v)} {mr = mr} (ins-sorted sl) {!!} Refl sr)
    ... | Greater ge neq = {!!}
    ins-sorted {x = k , v} (Node {x = .k , v'} sl b Refl sr) | Equal Refl = {!(SortedRBT.Node {x = k , v'} sl (nb p q r₁ s) sr)!}

