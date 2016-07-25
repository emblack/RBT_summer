open import Preliminaries 
open import TightBound3

module TightBound3-Sorted where

  module Sorted (KeyOrder : FancyOrder.DecidableOrder) (Value : Set) where 

    open FancyOrder.DecidableOrder KeyOrder renaming (A to Key)
    open FancyOrder

    compare' : Key → Key → Order 
    compare' x y with compare x y
    ... | Less _ _ = Less
    ... | Greater _ _ = Greater
    ... | Equal _ = Equal

    open RBT Key compare' Value

    record Bounds : Set where
      constructor bounds 
      field
        low  : Key
        high : Key
        leq  : low ≤ high
    
    _≤b_ : Key × Value → Bounds → Set
    (k , _) ≤b b = k ≤ Bounds.low b

    _b≤_ : Bounds → Key × Value → Set
    b b≤ (k , _) = Bounds.high b ≤ k

    postulate
      insBounds : Bounds → Key → Bounds

    record NodeBounds (overall : Bounds) (left : Bounds) (x : Key × Value) (right : Bounds) : Set where
      constructor nb 
      field 
        overallleft : Bounds.low overall ≤ Bounds.low left
        leftmid : left b≤ x
        midright : x ≤b right
        rightoverall : Bounds.high overall ≤ Bounds.high left

    data SortedRBT : {n : Nat} {c : RBColor} → RBT' n c → Bounds → Set where
      Empty : ∀ {b} → SortedRBT Empty b
      Node  : ∀ {n m c cl cr bl br b}
                {t : NodeType c m n cl cr}
                {l : RBT' n cl}
                {x : Key × Value}
                {r : RBT' n cr}
             → SortedRBT l bl
             → NodeBounds b bl x br
             → SortedRBT r br
             → SortedRBT (Node t l x r) b

    data SortedLeftARBT : {n : Nat}{c : RBColor} → LeftARBT n c → Bounds → Set where
      RR  : ∀ {n cr bl br b} {l : RBT' n Red} {x : Key × Value} {r : RBT' n cr} 
             → SortedRBT l bl
             → NodeBounds b bl x br
             → SortedRBT r br
             → SortedLeftARBT (RR l x r) b
      nv : ∀ {n c b} {t : RBT' n c} → SortedRBT t b → SortedLeftARBT (nv t) b

    data SortedRightARBT : {n : Nat}{c : RBColor} → RightARBT n c → Bounds → Set where
      RR  : ∀ {n cl bl br b} {l : RBT' n cl} {x : Key × Value} {r : RBT' n Red} 
             → SortedRBT l bl
             → NodeBounds b bl x br
             → SortedRBT r br
             → SortedRightARBT (RR l x r) b
      nv : ∀ {n c b} {t : RBT' n c} → SortedRBT t b → SortedRightARBT (nv t) b

    SortedARBT : {n : Nat}{c : RBColor} → ARBT n c → Bounds → Set 
    SortedARBT (Inl t) b = SortedLeftARBT t b
    SortedARBT (Inr t) b = SortedRightARBT t b

    SortedInsResult : (c : RBColor) {n : Nat} → InsResult c n → Bounds → Set
    SortedInsResult Black t b = SortedRBT (get t) b
    SortedInsResult Red t b = SortedARBT (get t) b

    ins-sorted : ∀ {m c b} {x : Key × Value} {t : RBT' m c} → SortedRBT t b → SortedInsResult c (ins x t) (insBounds b (fst x))
    ins-sorted Empty = Node Empty {!!} Empty
    ins-sorted {x = k , v} (Node {x = k' , v'} sl (nb p q r s) sr) with compare k k'
    ... | Less le neq = {!!}
    ... | Greater ge neq = {!!}
    ins-sorted {x = k , v} (Node {x = .k , v'} sl (nb p q r₁ s) sr) | Equal Refl = {!(SortedRBT.Node {x = k , v'} sl (nb p q r₁ s) sr)!}



    
