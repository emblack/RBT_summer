open import Preliminaries 

module TightBound3 where

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- colors

    data Color : Set where
      Red : Color
      Black : Color
      DoubleBlack : Color

    data BlackColor : Set where
      Black : BlackColor
      DoubleBlack : BlackColor

    data RBColor : Set where
      Black : RBColor
      Red   : RBColor

    ↑ : BlackColor → Color
    ↑ Black = Black
    ↑ DoubleBlack = DoubleBlack

    ↓ : RBColor → Color
    ↓ Black = Black
    ↓ Red = Red

    _-1 : BlackColor → RBColor
    Black -1 = Red
    DoubleBlack -1 = Black

    _+1 : RBColor → BlackColor
    Black +1 = DoubleBlack
    Red +1 = Black

    ↓↑black : ∀ c1 c2 → ↓ c1 == ↑ c2 → c1 == Black
    ↓↑black Black Black eq = Refl
    ↓↑black Black DoubleBlack eq = Refl
    ↓↑black Red Black ()
    ↓↑black Red DoubleBlack ()

    -- ----------------------------------------------------------------------
    -- datatypes

    data NodeType : RBColor → (thisHeight : Nat) (childHeight : Nat) (lc : RBColor) (rc : RBColor) → Set where
      Black       : ∀ {n lc rc} → NodeType Black (S n) n lc rc
      Red         : ∀ {n} → NodeType Red n n Black Black

    swap : ∀ {c m n cl cr} → NodeType c m n cl cr → NodeType c m n cr cl 
    swap Black = Black
    swap Red = Red

    data RBT' : Nat → RBColor → Set where
      Empty : RBT' 1 Black
      Node  : ∀ {n m c cl cr}
              → (t : NodeType c m n cl cr)
              → (l : RBT' n cl)
              → (x : Key × Value)
              → (r : RBT' n cr)
              → RBT' m c

    data LeftARBT : (n : Nat) → RBColor → Set where
      RR  : ∀ {n cr} → (l : RBT' n Red) → (x : Key × Value) → (r : RBT' n cr) → LeftARBT n Red
      nv : ∀ {n c} → RBT' n c → LeftARBT n c

    data RightARBT : (n : Nat) → RBColor → Set where
      RR  : ∀ {n cl} → (l : RBT' n cl) → (x : Key × Value) → (r : RBT' n Red) → RightARBT n Red
      nv : ∀ {n c} → RBT' n c → RightARBT n c

    data BBRBT : (n : Nat) → Color → Set where
      BB  : ∀ {n} → RBT' n Black → BBRBT (S n) DoubleBlack 
      nv : ∀ {n c} → RBT' n c → BBRBT n (↓ c)

    RightARBT-RedNode : ∀ {n cr} → (l : RBT' n Black) → (x : Key × Value) → (r : RBT' n cr) → RightARBT n Red
    RightARBT-RedNode {cr = Black} l x r = nv (Node Red l x r)
    RightARBT-RedNode {cr = Red} l x r = RR l x r

    nozeroheight : ∀ {c} → RBT' 0 c → Void
    nozeroheight (Node Red t₁ x t₂) = nozeroheight t₁
    
    -- ----------------------------------------------------------------------
    -- balance 

    data BalanceResult : Nat → BlackColor → Set where
      B : ∀ {c n} → RBT' (S n) c → BalanceResult n Black
      BB : ∀ {c n} → BBRBT (S (S n)) (↑ c) → BalanceResult n DoubleBlack

    bc-1type : (c : BlackColor) (n : Nat) → Σ \ m → NodeType (c -1) m n Black Black
    bc-1type Black _ = _ , Red
    bc-1type DoubleBlack _ = _ , Black

    BR-nv : ∀ {bc n} → RBT' (fst (bc-1type bc (S n))) (bc -1) → BalanceResult n bc
    BR-nv {Black} t = B t
    BR-nv {DoubleBlack} t = BB (nv t)

    BR-Node : ∀ {n lc rc} → {c : BlackColor} → RBT' n lc → Key × Value → RBT' n rc → BalanceResult n c
    BR-Node {c = Black} l x r = B (Node Black l x r)
    BR-Node {c = DoubleBlack} l x r = BB (BB (Node Black l x r))

    balanceLeft : ∀ {n lc rc} {c : BlackColor} → RightARBT n lc → (Key × Value) → RBT' n rc → BalanceResult n c
    balanceLeft (RR a x (Node Red b y c)) z d = BR-nv (Node (snd (bc-1type _ _)) (Node Black a x b) y (Node Black c z d)) 
    balanceLeft (nv a) z d = BR-Node a z d

    balanceRight : ∀ {n lc rc} → {c : BlackColor} → RBT' n lc → (Key × Value) → LeftARBT n rc → BalanceResult n c
    balanceRight a x (RR (Node Red b y c) z d) = BR-nv (Node (snd (bc-1type _ _)) (Node Black a x b) y (Node Black c z d)) 
    balanceRight a z (nv d) = BR-Node a z d

    -- ----------------------------------------------------------------------
    -- rotate

    data RotateType : RBColor → Nat → Nat → Color → RBColor → Set where
      Red : ∀ {n} {c : BlackColor} → RotateType Red n n (↑ c) Black
      Black : ∀ {n} {cv : Color} {cnv : RBColor} → RotateType Black (S n) n cv cnv 

    data CBBRBT : RBColor → Nat → Set where
      R : ∀ {m} {c : Color} → BBRBT m c → CBBRBT Red m
      B : ∀ {m} {c : BlackColor} → BBRBT m (↑ c) → CBBRBT Black m

    forgetC : ∀ {c n} → CBBRBT c n → Σ \ c' → BBRBT n c'
    forgetC (R t) = _ , t
    forgetC (B t) = _ , t

    promote-br-rr :  ∀ {c m n lc rc} → RotateType c m (S n) lc rc → BalanceResult n (c +1) → CBBRBT c m
    promote-br-rr Black (BB t) = B t
    promote-br-rr Red (B t) = R (nv t)

    rotate-Node : ∀ {c m n lc lc' rc} (t : RotateType c m n lc rc) (eq : lc == (↓ lc'))
                  (l : RBT' n lc') (x : Key × Value) (r : RBT' n rc)
                → CBBRBT c m
    rotate-Node Red eq l x r rewrite ↓↑black _ _ (! eq) = R (nv (Node Red l x r))
    rotate-Node Black Refl l x r = B (nv (Node Black l x r))

    rotateLeft : ∀ {c m n lc rc}
               → RotateType c m n lc rc → BBRBT n lc → (Key × Value) → RBT' n rc
               → CBBRBT c m 
    -- interesting case 1
    rotateLeft {c = rootc} t (BB a) x (Node Black b y c) = promote-br-rr t (balanceLeft {c = rootc +1} (RightARBT-RedNode a x b) y c) 
    -- interesting case 2
    rotateLeft Black (BB a) x (Node Red (Node Black b y c) z d) with (balanceLeft {c = Black} (RightARBT-RedNode a x b) y c)
    ...                                                           | B l' = B (nv (Node Black l' z d))
    -- keep it the same
    rotateLeft t (nv a) z d = rotate-Node t Refl a z d
    -- contradictions
    rotateLeft t (BB a) x Empty = abort (nozeroheight a)
    rotateLeft Black (BB a) x (Node Red Empty y c) = abort (nozeroheight a)

    rotateRight : ∀ {c m n lc rc}
               → RotateType c m n rc lc → RBT' n lc → (Key × Value) → BBRBT n rc
               → CBBRBT c m 
    rotateRight = {!symmetric!}

    CBBRBT-NodeL : ∀ {c m n lc rc} → NodeType c m n lc rc → CBBRBT lc n → (Key × Value) → RBT' n rc → CBBRBT c m
    CBBRBT-NodeL Black l x r = rotateLeft Black (snd (forgetC l)) x r
    CBBRBT-NodeL Red (B l) x r = rotateLeft Red l x r

    CBBRBT-NodeR : ∀ {c m n lc rc} → NodeType c m n lc rc → RBT' n lc → (Key × Value) → CBBRBT rc n → CBBRBT c m
    CBBRBT-NodeR = {!symmetric!}

    CBBRBT-Leaf : ∀ {c n cl cr} → NodeType c n 1 cl cr → RBT' 1 cl → CBBRBT c n
    CBBRBT-Leaf Black Empty = B (BB Empty)
    CBBRBT-Leaf Black (Node Red Empty x Empty) = B (nv (Node Black Empty x Empty))
    CBBRBT-Leaf Red Empty = R (nv Empty)
    -- impossible
    CBBRBT-Leaf Black (Node Black l x r) = abort (nozeroheight l)
    CBBRBT-Leaf Black (Node Red (Node Black l x l₁) x₁ r) = abort (nozeroheight l)
    CBBRBT-Leaf Black (Node Red Empty x (Node Black r x₁ r₁)) = abort (nozeroheight r)
    CBBRBT-Leaf Red (Node Black l x r) = abort (nozeroheight l)

    IsNode : ∀ {n c} → RBT' n c → Set
    IsNode (Node _ _ _ _) = Unit
    IsNode (Empty) = Void

    mindel : ∀ {n c} → (t : RBT' n c) {isnode : IsNode t} → (Key × Value) × CBBRBT c n
    mindel Empty {isnode = ()}
    mindel (Node t Empty x r) = x , CBBRBT-Leaf (swap t) r
    mindel (Node t (Node t1 l1 x l2) y r) with mindel (Node t1 l1 x l2)
    ...                                       | min , l' = min , CBBRBT-NodeL t l' y r

    del : ∀ {n c} → Key → (t : RBT' n c) → CBBRBT c n
    del k Empty = B (nv Empty)
    del k (Node {c = c} t l (k' , v') r) with compare k k'
    ...                                     | Less    = CBBRBT-NodeL t (del k l) (k' , v') r 
    ...                                     | Greater = CBBRBT-NodeR t l (k' , v') (del k r)
    del k (Node t l (k' , v') Empty) | Equal = CBBRBT-Leaf t l
    del k (Node t l (k' , v') (Node tr r1 x r2)) | Equal with mindel (Node tr r1 x r2)
    ...                                                     | a , r' = CBBRBT-NodeR t l a r'

    RBT = Σ(\ m → Σ \ c → RBT' m c)

    blackenroot : ∀ {n c} → BBRBT n c → RBT
    blackenroot (BB Empty) = _ , _ , Empty 
    blackenroot (BB (Node Black l x r)) = _ , _ , Node Black l x r
    blackenroot (nv t) = _ , _ , t

    delete : Key → RBT → RBT
    delete k (_ , _ , t) = blackenroot (snd (forgetC (del k t)))
