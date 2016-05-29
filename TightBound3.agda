open import Preliminaries 

module TightBound3 where

  record Σi {A : Set} (B : A → Set) : Set where
    constructor [_]
    field
      {first}  : A
      get : B first

  open Σi

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

    LeftARBT-RedNode : ∀ {n cl} → (l : RBT' n cl) → (x : Key × Value) → (r : RBT' n Black) → LeftARBT n Red
    LeftARBT-RedNode {cl = Black} l x r = nv (Node Red l x r)
    LeftARBT-RedNode {cl = Red} l x r = RR l x r

    nozeroheight : ∀ {c} → RBT' 0 c → Void
    nozeroheight (Node Red t₁ x t₂) = nozeroheight t₁
    
    -- ----------------------------------------------------------------------
    -- balance 

    data BalanceType : BlackColor → Nat → Nat → Set where
      Black       : ∀ {n} → BalanceType Black (S n) n
      DoubleBlack : ∀ {n} → BalanceType DoubleBlack (S (S n)) n

    BalanceResult : BlackColor → Nat → Set 
    BalanceResult Black m = Σi \ (c : RBColor) → RBT' m c
    BalanceResult DoubleBlack m = Σi \ (c : BlackColor) → BBRBT m (↑ c)

    BR-Node-1 : ∀ {c m n} → BalanceType c m n → RBT' (S n) Black → Key × Value → RBT' (S n) Black → BalanceResult c m
    BR-Node-1 Black l x r = [ Node Red l x r ]
    BR-Node-1 DoubleBlack l x r = [ nv (Node Black l x r) ]

    BR-Node : ∀ {c m n lc rc} → BalanceType c m n → RBT' n lc → Key × Value → RBT' n rc → BalanceResult c m
    BR-Node Black l x r = [ Node Black l x r ]
    BR-Node DoubleBlack l x r = [ BB (Node Black l x r) ]

    balanceLeft : ∀ {c n m lc rc} → BalanceType c m n → RightARBT n lc → (Key × Value) → RBT' n rc → BalanceResult c m
    balanceLeft t (RR a x (Node Red b y c)) z d = BR-Node-1 t (Node Black a x b) y (Node Black c z d)
    balanceLeft t (nv a) z d = BR-Node t a z d

    balanceRight : ∀ {c m n lc rc} → BalanceType c m n → RBT' n lc → (Key × Value) → LeftARBT n rc → BalanceResult c m
    balanceRight t a x (RR (Node Red b y c) z d) = BR-Node-1 t (Node Black a x b) y (Node Black c z d)
    balanceRight t a z (nv d) = BR-Node t a z d

    -- ----------------------------------------------------------------------
    -- rotate

    data RotateType : RBColor → Nat → Nat → Color → RBColor → Set where
      Red : ∀ {n} {c : BlackColor} → RotateType Red n n (↑ c) Black
      Black : ∀ {n} {cv : Color} {cnv : RBColor} → RotateType Black (S n) n cv cnv 

    CBBRBT : RBColor → Nat → Set 
    CBBRBT Red m = Σi \ (c : Color) → BBRBT m c
    CBBRBT Black m = Σi \ (c : BlackColor) → BBRBT m (↑ c)

    forgetC : ∀ c {m} → CBBRBT c m → Σi \ c' → BBRBT m c'
    forgetC Red  t = t
    forgetC Black [ t ] = [ t ]

    _+1' : ∀ {c m n lc rc} → RotateType c m (S n) lc rc → BalanceType (c +1) m n
    Red +1' = Black
    Black +1' = DoubleBlack
    
    promote-BR-CBB :  ∀ c {m} → BalanceResult (c +1) m → CBBRBT c m
    promote-BR-CBB Black [ t ] = [ t ]
    promote-BR-CBB Red [ t ] = [ nv t ]

    CBB-Node' : ∀ {c m n lc lc' rc} (t : RotateType c m n lc rc) (eq : lc == (↓ lc'))
                  (l : RBT' n lc') (x : Key × Value) (r : RBT' n rc)
                → CBBRBT c m
    CBB-Node' Red eq l x r rewrite ↓↑black _ _ (! eq) = [ nv (Node Red l x r) ]
    CBB-Node' Black Refl l x r = [ nv (Node Black l x r) ]

    CBB-Node : ∀ {c m n lc rc} (t : RotateType c m n (↓ lc) rc) 
                  (l : RBT' n lc) (x : Key × Value) (r : RBT' n rc)
                → CBBRBT c m
    CBB-Node t = CBB-Node' t Refl

    rotateLeft : ∀ {c m n lc rc}
               → RotateType c m n lc rc → BBRBT n lc → (Key × Value) → RBT' n rc
               → CBBRBT c m 
    -- interesting case 1
    rotateLeft {c = co} t (BB a) x (Node Black b y c) = promote-BR-CBB co (balanceLeft (t +1') (RightARBT-RedNode a x b) y c)
    -- interesting case 2
    rotateLeft Black (BB a) x (Node Red (Node Black b y c) z d) with (balanceLeft Black (RightARBT-RedNode a x b) y c)
    ...                                                            | [ l' ] = [ nv (Node Black l' z d) ]
    -- keep it the same
    rotateLeft t (nv a) z d = CBB-Node t a z d
    -- contradictions
    rotateLeft t (BB a) x Empty = abort (nozeroheight a)
    rotateLeft Black (BB a) x (Node Red Empty y c) = abort (nozeroheight a)

    rotateRight : ∀ {c m n lc rc}
               → RotateType c m n rc lc → RBT' n lc → (Key × Value) → BBRBT n rc
               → CBBRBT c m 
    rotateRight = {!symmetric!}

    CBB-NodeL : ∀ {c m n lc rc} → NodeType c m n lc rc → CBBRBT lc n → (Key × Value) → RBT' n rc → CBBRBT c m
    CBB-NodeL {lc = lc} Black l x r = rotateLeft Black (get (forgetC lc l)) x r
    CBB-NodeL Red [ l ] x r = rotateLeft Red l x r

    CBB-NodeR : ∀ {c m n lc rc} → NodeType c m n lc rc → RBT' n lc → (Key × Value) → CBBRBT rc n → CBBRBT c m
    CBB-NodeR = {!symmetric!}

    CBB-Leaf : ∀ {c n cl cr} → NodeType c n 1 cl cr → RBT' 1 cl → CBBRBT c n
    CBB-Leaf Black Empty = [ BB Empty ]
    CBB-Leaf Black (Node Red Empty x Empty) = [ nv (Node Black Empty x Empty) ]
    CBB-Leaf Red Empty = [ nv Empty ]
    -- impossible
    CBB-Leaf Black (Node Black l x r) = abort (nozeroheight l)
    CBB-Leaf Black (Node Red (Node Black l x l₁) x₁ r) = abort (nozeroheight l)
    CBB-Leaf Black (Node Red Empty x (Node Black r x₁ r₁)) = abort (nozeroheight r)
    CBB-Leaf Red (Node Black l x r) = abort (nozeroheight l)

    -- ----------------------------------------------------------------------
    -- delete

    IsNode : ∀ {n c} → RBT' n c → Set
    IsNode (Node _ _ _ _) = Unit
    IsNode (Empty) = Void

    mindel : ∀ {n c} → (t : RBT' n c) {isnode : IsNode t} → (Key × Value) × CBBRBT c n
    mindel Empty {isnode = ()}
    mindel (Node t Empty x r) = x , CBB-Leaf (swap t) r
    mindel (Node t (Node t1 l1 x l2) y r) with mindel (Node t1 l1 x l2)
    ...                                       | min , l' = min , CBB-NodeL t l' y r

    del : ∀ {n c} → Key → (t : RBT' n c) → CBBRBT c n
    del k Empty = [ nv Empty ]
    del k (Node {c = c} t l (k' , v') r) with compare k k'
    ...                                     | Less    = CBB-NodeL t (del k l) (k' , v') r 
    ...                                     | Greater = CBB-NodeR t l (k' , v') (del k r)
    del k (Node t l (k' , v') Empty) | Equal = CBB-Leaf t l
    del k (Node t l (k' , v') (Node tr r1 x r2)) | Equal with mindel (Node tr r1 x r2)
    ...                                                     | a , r' = CBB-NodeR t l a r'

    RBT = Σ(\ m → Σ \ c → RBT' m c)

    blackenroot : ∀ {n c} → BBRBT n c → RBT
    blackenroot (BB Empty) = _ , _ , Empty 
    blackenroot (BB (Node Black l x r)) = _ , _ , Node Black l x r
    blackenroot (nv t) = _ , _ , t

    delete : Key → RBT → RBT
    delete k (_ , c , t) = blackenroot (get (forgetC c (del k t)))

    -- ----------------------------------------------------------------------
    -- insert

    ARBT : Nat → RBColor → Set 
    ARBT m c = Either (LeftARBT m c) (RightARBT m c)

    InsResult : RBColor → Nat → Set
    InsResult Black m = Σi (\ c → RBT' m c)
    InsResult Red m = Σi (λ c → ARBT m c)

    promote : ∀ c {m} → InsResult c m → Σi (λ c → ARBT m c)
    promote Black [ t ] = [ Inl (nv t) ] -- could be Inr
    promote Red t = t

    IR-RBT : ∀ {c m} → RBT' m c → InsResult c m
    IR-RBT {Black} t = [ t ]
    IR-RBT {Red} t = [ Inl (nv t) ]  -- could be Inr

    balanceLeftLeft : ∀ {c n m lc rc} → BalanceType c m n → LeftARBT n lc → (Key × Value) → RBT' n rc → BalanceResult c m
    balanceLeftLeft t (RR (Node Red a x b) y c) z d = BR-Node-1 t (Node Black a x b) y (Node Black c z d)
    balanceLeftLeft t (nv a) z d = BR-Node t a z d

    balanceLeftEither : ∀ {c n m lc rc} → BalanceType c m n → ARBT n lc → (Key × Value) → RBT' n rc → BalanceResult c m
    balanceLeftEither t (Inl l) x r = balanceLeftLeft t l x r
    balanceLeftEither t (Inr l) x r = balanceLeft t l x r

    balanceRightRight : ∀ {c m n lc rc} → BalanceType c m n → RBT' n lc → (Key × Value) → RightARBT n rc → BalanceResult c m
    balanceRightRight t a x (RR b y (Node Red c z d)) = BR-Node-1 t (Node Black a x b) y (Node Black c z d)
    balanceRightRight t a z (nv d) = BR-Node t a z d

    balanceRightEither : ∀ {c n m lc rc} → BalanceType c m n → RBT' n lc → (Key × Value) → ARBT n rc → BalanceResult c m
    balanceRightEither t l x (Inl r) = balanceRight t l x r
    balanceRightEither t l x (Inr r) = balanceRightRight t l x r

    IR-NodeL : ∀ {c m n cl cr} → NodeType c m n cl cr → InsResult cl n → Key × Value → RBT' n cr → InsResult c m
    IR-NodeL {cl = cl} Black l x r = balanceLeftEither Black (get (promote cl l)) x r
    IR-NodeL Red [ l ] x r = [ Inl (LeftARBT-RedNode l x r) ]

    IR-NodeR : ∀ {c m n cl cr} → NodeType c m n cl cr → RBT' n cl → Key × Value → InsResult cr n → InsResult c m
    IR-NodeR {cr = cr} Black l x r = balanceRightEither Black l x (get (promote cr r))
    IR-NodeR Red l x [ r ] = [ Inr (RightARBT-RedNode l x r) ]

    ins : ∀ {m c} → Key × Value → RBT' m c → InsResult c m
    ins x Empty = [ Node Red Empty x Empty ]
    ins (k1 , v1) (Node {cl = cl} t l (k2 , v2) r) with compare k1 k2
    ... | Less = IR-NodeL t (ins (k1 , v1) l) (k2 , v2) r
    ... | Equal = IR-RBT (Node t l (k1 , v1) r)
    ... | Greater = IR-NodeR t l (k2 , v2) (ins (k1 , v1) r)
  
