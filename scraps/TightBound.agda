open import Preliminaries 

module TightBound where

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- the code
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

    data NodeType : RBColor → (thisHeight : Nat) (childHeight : Nat) (lc : RBColor) (rc : RBColor) → Set where
      Black       : ∀ {n lc rc} → NodeType Black (S n) n lc rc
      Red         : ∀ {n} → NodeType Red n n Black Black

    data RBT' : Nat → RBColor → Set where
      Empty : RBT' 1 Black
      Node  : ∀ {n m c cl cr}
              → (t : NodeType c m n cl cr)
              → (l : RBT' n cl)
              → (x : Key × Value)
              → (r : RBT' n cr)
              → RBT' m c

    data LeftARBT : (n : Nat) → RBColor → Set where
      RedRed  : ∀ {n cr} → (l : RBT' n Red) → (x : Key × Value) → (r : RBT' n cr) → LeftARBT n Red
      nv : ∀ {n c} → RBT' n c → LeftARBT n c

    data RightARBT : (n : Nat) → RBColor → Set where
      RedRed  : ∀ {n cl} → (l : RBT' n cl) → (x : Key × Value) → (r : RBT' n Red) → RightARBT n Red
      nv : ∀ {n c} → RBT' n c → RightARBT n c

    ↑ : BlackColor → Color
    ↑ Black = Black
    ↑ DoubleBlack = DoubleBlack

    ↓ : RBColor → Color
    ↓ Black = Black
    ↓ Red = Red

    data BBRBT : (n : Nat) → Color → Set where
      v  : ∀ {n} → RBT' n Black → BBRBT (S n) DoubleBlack 
      nv : ∀ {n c} → RBT' n c → BBRBT n (↓ c)

    _-1 : BlackColor → RBColor
    Black -1 = Red
    DoubleBlack -1 = Black

    _+1 : RBColor → BlackColor
    Black +1 = DoubleBlack
    Red +1 = Black

    _+_ : Nat → Color → Nat
    n + Red = n
    n + Black = (S n)
    n + DoubleBlack = (S (S n))

    RightARBT-RedNode : ∀ {n cr} → (l : RBT' n Black) → (x : Key × Value) → (r : RBT' n cr) → RightARBT n Red
    RightARBT-RedNode {cr = Black} l x r = nv (Node Red l x r)
    RightARBT-RedNode {cr = Red} l x r = RedRed l x r

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
    BR-Node {c = DoubleBlack} l x r = BB (v (Node Black l x r))

    balanceLeft : ∀ {n lc rc} {c : BlackColor} → RightARBT n lc → (Key × Value) → RBT' n rc → BalanceResult n c
    balanceLeft (RedRed a x (Node Red b y c)) z d = BR-nv (Node (snd (bc-1type _ _)) (Node Black a x b) y (Node Black c z d)) 
    balanceLeft (nv a) z d = BR-Node a z d

    balanceRight : ∀ {n lc rc} → {c : BlackColor} → RBT' n lc → (Key × Value) → LeftARBT n rc → BalanceResult n c
    balanceRight a x (RedRed (Node Red b y c) z d) = BR-nv (Node (snd (bc-1type _ _)) (Node Black a x b) y (Node Black c z d)) 
    balanceRight a z (nv d) = BR-Node a z d

    RotateInputV : RBColor → Σ \ (A : Set) → (A → Color)
    RotateInputV Black = Color , (λ x → x)
    RotateInputV Red = BlackColor , ↑ 

    RotateInputNV : RBColor → Σ \ (A : Set) → (A → RBColor)
    RotateInputNV Black = RBColor , (\ x → x) 
    RotateInputNV Red = Unit , (\ _ → Black)

    PresBlack : RBColor → Σ \ (A : Set) → (A → Color)
    PresBlack Black = BlackColor , ↑ 
    PresBlack Red = Color , (λ x → x)

    black : ∀ c → fst (RotateInputNV c)
    black Black = Black
    black Red = <>

    lemma1 : ∀ c1 c2 → ↓ c1 == ↑ c2 → c1 == Black
    lemma1 Black Black eq = Refl
    lemma1 Black DoubleBlack eq = Refl
    lemma1 Red Black ()
    lemma1 Red DoubleBlack ()

    cast1 : ∀ c n → BalanceResult n (c +1) → Σ (λ oc → BBRBT (S n + ↓ c) (snd (PresBlack c) oc))
    cast1 Black n (BB t) = _ , t
    cast1 Red n (B t) = _ , nv t

    rotateLeft : ∀ {n} 
               → (c : RBColor)
               → ∀ {lc rc lc' rc'}
               → BBRBT n lc' 
               → lc' == (snd (RotateInputV c) lc)
               → (Key × Value)
               → RBT' n rc'
               → rc' == (snd (RotateInputNV c) rc)
               → Σ (\ oc → BBRBT (n + ↓ c) (snd (PresBlack c) oc))
    -- interesting case 1
    rotateLeft rootc (v a) eq x (Node Black b y c) eqr = cast1 _ _ (balanceLeft {c = rootc +1} (RightARBT-RedNode a x b) y c)
    -- interesting case 2
    rotateLeft Black (v a) eq x (Node Red (Node Black b y c) z d) eqr with (balanceLeft {c = Black} (RightARBT-RedNode a x b) y c)
    ...                                                                  | B l' = _ , nv (Node Black l' z d)
    -- keep it the same (FIXME abstract)
    rotateLeft Black (nv a) eql z d Refl = _ , nv (Node Black a z d)
    rotateLeft Red {rc = <>} (nv a) eql z d Refl rewrite lemma1 _ _ eql = _ , nv (Node Red a z d) 
    -- contradictions
    rotateLeft rootc (v a) eq x Empty eqr = {!contradiction!}
    rotateLeft Red {rc = <>} (v a) eq x (Node Red b y c) ()
    rotateLeft Black (v a) eq x (Node Red Empty y c) eqr = {!contraction on a!}

    rotateRight : ∀ {n} 
               → (c : RBColor)
               → ∀ {lc rc}
               → RBT' n (snd (RotateInputNV c) lc)
               → (Key × Value)
               → BBRBT n (snd (RotateInputV c) rc)
               → Σ (\ oc → BBRBT (n + ↓ c) (snd (PresBlack c) oc))
    rotateRight = {!!}


    solve1 : ∀ {c cl cr c' m n} → NodeType c m n cl cr → Σ \ c4 → snd (PresBlack cl) c' == snd (RotateInputV c) c4
    solve1 {cl = Black} Black = _ , Refl
    solve1 {cl = Red} Black = _ , Refl
    solve1 Red = _ , Refl

    solve2 : ∀ {c cl cr m n} → NodeType c m n cl cr → Σ (λ c4 → cr == snd (RotateInputNV c) c4)
    solve2 {cl = Black} Black = _ , Refl
    solve2 {cl = Red} Black = _ , Refl
    solve2 Red = _ , Refl

    del : ∀ {n c} → Key → (t : RBT' n c) → Σ (\ co → BBRBT n (snd (PresBlack c) co))
    del k Empty = _ , nv Empty
    del k (Node {c = c} t l (k' , v') r) with compare k k'
    ...                             | Less    = transport (λ X → X) {!!} (rotateLeft c (snd (del k l)) (snd (solve1 t)) (k' , v') r (snd (solve2 t))) where
    ...                             | Greater = {!!}
    ...                             | Equal   = {!!}

    RBT = Σ(\ m → Σ \ c → RBT' m c)

    blackenroot : ∀ {n c} → BBRBT n c → RBT
    blackenroot (v Empty) = _ , _ , Empty 
    blackenroot (v (Node Black l x r)) = _ , _ , Node Black l x r
    blackenroot (nv t) = _ , _ , t

    delete : Key → RBT → RBT
    delete k (_ , _ , t) = blackenroot (snd (del k t))

{-
    increment : ∀ {m n ra} → RedBlackNodeType m (S n) ra → BlackNodeType m n
    increment Black = DoubleBlack
    increment Red = Black

    rotateRedAllowed : ∀ {m n ra} → (t : RedBlackNodeType m (S n) ra) → RAllowed
    rotateRedAllowed t = balanceRedAllowed (increment t)

    samer : ∀ {m n ra} → (t : RedBlackNodeType m (S n) ra) →  NodeType (nv (rotateRedAllowed t) No) m (S n) ra ra
    samer Black = Black
    samer Red = Red

    -- FIXME: view that would be helpful: a double black tree is either a formal double-black of a black-rooted tree or a promote??

    rotateLeft : ∀ {m n ra} (t : RedBlackNodeType m (S n) ra) 
               → RBT' (S n) (nv ra Yes)
               → (Key × Value)
               → RBT' (S n) (nv ra No) 
               → RBT' m (nv (rotateRedAllowed t) Yes)
    -- move up the double black node (FIXME: there's some duplication here)
    rotateLeft t     (Node DoubleBlack a x b) y (Node Black c z d) = wbby (balanceLeft (increment t) (Node ARedR (Node Black a x b) y c) z d)
    rotateLeft t     (Empty DoubleBlack) y (Node Black c z d) = wbby (balanceLeft (increment t) (Node ARedR (Empty Black) y c) z d)
    rotateLeft Black (Node DoubleBlack a w b) x (Node Red (Node Black c y d) z e) = Node Black (balanceLeft Black (Node ARedR (Node Black a w b) x c) y d) z (wr e)
    rotateLeft Black (Empty DoubleBlack) x (Node Red (Node Black c y d) z e) = Node Black (balanceLeft Black (Node ARedR (Empty Black) x c) y d) z (wr e)
    -- otherwise keep the tree the same
    rotateLeft t (Empty Black) y c = wbby (Node (samer t) (Empty Black) y c)
    rotateLeft t (Node Black a x b) y c = wbby (Node (samer t) (Node Black a x b) y c) 
    rotateLeft t (Node Red a x b) y c = wbby (Node (samer t) (Node Red a x b) y c)
    -- impossible, but too deep for Agda to see 
    rotateLeft _ (Empty DoubleBlack) _ (Empty ())
    rotateLeft Black (Empty DoubleBlack) _ (Node Red (Empty ()) _ _)
    rotateLeft _ (Node DoubleBlack _ _ _) _ (Empty ())
    rotateLeft Black (Node DoubleBlack _ _ _) _ (Node Red (Empty ()) _ _) 

    rotateRight : ∀ {m n ra} (t : RedBlackNodeType m (S n) ra) 
               → RBT' (S n) (nv ra No)
               → (Key × Value)
               → RBT' (S n) (nv ra Yes) 
               → RBT' m (nv (rotateRedAllowed t) Yes)
    rotateRight = {!!}

{-
    rotateBRight : {n : Nat} → RBT n → (Key × Value) → BBRBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBRight (BlackNode a x b) y (DBlackNode c z d)
                              with balanceBBRight a x (RedNode b y (BlackNode c z d) RC-Black)
    ... | (t , proof) = t , proof
    rotateBRight (BlackNode a x b) y DBEmpty
                              with balanceBBRight a x (RedNode b y Empty RC-Empty) 
    ... | (t , proof ) =  t  , proof
    rotateBRight (RedNode a kvw (BlackNode b x c) ablack RC-Black) y (DBlackNode d z e) 
                              with balanceBRight b x (RedNode c y (BlackNode d z e) RC-Black)
    ... | t = promote2BBRBT (BlackNode a kvw t) , Inl (promotePreservesBlack (BlackNode a kvw t) RC-Black)
    {-I defined the output to be a BBRBT and not a RBT that I sent through promote...so that I wouldn't have to write another helper.
    this is inconsistent. which way is better?-}
    rotateBRight (RedNode a kvw (BlackNode b x c) ablack RC-Black) y DBEmpty 
                              with balanceBRight b x (RedNode c y Empty RC-Empty)
    ... | t =  (BlackNode a kvw t) , Inl RC-Black 
    {-cases for completeness--these are annoying me, is it okay that i just left the RBT as arbitrary?
    because the only way rbt will work with empty is if it's also an empty or a rednode with empties.
    does agda know that?-}
    rotateBRight rbt x Empty = (BlackNode rbt x Empty) , (Inl RC-Black)
    rotateBRight rbt y  (BlackNode a x b)  = (BlackNode rbt y (BlackNode a x b)) , (Inl RC-Black)
    rotateBRight rbt y (RedNode a x b ablack bblack) = (BlackNode rbt y (RedNode a x b ablack bblack)) , (Inl RC-Black)
    {-these are cases agda says I need, but are impossible because they have red-red violations.-}
    rotateBRight (RedNode a kvw (RedNode b x c bblack cblack) ablack ()) y DBEmpty
    rotateBRight (RedNode a kvw (RedNode b x c bblack cblack) ablack ()) y (DBlackNode d z e) 

    rotateRRight : {n : Nat} → (l : RBT n) → (RootColored l Black)
                  → (Key × Value)
                  → (r : BBRBT n) → Either (RootColoredBBRBT r Black) (RootColoredBBRBT r DoubleBlack)
                  → BBRBT n
    {-first two are the only relevant cases-}
    rotateRRight (BlackNode a x b) RC-Black y (DBlackNode c z d) RCBBRBT-DoubleBlack =
                                                              promote2BBRBT (balanceBRight a x (RedNode b y (BlackNode c z d) RC-Black))
    rotateRRight (BlackNode a x b) RC-Black y DBEmpty RCBBRBT-DBEmpty = promote2BBRBT (balanceBRight a x (RedNode b y Empty RC-Empty))
    rotateRRight Empty RC-Empty y Empty RCBBRBT-Empty = promote2BBRBT (RedNode Empty y Empty RC-Empty RC-Empty)
    rotateRRight (BlackNode a x b) RC-Black y (BlackNode c z d) RCBBRBT-Black = promote2BBRBT (RedNode (BlackNode a x b) y (BlackNode c z d) RC-Black RC-Black)
    {-These cases can't work because we're going to have a red-red violation, but Agda says I need them for completion-}
    rotateRRight (BlackNode a x b) RC-Black y (RedNode c z d cl rr) (Inl ())
    rotateRRight (BlackNode a x b) RC-Black y (RedNode c z d cl rr) (Inr ())
    rotateRRight Empty RC-Empty y (RedNode c z d cl rr) (Inl ())
    rotateRRight Empty RC-Empty y (RedNode c z d cl rr) (Inr ())
    {-Agda says I need these cases but they won't work because an empty and a black node can't have the same height...what to do?
    I tried casing on the subtree to show that eventually you have to come to a black leaf but it's messy! -}
    rotateRRight Empty RC-Empty y (BlackNode (RedNode (RedNode c kv c₁ cl rr) kv₁ c₂ () rr₁) z d) RCBBRBT-Black
    rotateRRight (BlackNode (RedNode (RedNode a kv a₁ cl rr) kv₁ a₂ () rr₁) x b) RC-Black y Empty RCBBRBT-Empty
-}

    IsNode : ∀ {n i} → RBT' n i → Set
    IsNode (Node _ _ _ _) = Unit
    IsNode (Empty _) = Void

    presBlack : ∀ {n ra} → RBT' n (nv ra No) → RAllowed
    presBlack (Node Red _ _ _) = Yes
    presBlack (Empty t) = No
    presBlack (Node Black _ _ _) = No

    -- FIXME nicer way to do this?
    incrementr : RBT' 1 (nv Yes No) → RBT' (S 1) (nv No Yes)
    incrementr (Empty t) = Empty DoubleBlack
    incrementr (Node Black l x r) = Node DoubleBlack (wry l) x (wry r)
    incrementr (Node Red l x r) = Node Black (wry l) x (wry r) 

    nozeroheight : ∀ {i} → RBT' 0 i → Void
    nozeroheight (Empty ())
    nozeroheight (Node Red t₁ x t₂) = nozeroheight t₁
    nozeroheight (Node ARedL t₁ x t₂) = nozeroheight t₁
    nozeroheight (Node ARedR t₁ x t₂) = nozeroheight t₁

    mindel : {n : Nat} {ra : _} (t : RBT' n (nv ra No)) {isnode : IsNode t} → (Key × Value) × (RBT' n (nv (presBlack t) Yes))
    mindel (Empty t) {()}
    -- FIXME: combine next two cases
    -- at leaf
    mindel (Node Black (Empty Black) x r) = x , incrementr r
    mindel (Node Red (Empty Black) x r) = x , wr (wbby r)
    -- not at leaf; FIXME abstract; convenience split on n
    mindel (Node {n = 0} t (Node t1 a x b) y c) = abort (nozeroheight c)
    mindel (Node {n = S n} Black (Node t1 a x b) y c) with mindel (Node t1 a x b)
    ...                                                  | min , l'  = x , rotateLeft Black (wry l') y c
    mindel (Node {n = S n} Red (Node Black a x b) y c) with mindel {ra = No} (Node Black a x b)
    ...                                                   | min , l' = min , rotateLeft Red l' y c 

    weakendel : ∀ {ra m n racl racr} → NodeType (nv ra No) m n racl racr → Σ \ ra' → NodeType (nv Yes No) m n ra' ra'
    weakendel Black = _ , Black
    weakendel Red = _ , Red

    lemma : ∀ {n} → (l : RBT' n (nv No No)) → presBlack l == No
    lemma (Empty t) = Refl
    lemma (Node Black l x l₁) = Refl

    del : ∀ {n ra} → Key → (t : RBT' n (nv ra No)) → RBT' n (nv (presBlack t) Yes)
    del k (Empty Black) = Empty Black
    -- n is 0, break out this case because some of the lemmas assumes n is non-zero for convienience
    del k' (Node {n = 0} t l (k , val) r) = abort (nozeroheight l)  
    -- n is non-zero
    del k' (Node {n = S n} t l (k , val) r) with compare k' k 
    -- LESS case (FIXME abstract?, matching t makes a lot of things definitional)
    del k' (Node {S n} Black l (k , val) r) | Less = rotateLeft Black (wry (del k' l)) (k , val) r 
    del k' (Node {S n} Red l (k , val) r)   | Less with (del k' l)
    ...                                               | l' rewrite (lemma l) = rotateLeft Red l' (k , val) r
    -- GREATER case (FIXME abstract?, matching t makes a lot of things definitional)
    del k' (Node {S n} Black l (k , val) r) | Greater = rotateRight Black l (k , val) (wry (del k' r))
    del k' (Node {S n} Red l (k , val) r)   | Greater with (del k' r)
    ...                                                  | r' rewrite (lemma r) = rotateRight Red l (k , val) r'
    -- EQUAL, empty on right, return the left node modified
    del k' (Node {S .0} Black (Empty Black) (k , val) (Empty Black)) | Equal = Empty DoubleBlack
    del k' (Node {S .0} Black (Node Red l x l₁) (k , val) (Empty Black)) | Equal = Node Black (wr l) x (wr l₁)
    del k' (Node {S .0} Red (Empty Black) (k , val) (Empty Black)) | Equal = Empty Black
    -- EQUAL, empty on right, contradiction
    del k' (Node {S .0} Red (Node Black l x l₁) (k , val) (Empty Black)) | Equal = abort (nozeroheight l)
    del k' (Node {S .0} Black (Node Black l x l₁) (k , val) (Empty Black)) | Equal = abort (nozeroheight l)
    -- EQUAL non-empty on right (FIXME abstract?, matching makes a lot of things definitional)
    del k' (Node {S n} Black l (k , val) (Node t1 r1 x r2)) | Equal with mindel (Node t1 r1 x r2)
    ... | min , r' = rotateRight Black l min (wry r') 
    del k' (Node {S n} Red l (k , val) (Node Black r1 x r2)) | Equal with mindel {ra = No} (Node Black r1 x r2) 
    del k' (Node {S n} Red l (k , val) (Node Black r1 x r2)) | Equal | min , r' = rotateRight Red l min r'

    blackenroot : {n : Nat} → BBRBT n → Σ(\ m → RBT m)
    blackenroot (Empty t) = _ , Empty Black
    blackenroot (Node _ l x r) = _ , Node Black (wry l) x (wry r)

    delete : {n : Nat} → Key → (t : RBT n) → Σ(\ m → RBT m)
    delete k t = blackenroot (wry (del k t))
-}
