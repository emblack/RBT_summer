open import Preliminaries

module MergedTrees2 where

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- the code
    data Color : Set where
      Red : Color
      Black : Color
      DoubleBlack : Color

    data RAllowed : Set where
      Yes No : RAllowed

    data BBAllowed : Set where
      Yes No : BBAllowed

    data RRViol : Set where
      Left Right : RRViol

    data NodeInfo : Set where
      v  : RRViol → NodeInfo
      nv : RAllowed → BBAllowed → NodeInfo

    data EmptyType : NodeInfo → Nat → Set where
      Black : ∀ {i} → EmptyType i 1
      DoubleBlack : ∀ {ra} → EmptyType (nv ra Yes) 2

    data NodeType : NodeInfo → (thisHeight : Nat) (childrenHeight : Nat) (leftChildCanBeRed : RAllowed) (rightChildCanBeRed : RAllowed) → Set where
      Black       : ∀ {n i} → NodeType i (S n) n Yes Yes
      Red         : ∀ {n ba} → NodeType (nv Yes ba) n n No No
      DoubleBlack : ∀ {n ra} → NodeType (nv ra Yes) (S (S n)) n Yes Yes
      ARedL       : ∀ {n} → NodeType (v Left) n n Yes No
      ARedR       : ∀ {n} → NodeType (v Right) n n No Yes

    BlackNodeType : Nat → Nat → Set
    BlackNodeType m n = NodeType (nv No Yes) m n Yes Yes

    RedBlackNodeType : Nat → Nat → RAllowed → Set
    RedBlackNodeType m n ra = NodeType (nv Yes No) m n ra ra

    -- RAllowed and BBAllowed tell you what can be at the root
    data RBT' : Nat → (i : NodeInfo) → Set where
      Empty : ∀ {n i} → (t : EmptyType i n) → RBT' n i
      Node  : ∀ {n m i racl racr}
              → (t : NodeType i m n racl racr)
              → (l : RBT' n (nv racl No))
              → (x : Key × Value)
              → (r : RBT' n (nv racr No))
              → RBT' m i

    RBT : Nat → Set 
    RBT n = RBT' n (nv Yes No)

    BBRBT : Nat → Set 
    BBRBT n = RBT' n (nv Yes Yes)

    NonRedBBRBT : Nat → Set 
    NonRedBBRBT n = RBT' n (nv No Yes)

    {- An almost well red tree, or an ARBT, is either a tree with a red
       root and at most one red child, or a regular RBT.  We call an ARBT
       with a possible violation in the left child a LeftARBT, and an ARBT
       with a possible violation in the right child a RightARBT. 

       Red is always allowed, DoubleBlack is never allowed.
    -}
    LeftARBT : Nat → Set
    LeftARBT n = RBT' n (v Left)

    RightARBT : Nat → Set
    RightARBT n = RBT' n (v Right)

    wetr : ∀ {n ra bba} → EmptyType (nv No bba) n → EmptyType (nv ra bba) n
    wetr Black = Black
    wetr DoubleBlack = DoubleBlack

    wetr2 : ∀ {x t n} → EmptyType (v x) n → EmptyType t n
    wetr2 Black = Black

    wntr : ∀ {ra bba m n racl racr} → NodeType (nv No bba) m n racl racr → NodeType (nv ra bba) m n racl racr
    wntr Black = Black
    wntr DoubleBlack = DoubleBlack

    wr : ∀ {n ra bba} → RBT' n (nv No bba) → RBT' n (nv ra bba)
    wr (Empty c) = Empty (wetr c)
    wr (Node c l x r) = Node (wntr c) l x r

    wry : ∀ {n ra bba} → RBT' n (nv ra bba) → RBT' n (nv Yes bba)
    wry (Empty Black) = Empty Black
    wry (Empty DoubleBlack) = Empty DoubleBlack 
    wry (Node Black l x r) = Node Black l x r
    wry (Node Red l x r) = Node Red l x r
    wry (Node DoubleBlack l x r) = Node DoubleBlack l x r 

    wbby : ∀ {n ra bba} → RBT' n (nv ra bba) → RBT' n (nv ra Yes)
    wbby (Empty Black) = Empty Black
    wbby (Empty DoubleBlack) = Empty DoubleBlack 
    wbby (Node Black l x r) = Node Black l x r
    wbby (Node Red l x r) = Node Red l x r
    wbby (Node DoubleBlack l x r) = Node DoubleBlack l x r 

    balanceBBAllowed : ∀ {n m} → (c : BlackNodeType m n) → BBAllowed
    balanceBBAllowed Black = No
    balanceBBAllowed DoubleBlack = Yes

    balanceRedAllowed : {n m : Nat} → (c : BlackNodeType m n) → RAllowed
    balanceRedAllowed Black = Yes
    balanceRedAllowed DoubleBlack = No

    same : ∀ {m n} → (t : NodeType (nv No Yes) m n Yes Yes) → NodeType (nv No (balanceBBAllowed t)) m n Yes Yes 
    same Black = Black
    same DoubleBlack = DoubleBlack

    decrement : ∀ {m n} → (t : NodeType (nv No Yes) m n Yes Yes) → Σ \ arc → NodeType (nv (balanceRedAllowed t) (balanceBBAllowed t)) m (S n) arc arc 
    decrement Black = _ , Red
    decrement DoubleBlack = _ , Black

    balanceLeft : ∀ {n m} → (t : BlackNodeType m n) → RightARBT n → (Key × Value) → RBT n → RBT' m (nv (balanceRedAllowed t) (balanceBBAllowed t))
    -- principal case
    balanceLeft t (Node ARedR a x (Node Red b y c)) z d = Node (snd (decrement t)) (Node Black (wr a) x (wr b)) y (Node Black (wr c) z d) 
    -- otherwise keep it the same
    balanceLeft t (Node ARedR a x (Node Black b y c)) z d  = wr (Node (same t) (Node Red a x (Node Black b y c)) z d)
    balanceLeft t (Node ARedR a x (Empty Black)) z d  = wr (Node (same t) (Node Red a x (Empty Black)) z d) 
    balanceLeft t (Node Black a x b) z d = wr (Node (same t) (Node Black a x b) z d)
    balanceLeft t (Empty t') z d = wr (Node (same t) (Empty (wetr2 t')) z d)

    balanceRight : ∀ {n m} → (t : BlackNodeType m n) → RBT n → (Key × Value) → LeftARBT n → RBT' m (nv (balanceRedAllowed t) (balanceBBAllowed t))
    -- principal case
    balanceRight t a x (Node ARedL (Node Red b y c) z d) = Node (snd (decrement t)) (Node Black a x (wr b)) y (Node Black (wr c) z (wr d))
    -- otherwise keep it the same
    balanceRight t a x (Node ARedL (Empty Black) z d) = wr (Node (same t) a x (Node Red (Empty Black) z d))
    balanceRight t a x (Node ARedL (Node Black b y c) z d) = wr (Node (same t) a x (Node Red (Node Black b y c) z d))
    balanceRight t a x (Node Black c z d) = wr (Node (same t) a x (Node Black c z d))
    balanceRight t a x (Empty t') = wr (Node (same t) a x (Empty (wetr2 t')))

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
