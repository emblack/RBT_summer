open import Preliminaries

module RBTspecs where

  module RBT (Key : Set) (compare : Key -> Key -> Order) (Value : Set) where 

    -- ----------------------------------------------------------------------
    -- the code
    data Color : Set where
      Red : Color
      Black : Color
      DoubleBlack : Color

    data ColorHeight :  Nat → Nat → Set where
        CH-Red : ∀ {n} → ColorHeight n n 
        CH-Black : ∀ {n} → ColorHeight n (S n)
        CH-DoubleBlack :  ∀ {n} → ColorHeight n (S (S n))

    mutual
     data RBT     : Nat → Set where
      Empty       : RBT 1
      RedNode     : ∀ {n}
                   → (l : RBT n) 
                   → (kv : Key × Value)
                   → (r : RBT n)
                   → (cl : RootColored l Black)
                   → (rr : RootColored r Black) 
                   →  RBT (n)
      BlackNode   : ∀ {n}
                   → (l : RBT n) 
                   → (kv : Key × Value)
                   → (r : RBT n)
                   →  RBT (S n) 

     data RootColored : {n : Nat } ->  RBT n -> Color -> Set where 
        RC-Empty : RootColored Empty Black
        RC-Red   :  {n : Nat } {l : RBT n } {kv : Key × Value} {r : RBT n }
                   {cl : RootColored l Black} {cr : RootColored r Black}
                 → RootColored (RedNode l kv r cl cr) Red
        RC-Black :  {n : Nat } {l : RBT n } {kv : Key × Value} {r : RBT n}
                 → RootColored (BlackNode l kv r) Black

{-An almost well red tree, or an ARBT, is either a tree with a red root and at most one red child, or a regular RBT. 
We call an ARBT with a possible violation in the left child a LeftARBT and an ARBT with a possible violation in the right child a RightARBT.-}
    data LeftARBT : Nat -> Set where
               Empty     : LeftARBT 1
               RedNode   :  ∀ {n}
                         → (l : RBT n )
                         → (kv : Key × Value)
                         → (r : RBT n )
                         → (rr : RootColored r Black)
                         → LeftARBT n 
               BlackNode :  ∀ {n}
                         → (l : RBT n)
                         → (kv : Key × Value)
                         → (r : RBT n)
                         → LeftARBT (S n)
                         
    data RightARBT : Nat -> Set where
              Empty     : RightARBT 1
              RedNode   :  ∀ {n}
                         → (l : RBT n )
                         → (kv : Key × Value)
                         → (r : RBT n )
                         → (cl : RootColored l Black)
                         → RightARBT n 
              BlackNode : ∀ {n}
                         → (l : RBT n)
                         → (kv : Key × Value)
                         → (r : RBT n)
                         → RightARBT (S n)
{-A BBRBT is a tree with a red, black or double black root that has RBTs as children. 
If the root is red, there can be no red-red violations.
Essentially, a BBRBT is an RBT that may have a double black root.-}
    data BBRBT : Nat -> Set where
      Empty     : BBRBT 1
      DBEmpty   : BBRBT 2
      RedNode   :  ∀ {n}
                      → (l : RBT n)
                      → (kv : Key × Value)
                      → (r : RBT n)
                      → (cl : RootColored l Black)
                      → (rr : RootColored r Black)
                      → BBRBT n 
      BlackNode : ∀ {n}
                      → (l : RBT n)
                      → (kv : Key × Value)
                      → (r : RBT n)
                      → BBRBT (S n) 
      DBlackNode : ∀ {n}
                      → (l : RBT n)
                      → (kv : Key × Value)
                      → (r : RBT n)
                      → BBRBT (S (S n))

    data RootColoredBBRBT : {n : Nat } -> BBRBT n -> Color -> Set where 
        RC-Empty : RootColoredBBRBT Empty Black
        RC-DBEmpty : RootColoredBBRBT DBEmpty DoubleBlack
        RC-Red   :  {n : Nat } {l : RBT n } {kv : Key × Value} {r : RBT n }
                   {cl : RootColored l Black} {cr : RootColored r Black}
                 → RootColoredBBRBT (RedNode l kv r cl cr) Red
        RC-Black :  {n : Nat } {l : RBT n } {kv : Key × Value} {r : RBT n}
                 → RootColoredBBRBT (BlackNode l kv r) Black
        RC-DoubleBlack :  {n : Nat } {l : RBT n } {kv : Key × Value} {r : RBT n}
                 → RootColoredBBRBT (DBlackNode l kv r) DoubleBlack

{-A BBARBT is a tree with a red, black, or double black root, with a the right child a LeftARBT OR the left child a RightARBT.
If the root is red, there cannot be any red-red violations and so the tree has to be a regular RBT. -}                      
    data BBARBT : Nat -> Set where   
             Empty         : BBARBT 1
       {-a BBARBT Can have its left child a right ARBT-}
             LBlackNode    : ∀ {n}
                           → (l : RightARBT n )
                           → (kv : Key × Value)
                           → (r : RBT n) 
                           → BBARBT (S n)
       {-or its right child a left ARBT-}
             RBlackNode    :  ∀ {n}
                           → (l : RBT n) 
                           → (kv : Key × Value)
                           → (r : LeftARBT n )
                           → BBARBT (S n) 
             LDBlackNode   :   ∀ {n}
                           → (l : RightARBT n)
                           → (kv : Key × Value)
                           → (r : RBT n) 
                           → BBARBT (S (S n))
       {-or its right child a left ARBT-}
             RDBlackNode   :   ∀ {n}
                           → (l : RBT n)
                           → (kv : Key × Value)
                           → (r : LeftARBT n)
                           → BBARBT (S (S n))
             RedNode       : ∀ {n}
                           → (l : RBT n)
                           → (kv : Key × Value)
                           → (r : RBT n)
                           → (cl : RootColored l Black)
                           → (rr : RootColored r Black)
                           → BBARBT n 
                          
             
{-An RBT fits the definition of every tree we've defined-}
 
    promote2 : {n : Nat} → RBT n -> LeftARBT n
    promote2 Empty =  Empty
    promote2 (RedNode l kv r _ rr) = RedNode l kv r rr
    promote2 (BlackNode l kv r)   = BlackNode l kv r

    promote3 : {n : Nat} → RBT n -> RightARBT n
    promote3 Empty =  Empty
    promote3 (RedNode l kv r cl _) = RedNode l kv r cl
    promote3 (BlackNode l kv r)   = BlackNode l kv r

    promote4 : {n : Nat} → RBT n -> BBRBT n
    promote4 Empty =  Empty
    promote4 (RedNode l kv r cl rr) = RedNode l kv r cl rr
    promote4 (BlackNode l kv r ) = BlackNode l kv r

    promote5 : {n : Nat} → RBT n -> BBARBT n
    promote5 Empty =  BBARBT.Empty 
    promote5 (RedNode l kv r cl rr) = RedNode l kv r cl rr
    promote5 (BlackNode l kv r ) = LBlackNode (promote3 l) kv r 
{-problem: technically, both LBBARBTBlackNode and RRBBARBTBlackNode should equal a normal RBT blacknode. what should I do? Is this going to be a problem?-}

{-confused here-- in meetings, I remembe saying that we included the RBT def in each of the other tree definitions so that the "normal" case of when the tree is actually an RBT is folded into the function. But here, I have to make a different one at least for the BB case because we're trying to prove something different if the input is an RBT. Is this a problem? 
However, we don't have to prove anything different for balanceBNeither, so do I need that function?-}

    {-balance takes a tree with a black or double black root. If the root is double black, there are three input/output possiblities:
    1. left child can be a RightARBT, with the right child an RBT. Then balance returns an RBT with a black root
    2. right child can be a LeftARBT, with the left child an RBT. Then balance returns an RBT with a black root.
    3. Both children are RBTs, then balance returns an BBRBT with a double black root-}

    balanceBBLeft : {n : Nat} → RightARBT n → (Key × Value) → RBT n → Σ \ (t : RBT (S(S n))) → RootColored t Black
    balanceBBLeft (RedNode a kvx (RedNode b kvy c bblack cblack) ablack) kvz d  = (BlackNode (BlackNode a kvx b) kvy (BlackNode c kvz d)) , RC-Black
    {-cases for completeness: problem here.
    In these cases, the tree is actually an RBT, and so balance returns the input tree, which is not what this spec says. HELP!-}
    balanceBBLeft (RedNode a kvx (BlackNode b kvy c) ablack) kvz d  = {!!} , {!!}
    balanceBBLeft (RedNode a kvx Empty ablack) kvz d  = {!!}
    balanceBBLeft (BlackNode a kvx b) kvz d  = {!!}
    {-problem here: if I leave the rbt as d, agda doesn't complain but i know only an empty tree would make this possible.
    If I specify that the rbt is empty, it asks me for the other cases, but I can't have an empty tree and a blacknode of height 1. 
    what to do here?-}
    balanceBBLeft Empty kvx d = {!!}  

    balanceBBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → Σ \ (t : RBT (S(S n))) → RootColored t Black
    balanceBBRight a kvx (RedNode (RedNode b kvy c bblack cblack) kvz d dblack) = (BlackNode (BlackNode a kvx b) kvy (BlackNode c kvz d)) , RC-Black
    {-cases for completeness: same problem as above!-}
    balanceBBRight a kvx (RedNode (BlackNode b kvy c) kvz d dblack) = {!!}
    balanceBBRight a kvx (RedNode Empty kvz d dblack) = {!!}
    balanceBBRight a kvx (BlackNode c kvz d) = {!!}
    balanceBBRight a kvx Empty  = {!!} 

    balanceBBNeither :  {n : Nat} → RBT n → (Key × Value) → RBT n → Σ \ (t : BBRBT (S(S n))) → RootColoredBBRBT t DoubleBlack {-I think this is a problem...-}
    {-when balance is given a BBRBT with no red-red violations, it just returns the input.-}
    balanceBBNeither a kvx b = (DBlackNode a kvx b) , RC-DoubleBlack 

    {-If balance takes a B root, then there are the same three cases as above, except in each case, balance simply returns an RBT.-}
    balanceBLeft : {n : Nat} → RightARBT n → (Key × Value) → RBT n → RBT (S n)
    {-this is the only relevant, violation case-}
    balanceBLeft (RedNode a kvx (RedNode b kvy c cl2 rr2) cl) kvz d = RedNode (BlackNode a kvx b) kvy (BlackNode c kvz d) RC-Black RC-Black
    {-the rest of these cases, the tree is actually already an RBT, and there is no violation, but we need them for completeness-}
    balanceBLeft Empty kv d = BlackNode Empty kv d
    balanceBLeft (BlackNode a kvx b) kvz d = BlackNode (BlackNode a kvx b) kvz d 
    balanceBLeft (RedNode a kvx Empty cl) kvz d = BlackNode (RedNode a kvx Empty cl RC-Empty) kvz d
    balanceBLeft (RedNode a kvx (BlackNode b kvy c) cl) kvz d = BlackNode (RedNode a kvx (BlackNode b kvy c) cl RC-Black) kvz d

    balanceBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → RBT (S n)
    balanceBRight a kvx (RedNode (RedNode b kvy c cl rr) kvz d cr) = RedNode (BlackNode a kvx b) kvy (BlackNode c kvz d) RC-Black RC-Black
    balanceBRight a kvx Empty = BlackNode a kvx Empty
    balanceBRight a kvx (RedNode Empty kvz d cr) = BlackNode a kvx (RedNode Empty kvz d RC-Empty cr)
    balanceBRight a kvx (RedNode (BlackNode b kvy c) kvz d cr) = BlackNode a kvx (RedNode (BlackNode b kvy c) kvz d RC-Black cr)
    balanceBRight a kvx (BlackNode c kvz d) = BlackNode a kvx (BlackNode c kvz d)

    {-i decided balanceBNeither was unecessary because the case where the input is just an RBT is included in the above functions-}


    {-need helper function: if t is black, then promote4 t is black.-}
    promote4color : {n : Nat} → (t1 : RBT n) → (RootColored t1 Black) → (RootColoredBBRBT (promote4 t1) Black)
    promote4color Empty x = RC-Empty
    promote4color (RedNode t1 kv t2 cl rr) ()
    promote4color (BlackNode t1 kv t2) x = RC-Black


    {-Rotate can either take a tree with a red root or a black root. If the root is black, at most one of the left or right child
    is a BBRBT, with the other child an RBT. Then, balance returns a BBRBT with a black or double black root.-}
    rotateBLeft : {n : Nat} → BBRBT n → (Key × Value) → RBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBLeft (DBlackNode a kvx b) kvy (BlackNode c kvz d)
                              with balanceBBLeft (RedNode (BlackNode a kvx b) kvy c RC-Black) kvz d
    ... | (t , proof) = promote4 t , Inl (promote4color t proof)
    rotateBLeft DBEmpty kvy (BlackNode c kvz d)
                              with balanceBBLeft (RedNode Empty kvy c RC-Empty) kvz d
    ... | (t , proof ) = promote4 t  , (Inl (promote4color t proof))
    rotateBLeft (DBlackNode a kvw b) kvx (RedNode (BlackNode c kvy d) kvz e RC-Black eblack)
                              with balanceBLeft (RedNode (BlackNode a kvw b) kvx c RC-Black) kvy d
    ... | t = promote4 (BlackNode t kvz e) , Inl (promote4color (BlackNode t kvz e) RC-Black)
    {-I defined the output to be a BBRBT and not a RBT that I sent through promote...so that I wouldn't have to write another helper.
    this is inconsistent. which way is better?-}
    rotateBLeft DBEmpty kvx (RedNode (BlackNode c kvy d) kvz e RC-Black eblack)
                              with balanceBLeft (RedNode Empty kvx c RC-Empty) kvy d
    ... | t =  (BlackNode t kvz e) , Inl RC-Black 
    {-cases for completeness--these are annoying me, is it okay that i just left the RBT as arbitrary?
    because the only way rbt will work with empty is if it's also an empty or a rednode with empties.
    does agda know that?-}
    rotateBLeft Empty kvx rbt = (BlackNode Empty kvx rbt) , (Inl RC-Black)
    rotateBLeft (BlackNode a kvx b) kvy rbt = (BlackNode (BlackNode a kvx b) kvy rbt) , (Inl RC-Black)
    rotateBLeft (RedNode a kvx b ablack bblack) kvy rbt = (BlackNode (RedNode a kvx b ablack bblack) kvy rbt) , (Inl RC-Black) 
    

    rotateBRight : {n : Nat} → RBT n → (Key × Value) → BBRBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBRight (BlackNode a kvx b) kvy (DBlackNode c kvz d)
                              with balanceBBRight a kvx (RedNode b kvy (BlackNode c kvz d) RC-Black)
    ... | (t , proof) = promote4 t , Inl (promote4color t proof)
    rotateBRight (BlackNode a kvx b) kvy DBEmpty
                              with balanceBBRight a kvx (RedNode b kvy Empty RC-Empty) 
    ... | (t , proof ) = promote4 t  , (Inl (promote4color t proof))
    rotateBRight (RedNode a kvw (BlackNode b kvx c) ablack RC-Black) kvy (DBlackNode d kvz e) 
                              with balanceBRight b kvx (RedNode c kvy (BlackNode d kvz e) RC-Black)
    ... | t = promote4 (BlackNode a kvw t) , Inl (promote4color (BlackNode a kvw t) RC-Black)
    {-I defined the output to be a BBRBT and not a RBT that I sent through promote...so that I wouldn't have to write another helper.
    this is inconsistent. which way is better?-}
    rotateBRight (RedNode a kvw (BlackNode b kvx c) ablack RC-Black) kvy DBEmpty 
                              with balanceBRight b kvx (RedNode c kvy Empty RC-Empty)
    ... | t =  (BlackNode a kvw t) , Inl RC-Black 
    {-cases for completeness--these are annoying me, is it okay that i just left the RBT as arbitrary?
    because the only way rbt will work with empty is if it's also an empty or a rednode with empties.
    does agda know that?-}
    rotateBRight rbt kvx Empty = (BlackNode rbt kvx Empty) , (Inl RC-Black)
    rotateBRight rbt kvy  (BlackNode a kvx b)  = (BlackNode rbt kvy (BlackNode a kvx b)) , (Inl RC-Black)
    rotateBRight rbt kvy (RedNode a kvx b ablack bblack) = (BlackNode rbt kvy (RedNode a kvx b ablack bblack)) , (Inl RC-Black)
    {-these are cases agda says I need, but there are more than in rotateBLeft? Confused.-}
    rotateBRight {._} (RedNode {._} _ _ (RedNode {._} _ _ _ _ _) _ _) _ DBEmpty = {!!} 
    rotateBRight {._} (RedNode {._} _ _ (RedNode {._} _ _ _ _ _) _ _) _ (DBlackNode {_} _ _ _) = {!!} 

    {-do I need the case where neither is a BBRBT? I think not, so I'm going to skip.-}

    {-If rotate takes a tree with a red root, there are the same cases except there is the added restriction that there can be no red-red violations
    from the root. Then, rotate returns a BBRBT.-}
    rotateRLeft : {n : Nat} → (l : BBRBT n) → Either (RootColoredBBRBT l Black) (RootColoredBBRBT l DoubleBlack)
                  → (Key × Value)
                  → (r : RBT n) → (RootColored r Black)
                  → BBRBT n
    {-the first two are the only really relevant cases-}
    rotateRLeft (DBlackNode a kvx b) RCBBRBT-DoubleBlack kvy (BlackNode c kvz d) RC-Black  =
                                                         promote4 (balanceBLeft (RedNode (BlackNode a kvx b) kvy c RC-Black) kvz d)
    rotateRLeft DBEmpty RCBBRBT-DBEmpty kvy (BlackNode c kvz d) RC-Black  = promote4 (balanceBLeft (RedNode Empty kvy c RC-Empty) kvz d)
    rotateRLeft Empty RCBBRBT-Empty kvy Empty RC-Empty = RedNode Empty kvy Empty RC-Empty RC-Empty
    rotateRLeft (BlackNode a kvx b) RCBBRBT-Black kvy (BlackNode c kvz d) (RC-Black) = RedNode (BlackNode a kvx b) kvy (BlackNode c kvz d) RC-Black RC-Black
    {-this shouldn't work, because of different black-heights, why is agda allowing this?-}
    rotateRLeft Empty RCBBRBT-Empty kvy (BlackNode c kvz d) (RC-Black) = RedNode Empty kvy (BlackNode c kvz d) RC-Empty RC-Black
    {-this can't work because we have a rednode where there needs to be a black one but agda says I need this case--so I did a void thing-}
    rotateRLeft (RedNode a kvx b cl rr) (Inl ()) kvy (BlackNode c kvz d) RC-Black
    rotateRLeft (RedNode a kvx b cl rr) (Inr ()) kvy (BlackNode c kvz d) RC-Black 
    rotateRLeft (RedNode a kvx b cl rr) (Inl ()) kxy .Empty RC-Empty
    rotateRLeft (RedNode a kvx b cl rr) (Inr ()) kxy .Empty RC-Empty
    {-agda says that I need the case of a black node and an empty for completeness but they can't work because a black node and an empty tree
    will never have the same black height, so this case won't work! I found a way for agda to see it's dumb but it's messy-}
    rotateRLeft (BlackNode (RedNode (RedNode a kv a₁ cl rr) kv₁ a₂ () rr₁) kvx b) x r .Empty RC-Empty
    

    rotateRRight : {n : Nat} → (l : RBT n) → (RootColored l Black)
                  → (Key × Value)
                  → (r : BBRBT n) → Either (RootColoredBBRBT r Black) (RootColoredBBRBT r DoubleBlack)
                  → BBRBT n
    {-first two are the only relevant cases-}
    rotateRRight (BlackNode a kvx b) RC-Black kvy (DBlackNode c kvz d) RCBBRBT-DoubleBlack =
                                                              promote4 (balanceBRight a kvx (RedNode b kvy (BlackNode c kvz d) RC-Black))
    rotateRRight (BlackNode a kvx b) RC-Black kvy DBEmpty RCBBRBT-DBEmpty = promote4 (balanceBRight a kvx (RedNode b kvy Empty RC-Empty))
    rotateRRight Empty RC-Empty kvy Empty RCBBRBT-Empty = promote4 (RedNode Empty kvy Empty RC-Empty RC-Empty)
    rotateRRight (BlackNode a kvx b) RC-Black kvy (BlackNode c kvz d) RCBBRBT-Black = promote4 (RedNode (BlackNode a kvx b) kvy (BlackNode c kvz d) RC-Black RC-Black)
    {-These cases can't work because we're going to have a red-red violation, but Agda says I need them for completion-}
    rotateRRight (BlackNode a kvx b) RC-Black kvy (RedNode c kvz d cl rr) (Inl ())
    rotateRRight (BlackNode a kvx b) RC-Black kvy (RedNode c kvz d cl rr) (Inr ())
    rotateRRight Empty RC-Empty kvy (RedNode c kvz d cl rr) (Inl ())
    rotateRRight Empty RC-Empty kvy (RedNode c kvz d cl rr) (Inr ())
    {-Agda says I need these cases but they won't work because an empty and a black node can't have the same height...what to do?
    I tried casing on the subtree to show that eventually you have to come to a black leaf but it's messy! -}
    rotateRRight Empty RC-Empty kvy (BlackNode (RedNode (RedNode c kv c₁ cl rr) kv₁ c₂ () rr₁) kvz d) RCBBRBT-Black
    rotateRRight (BlackNode (RedNode (RedNode a kv a₁ cl rr) kv₁ a₂ () rr₁) kvx b) RC-Black kvy Empty RCBBRBT-Empty
    

    {-mindel takes an RBT and deletes the minimum element. It returns a BBRBT and the element deleted.
    If the root color is B, then mindel returns the element deleted and a BBRBT with a B or BB root. 
    If the root color of the input is R, it simply returns the element deleted and a BBRBT.-}

    mindelB : {n : Nat} → (s : RBT n) → RootColored s Black →
                       ((Key × Value) × Σ \ (t : BBRBT n) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack)))
    mindelB = {!!}

    mindelR : {n : Nat} → (s : RBT n) → RootColored s Red → ((Key × Value) × BBRBT n)
    mindelR = {!!}

    {-blackenroot blackens the root of a tree. It takes a BBRBT and returns an RBT.-}
    blackenroot : {n : Nat} → BBRBT n → RBT n
    blackenroot = {!!}

    {-del takes an RBT and an element to delete. 
    1. If the root color is B, then del returns a BBRBT with a black or double black root
    2. If the root color is R, then del returns a BBRBT-}
    delB : {n : Nat} → RBT n →  Σ \ (t : BBRBT n) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    delB = {!!}

    delR : {n : Nat} → RBT n → BBRBT n
    delR = {!!}

    {-Delete takes an RBT and an element to delete and returns an RBT. -}
    delete : {n : Nat} → (t : RBT n) → RBT n
    delete = {!!} {-if rootcolor t is black, send to one func, otherwise send to other -}
  {-  delete RedNode (Node l kv r cl cr) = blackenroot ?
    delete BlackNode = ? why doesn't thi work?-}

    
