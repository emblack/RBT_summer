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
    balanceBBLeft = {!!}

    balanceBBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → Σ \ (t : RBT (S(S n))) → RootColored t Black
    balanceBBRight = {!!}

    balanceBBNeither :  {n : Nat} → RBT n → (Key × Value) → RBT n → Σ \ (t : BBRBT (S(S n))) → RootColoredBBRBT t DoubleBlack {-is this a problem?-}
    balanceBBNeither = {!!}

    {-If balance takes a B root, then there are the same three cases as above, except in each case, balance simply returns an RBT.-}
    balanceBLeft : {n : Nat} → RightARBT n → (Key × Value) → RBT n → RBT (S n)
    balanceBLeft = {!!}

    balanceBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → RBT (S n)
    balanceBRight = {!!}

    balanceBNeither :  {n : Nat} → RBT n → (Key × Value) → RBT n → RBT (S n) {-is this necessary?-}
    balanceBNeither = {!!}

    {-Rotate can either take a tree with a red root or a black root. If the root is black, at most one of the left or right child
    is a BBRBT, with the other child an RBT. Then, balance returns a BBRBT with a black or double black root.-}

    rotateBLeft : {n : Nat} → BBRBT n → (Key × Value) → RBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBLeft = {!!}

    rotateBRight : {n : Nat} → RBT n → (Key × Value) → BBRBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBRight = {!!}

    {-do I need the case where neither is a BBRBT? I think not, so I'm going to skip.-}

    {-If rotate takes a tree with a red root, there are the same cases except there is the added restriction that there can be no red-red violations
    from the root. Then, rotate returns a BBRBT.-}
    rotateRLeft : {n : Nat} → (l : BBRBT n) → Either (RootColoredBBRBT l Black) (RootColoredBBRBT l DoubleBlack)
                  → (Key × Value)
                  → (r : RBT n) → (RootColored r Black)
                  → BBRBT n
    rotateRLeft = {!!}

    rotateRRight : {n : Nat} → (l : RBT n) → (RootColored l Black)
                  → (Key × Value)
                  → (r : BBRBT n) → Either (RootColoredBBRBT r Black) (RootColoredBBRBT r DoubleBlack)
                  → BBRBT n
    rotateRRight = {!!}

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

    
