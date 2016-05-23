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

    data AlmostWellRedTree :   Nat  ->  Set where 
         Empty      : AlmostWellRedTree 1
         RedNode    :  ∀ {n}
                     → (l : RBT n ) 
                     → (kv : Key × Value)
                     → (r : RBT n )
                     → AlmostWellRedTree n
         BlackNode  :  ∀ {n}
                      → (l : RBT n ) 
                      → (kv : Key × Value)
                      → (r : RBT n )
                      → AlmostWellRedTree (S n)

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
                          
             

 
    promote : {n : Nat} →  RBT n -> AlmostWellRedTree n
    promote Empty  = Empty 
    promote (RedNode l kv r _ _) = RedNode l kv r
    promote (BlackNode l kv r)   = BlackNode l kv r

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

    balanceBBLeft : {n : Nat} → RightARBT n → (Key × Value) → RBT n → Σ \ (t : RBT (S(S n))) → RootColored t Black
    balanceBBLeft = {!!}

    balanceBBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → Σ \ (t : RBT (S(S n))) → RootColored t Black
    balanceBBRight = {!!}

    balanceBBNeither :  {n : Nat} → RBT n → (Key × Value) → RBT n → Σ \ (t : RBT (S(S n))) → RootColored t DoubleBlack {-is this a problem?-}
    balanceBBNeither = {!!}

    balanceBLeft : {n : Nat} → RightARBT n → (Key × Value) → RBT n → RBT (S n)
    balanceBLeft = {!!}

    balanceBRight :  {n : Nat} → RBT n → (Key × Value) → LeftARBT n → RBT (S n)
    balanceBRight = {!!}

    balanceBNeither :  {n : Nat} → RBT n → (Key × Value) → RBT n → RBT (S n) {-is this necessary?-}
    balanceBNeither = {!!}

    rotateBLeft : {n : Nat} → BBRBT n → (Key × Value) → RBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBLeft = {!!}

    rotateBRight : {n : Nat} → RBT n → (Key × Value) → BBRBT n →
                  Σ \ (t : BBRBT (S n)) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    rotateBRight = {!!}

    {-do I need the case where neither is a BBRBT? I think not, so I'm going to skip.-}

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

    mindelB : {n : Nat} → (s : RBT n) → RootColored s Black →
                       ((Key × Value) × Σ \ (t : BBRBT n) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack)))
    mindelB = {!!}

    mindelR : {n : Nat} → (s : RBT n) → RootColored s Red → ((Key × Value) × BBRBT n)
    mindelR = {!!}

    blackenroot : {n : Nat} → BBRBT n → RBT n
    blackenroot = {!!}

    delB : {n : Nat} → RBT n →  Σ \ (t : BBRBT n) → (Either (RootColoredBBRBT t Black) (RootColoredBBRBT t DoubleBlack))
    delB = {!!}

    delR : {n : Nat} → RBT n → BBRBT n
    delR = {!!}

    delete : {n : Nat} → (t : RBT n) → RBT n
    delete = {!!} {-if rootcolor t is black, send to one func, otherwise send to other -}
  {-  delete RedNode (Node l kv r cl cr) = blackenroot ?
    delete BlackNode = ? why doesn't thi work?-}

    
