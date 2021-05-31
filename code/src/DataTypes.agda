module DataTypes where

open import Haskell.Prelude renaming (length to lengthT)

record Sized (a : Set) : Set where
  field
    size : a -> Int 

open Sized ⦃ ... ⦄ public
{-# COMPILE AGDA2HS Sized class #-}

-- Digits
data Digit (a : Set) : Set where
  One   : a -> Digit a
  Two   : a -> a -> Digit a
  Three : a -> a -> a -> Digit a
  Four  : a -> a -> a -> a -> Digit a
{-# COMPILE AGDA2HS Digit deriving Show #-}


instance
  DigitFoldable : Foldable Digit
  DigitFoldable .foldMap f (One a) = f a
  DigitFoldable .foldMap f (Two a b) = (f a) <> (f b)
  DigitFoldable .foldMap f (Three a b c) = f a <> f b <> f c
  DigitFoldable .foldMap f (Four a b c d) = f a <> f b <> f c <> f d
{-# COMPILE AGDA2HS DigitFoldable #-}

instance
  DigitFunctor : Functor Digit
  DigitFunctor .fmap f (One a) = One (f a)
  DigitFunctor .fmap f (Two a b) = Two (f a) (f b)
  DigitFunctor .fmap f (Three a b c) = Three (f a) (f b) (f c)
  DigitFunctor .fmap f (Four a b c d) = Four (f a) (f b) (f c) (f d)
{-# COMPILE AGDA2HS DigitFunctor #-}

instance
  DigitTraversable : Traversable Digit
  DigitTraversable .traverse f (One a) = One <$> f a
  DigitTraversable .traverse f (Two a b) = Two <$> f a <*> f b
  DigitTraversable .traverse f (Three a b c) = Three <$> f a <*> f b <*> f c
  DigitTraversable .traverse f (Four a b c d) = Four <$> f a <*> f b <*> f c <*> f d
{-# COMPILE AGDA2HS DigitTraversable #-}

instance
  DigitSized : {{Sized a}} -> Sized (Digit a)
  DigitSized .size (One a) = size a
  DigitSized .size (Two a b) = size a + size b
  DigitSized .size (Three a b c) = size a + size b + size c
  DigitSized .size (Four a b c d) = size a + size b + size c + size d
{-# COMPILE AGDA2HS DigitSized #-}


--Nodes
data Node (a : Set) : Set where
  Node2 : Int -> a -> a -> Node a
  Node3 : Int -> a -> a -> a -> Node a
{-# COMPILE AGDA2HS Node deriving Show #-}


instance
  NodeFoldable : Foldable Node
  NodeFoldable .foldMap f (Node2 _ a b) = f a <> f b
  NodeFoldable .foldMap f (Node3 _ a b c) = f a <> f b <> f c
{-# COMPILE AGDA2HS NodeFoldable #-}

instance
  NodeFunctor : Functor Node
  NodeFunctor .fmap f (Node2 v a b) = Node2 v (f a) (f b)
  NodeFunctor .fmap f (Node3 v a b c) = Node3 v (f a) (f b) (f c)
{-# COMPILE AGDA2HS NodeFunctor #-}

instance
  NodeTraversable : Traversable Node
  NodeTraversable .traverse f (Node2 v a b) = Node2 v <$> f a <*> f b
  NodeTraversable .traverse f (Node3 v a b c) = Node3 v <$> f a <*> f b <*> f c
{-# COMPILE AGDA2HS NodeTraversable #-}

instance
  NodeSized : {{Sized a}} -> Sized (Node a)
  NodeSized .size (Node2 v a b) = size a + size b
  NodeSized .size (Node3 v a b c) = size a + size b + size c 
{-# COMPILE AGDA2HS NodeSized #-}

isValidNode : {a : Set} -> {{Sized a}} -> Node a -> Bool
isValidNode (Node2 v x₁ x₂) = v == size x₁ + size x₂
isValidNode (Node3 v x₁ x₂ x₃) = v == size x₁ + size x₂ + size x₃


{-# FOREIGN AGDA2HS
{-# INLINE node2 #-}
#-}
node2 : {a : Set} -> {{Sized a}} -> a -> a -> Node a
node2 a b =  Node2 (size a + size b) a b
{-# COMPILE AGDA2HS node2 #-}

{-# FOREIGN AGDA2HS
{-# INLINE node3 #-}
#-}
node3 : {a : Set} -> {{Sized a}} -> a -> a -> a -> Node a
node3 a b c =  Node3 (size a + size b + size c) a b c
{-# COMPILE AGDA2HS node3 #-}

nodeToDigit : {a : Set} -> Node a -> Digit a
nodeToDigit (Node2 _ a b) = Two a b
nodeToDigit (Node3 _ a b c) = Three a b c
{-# COMPILE AGDA2HS nodeToDigit #-}

--FingerTrees
data FingerTree (a : Set) : Set where
  EmptyT  : FingerTree a
  Single : a -> FingerTree a
  Deep   : Int -> Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
{-# COMPILE AGDA2HS FingerTree deriving Show #-}


instance
  FingerTreeFoldable : Foldable FingerTree
  FingerTreeFoldable .foldMap _ EmptyT = mempty
  FingerTreeFoldable .foldMap f (Single a) = f a
  FingerTreeFoldable .foldMap f (Deep _ pre tree suf) = (foldMap f pre) <> (foldMap (foldMap f) tree) <> (foldMap f suf)
{-# COMPILE AGDA2HS FingerTreeFoldable #-}

instance
  FingerTreeFunctor : Functor FingerTree
  FingerTreeFunctor .fmap _ EmptyT = EmptyT
  FingerTreeFunctor .fmap f (Single a) = Single (f a)
  FingerTreeFunctor .fmap f (Deep v pre tree suf) = Deep v (fmap f pre) (fmap (fmap f) tree) (fmap f suf)
{-# COMPILE AGDA2HS FingerTreeFunctor #-}

instance
  FingerTreeTraversable : Traversable FingerTree
  FingerTreeTraversable .traverse _ EmptyT = pure EmptyT
  FingerTreeTraversable .traverse f (Single a) = Single <$> f a
  FingerTreeTraversable .traverse f (Deep v pre tree suf) = Deep v <$> traverse f pre <*> traverse (traverse f) tree <*> traverse f suf
{-# COMPILE AGDA2HS FingerTreeTraversable #-}

instance
  FingerTreeSized : {{Sized a}} -> Sized (FingerTree a)
  FingerTreeSized .size EmptyT = 0
  FingerTreeSized .size (Single a) = size a
  FingerTreeSized .size (Deep v pr m sf) = v
{-# COMPILE AGDA2HS FingerTreeSized #-}


isValidFingerTree : {a : Set} -> ⦃ Sized a ⦄ -> FingerTree a -> Bool 
isValidFingerTree EmptyT = true
isValidFingerTree (Single x) = true
isValidFingerTree (Deep v pr m sf) = v == size pr + size m + size sf


-- {-# FOREIGN AGDA2HS
-- {-# SPECIALIZE digitToTree :: Digit (Elem a) -> FingerTree (Elem a) #-}
-- {-# SPECIALIZE digitToTree :: Digit (Node a) -> FingerTree (Node a) #-}
-- #-}
digitToTree  : {a : Set} -> {{Sized a}} -> Digit a -> FingerTree a
digitToTree (One a) = Single a
digitToTree (Two a b) = Deep (size a + size b) (One a) EmptyT (One b)
digitToTree (Three a b c) = Deep (size a + size b + size c) (Two a b) EmptyT (One c)
digitToTree (Four a b c d) = Deep (size a + size b + size c + size d) (Two a b) EmptyT (Two c d)
{-# COMPILE AGDA2HS digitToTree #-}

-- | Given the size of a digit and the digit itself, efficiently converts
-- it to a FingerTree.
digitToTree' : {a : Set} -> {{Sized a}} -> Int -> Digit a -> FingerTree a
digitToTree' n (Four a b c d) = Deep n (Two a b) EmptyT (Two c d)
digitToTree' n (Three a b c) = Deep n (Two a b) EmptyT (One c)
digitToTree' n (Two a b) = Deep n (One a) EmptyT (One b)
digitToTree' !_n (One a) = Single a
{-# COMPILE AGDA2HS digitToTree' #-}


deep : {a : Set} -> {{Sized a}} -> Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
deep pr m sf = Deep (size pr + size m + size sf) pr m sf
{-# COMPILE AGDA2HS deep #-}


--Elements
data Elem (a : Set) : Set where
  Element : a -> Elem a
{-# COMPILE AGDA2HS Elem #-}

getElem : Elem a -> a
getElem (Element a) = a
{-# COMPILE AGDA2HS getElem #-}


instance
  ElemFoldable : Foldable Elem
  ElemFoldable .foldMap f (Element a) = f a
{-# COMPILE AGDA2HS ElemFoldable #-}

instance
  ElemFunctor : Functor Elem
  ElemFunctor .fmap f (Element a) = Element (f a)
{-# COMPILE AGDA2HS ElemFunctor #-}

instance
  ElemTraversable : Traversable Elem
  ElemTraversable .traverse f (Element a) = Element <$> f a
{-# COMPILE AGDA2HS ElemTraversable #-}

instance
  ElemSized : Sized (Elem a)
  ElemSized .size _ = 1
{-# COMPILE AGDA2HS ElemSized #-}

instance
  ElemShow : {{Show a}} -> Show (Elem a)
  ElemShow .showsPrec p (Element a) = showsPrec p a
  ElemShow .showList es = defaultShowList (showsPrec 0) es
--{-# COMPILE AGDA2HS ElemShow #-}


--Sequences
data Seq (a : Set) : Set where
  Sequence : (xs : FingerTree (Elem a))  -> Seq a
{-# COMPILE AGDA2HS Seq #-}

--gets the fingertree from the given sequence
getTreeFromSequence : {a : Set} -> Seq a -> FingerTree (Elem a)
getTreeFromSequence (Sequence xs) = xs
{-# COMPILE AGDA2HS getTreeFromSequence #-} 



instance
  SeqFoldable : Foldable Seq
  SeqFoldable .foldMap f (Sequence xs) = foldMap (foldMap f) xs
{-# COMPILE AGDA2HS SeqFoldable #-}

instance
  SeqFunctor : Functor Seq
  SeqFunctor .fmap f (Sequence xs) = Sequence ((fmap (fmap f) xs))
{-# COMPILE AGDA2HS SeqFunctor #-}

instance
  SeqTraversable : Traversable Seq
  SeqTraversable .traverse f (Sequence xs) = Sequence <$> traverse (traverse f) xs
{-# COMPILE AGDA2HS SeqTraversable #-}

instance
  SeqSized : {a : Set} -> Sized (Seq a)
  SeqSized .size (Sequence xs) = size xs
{-# COMPILE AGDA2HS SeqSized #-}

isValidSeq : {a : Set} -> Seq a -> Bool
isValidSeq (Sequence xs) = isValidFingerTree xs

--get length of the current sequence
length : {a : Set} -> Seq a -> Int
length xs = size xs
{-# COMPILE AGDA2HS length #-}


--right end view of the sequence
data ViewR (a : Set) : Set where
  EmptyR : ViewR a 
  _:>_ : Seq a -> a -> ViewR a
{-# COMPILE AGDA2HS ViewR #-}

-- similarly look into data, generic, Generic1

instance
  ViewRFoldable : Foldable ViewR
  ViewRFoldable .foldMap _ EmptyR = mempty
  ViewRFoldable .foldMap f (xs :> x) = foldMap f xs <> f x
{-# COMPILE AGDA2HS ViewRFoldable #-}

instance
  ViewRFunctor : Functor ViewR
  ViewRFunctor .fmap _ EmptyR = EmptyR
  ViewRFunctor .fmap f (xs :> x) = fmap f xs :> f x
{-# COMPILE AGDA2HS ViewRFunctor #-}

instance
  ViewRTraversable : Traversable ViewR
  ViewRTraversable .traverse _ EmptyR = pure EmptyR
  ViewRTraversable .traverse f (xs :> x) = (_:>_) <$> (traverse f xs) <*> (f x)
{-# COMPILE AGDA2HS ViewRTraversable #-}

-- views

data ViewLTree (a : Set) : Set where
  EmptyLTree : ViewLTree a 
  ConsLTree  : a -> FingerTree a -> ViewLTree a
{-# COMPILE AGDA2HS ViewLTree #-}


data ViewRTree (a : Set) : Set where
  EmptyRTree : ViewRTree a 
  SnocRTree  : FingerTree a -> a -> ViewRTree a
{-# COMPILE AGDA2HS ViewRTree #-}

--left end view of sequence
data ViewL (a : Set) : Set where
  EmptyL : ViewL a
  _:<_   : a -> Seq a -> ViewL a
{-# COMPILE AGDA2HS ViewL #-}

--Look at Data, Generic1, Generic

instance
  ViewLFoldable : Foldable ViewL
  ViewLFoldable .foldMap _ EmptyL = mempty
  ViewLFoldable .foldMap f (x :< xs) = f x <> foldMap f xs
{-# COMPILE AGDA2HS ViewLFoldable #-}

instance
  ViewLFunctor : Functor ViewL
  ViewLFunctor .fmap _ EmptyL = EmptyL
  ViewLFunctor .fmap f (x :< xs) = f x :< fmap f xs
{-# COMPILE AGDA2HS ViewLFunctor #-}

instance
  ViewLTraversable : Traversable ViewL
  ViewLTraversable .traverse _ EmptyL = pure EmptyL
  ViewLTraversable .traverse f (x :< xs) = (_:<_) <$> (f x) <*> (traverse f xs)
{-# COMPILE AGDA2HS ViewLTraversable #-}

-- Given a FingerTree, returns a ViewLTree of it
--Look into making the third case's case lambda an inline function instead
viewLTree : {a : Set} -> {{Sized a}} -> FingerTree a -> ViewLTree a
viewLTree EmptyT                = EmptyLTree
viewLTree (Single a)            = ConsLTree a EmptyT
viewLTree (Deep s (One a) m sf) = ConsLTree a (case viewLTree m of
              λ {
                  EmptyLTree          -> digitToTree' (s - size a) sf
                ; (ConsLTree pr m')   -> Deep (s - size a) (nodeToDigit pr) m' sf
              }
            )
viewLTree (Deep s (Two a b) m sf) =
    ConsLTree a (Deep (s - size a) (One b) m sf)
viewLTree (Deep s (Three a b c) m sf) =
    ConsLTree a (Deep (s - size a) (Two b c) m sf)
viewLTree (Deep s (Four a b c d) m sf) =
    ConsLTree a (Deep (s - size a) (Three b c d) m sf) 
{-# COMPILE AGDA2HS viewLTree #-}

viewLTreeToviewL : {a : Set} -> ViewLTree (Elem a) -> ViewL a
viewLTreeToviewL EmptyLTree = EmptyL
viewLTreeToviewL (ConsLTree (Element x) xs) = x :< Sequence xs
{-# COMPILE AGDA2HS viewLTreeToviewL #-}

-- Returns the viewL of a sequence
viewl : {a : Set} -> Seq a -> ViewL a
viewl (Sequence xs)  =  viewLTreeToviewL (viewLTree xs)
{-# COMPILE AGDA2HS viewl #-}



-- Given a FingerTree, returns a ViewRTree of it
--Look into making the third case's case lambda an inline function instead
viewRTree : {a : Set} -> {{Sized a}} -> FingerTree a -> ViewRTree a
viewRTree EmptyT               = EmptyRTree
viewRTree (Single z)            = SnocRTree EmptyT z
viewRTree (Deep s pr m (One z)) = SnocRTree (case viewRTree m of
              λ {
                  EmptyRTree          -> digitToTree' (s - size z) pr
                ; (SnocRTree m' sf)   -> Deep (s - size z) pr m' (nodeToDigit sf)
              }
            ) z
viewRTree (Deep s pr m (Two y z)) =
    SnocRTree (Deep (s - size z) pr m (One y)) z
viewRTree (Deep s pr m (Three x y z)) =
    SnocRTree (Deep (s - size z) pr m (Two x y)) z
viewRTree (Deep s pr m (Four w x y z)) =
    SnocRTree (Deep (s - size z) pr m (Three w x y)) z
{-# COMPILE AGDA2HS viewRTree #-}


viewRTreeToviewR : {a : Set} -> ViewRTree (Elem a) -> ViewR a
viewRTreeToviewR EmptyRTree = EmptyR
viewRTreeToviewR (SnocRTree xs' (Element x)) = Sequence xs' :> x
{-# COMPILE AGDA2HS viewRTreeToviewR #-}

-- Returns the viewR of a sequence
viewr : {a : Set} -> Seq a -> ViewR a
viewr (Sequence xs)  =  viewRTreeToviewR (viewRTree xs)
{-# COMPILE AGDA2HS viewr #-}
