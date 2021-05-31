module TemporaryToHaskell where

open import Haskell.Prelude
  hiding (scanl; scanr; scanl1; scanr1; splitAt; take; drop; filter; lookup; zipWith; zip; zipWith3; zip3; reverse; length; unzip)

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
  NodeSized .size (Node2 v _ _) = v
  NodeSized .size (Node3 v _ _ _) = v
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
digitToTree' n (One a) = Single a
{-# COMPILE AGDA2HS digitToTree' #-}


deep : {a : Set} -> {{Sized a}} -> Digit a -> FingerTree (Node a) -> Digit a -> FingerTree a
deep pr m sf = Deep (size pr + size m + size sf) pr m sf
{-# COMPILE AGDA2HS deep #-}


--Elements
data Elem (a : Set) : Set where
  Element : a -> Elem a
{-# COMPILE AGDA2HS Elem deriving Show #-}

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

-- defaultShowList doesn't exist on the Haskell side, so this is a quick workaround to it
{-# FOREIGN AGDA2HS
instance (Show a) => Show (Elem a) where
  showsPrec p (Element a) = showsPrec p a 
#-}

instance
  ElemShow : {{Show a}} -> Show (Elem a)
  ElemShow .showsPrec p (Element a) = showsPrec p a
  ElemShow .showList es = defaultShowList (showsPrec 0) es
--{-# COMPILE AGDA2HS ElemShow #-}


--Sequences
data Seq (a : Set) : Set where
  Sequence : (xs : FingerTree (Elem a))  -> Seq a
{-# COMPILE AGDA2HS Seq deriving Show #-}

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

-- Basic Seqs
-- O(1) EmptyT sequence.
pattern Empty = Sequence EmptyT
--{-# COMPILE AGDA2HS Empty #-}

-- TODO DEFINE OTHER
--  PATTERNS!!

---------------
-- Construction
---------------

-- An empty sequence
empty : {a : Set} -> Seq a
empty = Sequence EmptyT
{-# COMPILE AGDA2HS empty #-}

-- A singleton sequence.
singleton : {a : Set} -> a -> Seq a
singleton x = Sequence (Single (Element x))
{-# COMPILE AGDA2HS singleton #-}

-- <| helper
consTree : {a : Set} -> {{Sized a}} -> a -> FingerTree a -> FingerTree a
consTree a EmptyT = Single a
consTree a (Single b) = deep (One a) EmptyT (One b)
consTree a (Deep s (Four b c d e) m sf) = (Deep (size a + s) (Two a b) (consTree (node3 c d e) m) sf)
consTree a (Deep s (Three b c d) m sf) =
    Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size a + s) (Two a b) m sf
{-# COMPILE AGDA2HS consTree #-}    

-- Add an element to the left end of a sequence.
_<|_ : {a : Set} -> a -> Seq a -> Seq a
x <| Sequence xs = Sequence (consTree (Element x) xs)
{-# COMPILE AGDA2HS _<|_ #-}


-- |> helper
snocTree : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> FingerTree a
snocTree EmptyT a = Single a
snocTree (Single a) b = deep (One a) EmptyT (One b)
snocTree (Deep s pr m (Four a b c d)) e = (Deep (s + size e) pr (snocTree m (node3 a b c)) (Two d e))
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size b) pr m (Two a b)
{-# COMPILE AGDA2HS snocTree #-}

-- Add an element to the right end of a sequence.
_|>_ : {a : Set} -> Seq a -> a -> Seq a
Sequence xs |> x = Sequence (snocTree xs (Element x))
{-# COMPILE AGDA2HS _|>_ #-}

--Machine generate code taken from the source of Data.Sequence.Internal
appendTree0 : {a : Set} -> FingerTree (Elem a) -> FingerTree (Elem a) -> FingerTree (Elem a)
addDigits0 : {a : Set} -> FingerTree (Node (Elem a)) -> Digit (Elem a) -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> FingerTree (Node (Elem a))
appendTree1 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits1 : {a : Set} -> {{Sized a}} -> FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
appendTree2 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits2 : {a : Set} -> {{Sized a}} -> FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
appendTree3 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits3 : {a : Set} -> {{Sized a}} -> FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))
appendTree4 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Node a -> Node a -> Node a -> Node a -> FingerTree (Node a) -> FingerTree (Node a)
addDigits4 : {a : Set} -> {{Sized a}} -> FingerTree (Node (Node a)) -> Digit (Node a) -> Node a -> Node a -> Node a -> Node a -> Digit (Node a) -> FingerTree (Node (Node a)) -> FingerTree (Node (Node a))

appendTree0 EmptyT xs =
    xs
appendTree0 xs EmptyT =
    xs
appendTree0 (Single x) xs =
    consTree x xs
appendTree0 xs (Single x) =
    snocTree xs x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    Deep (s1 + s2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree0 #-}

addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
{-# COMPILE AGDA2HS addDigits0 #-}

appendTree1 EmptyT a xs =
    consTree a xs
appendTree1 xs a EmptyT =
    snocTree xs a
appendTree1 (Single x) a xs =
    consTree x (consTree a xs)
appendTree1 xs a (Single x) =
    snocTree (snocTree xs a) x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + s2) pr1 (addDigits1 m1 sf1 a pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree1 #-}    

addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
{-# COMPILE AGDA2HS addDigits1 #-}

appendTree2 EmptyT a b xs =
    consTree a (consTree b xs)
appendTree2 xs a b EmptyT =
    snocTree (snocTree xs a) b
appendTree2 (Single x) a b xs =
    consTree x (consTree a (consTree b xs))
appendTree2 xs a b (Single x) =
    snocTree (snocTree (snocTree xs a) b) x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + s2) pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2 
{-# COMPILE AGDA2HS appendTree2 #-} 

addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
{-# COMPILE AGDA2HS addDigits2 #-}

appendTree3 EmptyT a b c xs =
    consTree a (consTree b (consTree c xs))
appendTree3 xs a b c EmptyT =
    snocTree (snocTree (snocTree xs a) b) c
appendTree3 (Single x) a b c xs =
    consTree x (consTree a (consTree b (consTree c xs)))
appendTree3 xs a b c (Single x) =
    snocTree (snocTree (snocTree (snocTree xs a) b) c) x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + s2) pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree3 #-} 

addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
{-# COMPILE AGDA2HS addDigits3 #-}

appendTree4 EmptyT a b c d xs =
    consTree a (consTree b (consTree c (consTree d xs)))
appendTree4 xs a b c d EmptyT =
    snocTree (snocTree (snocTree (snocTree xs a) b) c) d
appendTree4 (Single x) a b c d xs =
    consTree x (consTree a (consTree b (consTree c (consTree d xs))))
appendTree4 xs a b c d (Single x) =
    snocTree (snocTree (snocTree (snocTree (snocTree xs a) b) c) d) x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + size d + s2) pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree4 #-} 

addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
{-# COMPILE AGDA2HS addDigits4 #-}

-- Concatenates two sequences
_><_ : {a : Set} -> Seq a -> Seq a -> Seq a
Sequence xs >< Sequence ys = Sequence (appendTree0 xs ys)
{-# COMPILE AGDA2HS _><_ #-}

fromList : {a : Set} -> List a -> Seq a
fromList = foldr _<|_ empty
{-# COMPILE AGDA2HS fromList #-}