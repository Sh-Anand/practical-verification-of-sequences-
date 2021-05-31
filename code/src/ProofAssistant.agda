module ProofAssistant where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Project

-- Simple list length to make proving easier
lengthList : {a : Set} -> List a -> Int
lengthList [] = 0
lengthList (x ∷ xs) = 1 + lengthList xs

Node^ : Nat -> Set -> Set
Node^ zero a = a
Node^ (suc n) a = Node (Node^ n a)

sizedNode^ : {a : Set} -> (n : Nat) -> Sized (Node^ n (Elem a))
sizedNode^ zero = ElemSized
sizedNode^ (suc n) = NodeSized ⦃ sizedNode^ n ⦄

isValidNode^ : {a : Set} -> (n : Nat) -> Node^ n (Elem a) -> Bool
isValidNode^ zero (Element x) = true
isValidNode^ (suc n) (Node2 x x₁ x₂) = x == size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂
isValidNode^ (suc n) (Node3 x x₁ x₂ x₃) = x == size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ + size ⦃ sizedNode^ n ⦄ x₃

node^Folder : {a : Set} -> (n : Nat) -> Node^ n (Elem a) -> List a -> List a
node^Folder zero = flip (foldr _∷_)
node^Folder (suc n) = flip (foldr (node^Folder n))

node^FolderSeq : {a : Set} -> (n : Nat) -> Node^ n (Elem a) -> Seq a -> Seq a
node^FolderSeq zero = flip (foldr _<|_)
node^FolderSeq (suc n) = flip (foldr (node^FolderSeq n))



-- THIS POSTULATE IS UNPROVEN AND NEEDS TO BE PROVEN, BUT CANNOT NOW
-- We assume some properties of lists hold
postulate
    identityInt : (x : Int) -> 0 + x ≡ x
    associativeInt : (x y z : Int) -> x + y + z ≡ x + (y + z)
    commutativeInt : (x y : Int) -> x + y ≡ y + x
    integerEqualityEquivalence : {x y : Int} -> IsTrue (x == y) -> x ≡ y
    lengthListConcat : {a : Set} -> (xs ys : List a) -> lengthList (xs ++ ys) ≡ lengthList xs + lengthList ys
    associativeConcatList : {a : Set} -> (x y z : List a) -> x ++ y ++ z ≡ (x ++ y) ++ z
    identityConcatList : {a : Set} -> (xs : List a) -> xs ≡ xs ++ []

-- THESE NEED TO BE PROVEN
-- All of these can be proven because a mirror proof already exists
-- splitSnocTree is postulated because we have proven the consTree case and snocTree is simply the mirror of that
postulate 
    isTrueFingerTreeSub : {a : Set} -> ⦃ _ : Sized a ⦄ -> (v : Int) -> (pr : Digit a) -> (xs : FingerTree (Node a)) -> (sf : Digit a) -> IsTrue (isValidFingerTree (Deep v pr xs sf)) -> IsTrue (isValidFingerTree xs)
    appendTree0xsEmpty : {a : Set} -> (xs : FingerTree (Elem a)) -> appendTree0 xs EmptyT ≡ xs
    appendTree0xsSingle : {a : Set} -> (xs : FingerTree (Elem a)) -> (x : Elem a) -> appendTree0 xs (Single x) ≡ snocTree xs x
    appendTree0Singlexs : {a : Set} -> (x : Elem a) -> (xs : FingerTree (Elem a)) -> appendTree0 (Single x) xs ≡ consTree x xs
    appendTree1xsEmpty : {a : Set} -> (xs : FingerTree (Node (Elem a))) -> (n : Node (Elem a)) -> appendTree1 xs n EmptyT ≡ snocTree xs n
    appendTree1Singlexs : {a : Set} -> (x : Node (Elem a)) -> (n : Node (Elem a)) -> (xs : FingerTree (Node (Elem a))) -> appendTree1 (Single x) n xs ≡ consTree x (consTree n xs)
    appendTree1xsSingle : {a : Set} -> (xs : FingerTree (Node (Elem a))) -> (n : Node (Elem a)) -> (x : Node (Elem a)) -> appendTree1 xs n (Single x) ≡ snocTree (snocTree xs n) x
    splitSnocTree : {a : Set} -> (n : Nat) -> (z : List a) -> (m : FingerTree (Node^ n (Elem a))) -> (x : Node^ n (Elem a)) 
                -> foldr (node^Folder n) z (snocTree ⦃ sizedNode^ n ⦄ m x) ≡ (foldr (node^Folder n) [] m) ++ (node^Folder n x z)
    splitFoldrFingerTree : {a : Set} -> (n : Nat) -> (z : List a) -> (m : FingerTree (Node^ n (Elem a)))
                        -> foldr (node^Folder n) z m ≡ foldr (node^Folder n) [] m ++ z