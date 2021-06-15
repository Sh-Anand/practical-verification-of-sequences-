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
    foldMapConcat : {a b : Set} -> (f : a -> List b) -> (xs ys : List a) -> foldMap f (xs ++ ys) ≡ foldMap f xs ++ foldMap f ys
    mapConcat : {a b : Set} -> (f : a -> b) -> (xs ys : List a) -> map f (xs ++ ys) ≡ map f xs ++ map f ys
    mapComposition : {a b c : Set} -> (f : b -> c) -> (g : a -> b) -> (xs : List a) -> map f (map g xs) ≡ map (f ∘ g) xs
    preservePure : {a : Set} → {p q : Set → Set} ⦃ ap : Applicative p ⦄ ⦃ aq : Applicative q ⦄ → (t : {x' : Set} → p x' → q x') → (x : a) → t (pure x) ≡ pure x
    preserveApp : {A B : Set} → {p q : Set → Set} ⦃ ap : Applicative p ⦄ ⦃ aq : Applicative q ⦄ → (t : {x' : Set} → p x' → q x') → (g : p (A → B)) (a : p A) 
                                → t (g <*> a) ≡ (t g <*> t a)
    applicativeFmapApp : {a b : Set} → {p : Set → Set} ⦃ ap : Applicative p ⦄ → (f : a -> b) → (x : p a) → (fmap f x) ≡ ((pure f) <*> x)

-- THESE NEED TO BE PROVEN
-- All of these can be proven because a mirror proof already exists
-- splitSnocTree is postulated because we have proven the consTree case and snocTree is simply the mirror of that
postulate 
    isTrueFingerTreeSub : {a : Set} -> ⦃ _ : Sized a ⦄ -> (v : Int) -> (pr : Digit a) -> (xs : FingerTree (Node a)) -> (sf : Digit a) -> IsTrue (isValidFingerTree (Deep v pr xs sf)) -> IsTrue (isValidFingerTree xs)
    appendTree0xsSingle : {a : Set} -> (xs : FingerTree (Elem a)) -> (x : Elem a) -> appendTree0 xs (Single x) ≡ snocTree xs x
    appendTree0Singlexs : {a : Set} -> (x : Elem a) -> (xs : FingerTree (Elem a)) -> appendTree0 (Single x) xs ≡ consTree x xs
    appendTree1xsEmpty : {a : Set} -> ⦃ _ : Sized a ⦄ -> (xs : FingerTree a) -> (n : a) -> appendTree1 xs n EmptyT ≡ snocTree xs n
    appendTree1Singlexs : {a : Set} -> ⦃ _ : Sized a ⦄ -> (x : a) -> (n : a) -> (xs : FingerTree a) -> appendTree1 (Single x) n xs ≡ consTree x (consTree n xs)
    appendTree1xsSingle : {a : Set} -> ⦃ _ : Sized a ⦄ -> (xs : FingerTree a) -> (n : a) -> (x : a) -> appendTree1 xs n (Single x) ≡ snocTree (snocTree xs n) x
    splitSnocTree : {a : Set} -> (n : Nat) -> (z : List a) -> (m : FingerTree (Node^ n (Elem a))) -> (x : Node^ n (Elem a)) 
                -> foldr (node^Folder n) z (snocTree ⦃ sizedNode^ n ⦄ m x) ≡ (foldr (node^Folder n) [] m) ++ (node^Folder n x z)
    splitFoldrFingerTree : {a : Set} -> (n : Nat) -> (z : List a) -> (m : FingerTree (Node^ n (Elem a)))
                        -> foldr (node^Folder n) z m ≡ foldr (node^Folder n) [] m ++ z
    toListSeqConcatSplit : {a : Set} -> (xs ys : Seq a) -> toList (xs >< ys) ≡ toList xs ++ toList ys

appendTree0xsEmpty : {a : Set} -> (xs : FingerTree (Elem a)) -> appendTree0 xs EmptyT ≡ xs
appendTree0xsEmpty EmptyT = refl
appendTree0xsEmpty (Single x) = refl
appendTree0xsEmpty (Deep x x₁ xs x₂) = refl

><Emptyxs : {a : Set} -> (xs : Seq a) -> empty >< xs ≡ xs
><Emptyxs (Sequence xs) = refl