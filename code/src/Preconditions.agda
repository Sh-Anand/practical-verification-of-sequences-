module Preconditions where

open import Haskell.Prelude renaming (length to lengthT)

open import DataTypes

open import Agda.Builtin.Equality

data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} {x y : A} → (P : A → Set) → x ≡ y → P x → P y
subst P refl p = p

begin_ : {A : Set} → {x y : A} → x ≡ y → x ≡ y
begin p = p

_∎ : {A : Set} → (x : A) → x ≡ x
x ∎ = refl

_=⟨_⟩_ : {A : Set} → (x : A) → {y z : A} → x ≡ y → y ≡ z → x ≡ z
x =⟨ p ⟩ q = trans p q

_=⟨⟩_ : {A : Set} → (x : A) → {y : A} → x ≡ y → x ≡ y
x =⟨⟩ q = x =⟨ refl ⟩ q

infix 1 begin_
infix 3 _∎
infixr 2 _=⟨_⟩_
infixr 2 _=⟨⟩_

extract : {a b : Set} -> a -> a ≡ b -> b
extract a refl = a

-- Checks whether the given sequence is empty or not
isNotEmptySequence : {a : Set} -> Seq a -> Bool
isNotEmptySequence (Sequence EmptyT) = false
isNotEmptySequence _ = true

--Checks whether given viewR is empty or not
isNotEmptyViewR : {a : Set} -> ViewR a -> Bool
isNotEmptyViewR EmptyR = false
isNotEmptyViewR _ = true

--Checks whether given viewL is empty or not
isNotEmptyViewL : {a : Set} -> ViewL a -> Bool
isNotEmptyViewL EmptyL = false
isNotEmptyViewL _ = true

--Checks whether given viewRTree is empty or not
isNotEmptyViewRTree : {a : Set} -> ViewRTree a -> Bool
isNotEmptyViewRTree EmptyRTree = false
isNotEmptyViewRTree _ = true

--Checks whether given viewLTree is empty or not
isNotEmptyViewLTree : {a : Set} -> ViewLTree a -> Bool
isNotEmptyViewLTree EmptyLTree = false
isNotEmptyViewLTree _ = true

isNotEmptyFingerTree : {a : Set} -> FingerTree a -> Bool
isNotEmptyFingerTree EmptyT = false
isNotEmptyFingerTree _ = true

isNotNothing : {a : Set} -> Maybe a -> Bool
isNotNothing Nothing = false
isNotNothing _ = true

isSameLengthSeq : {a b : Set} -> Seq a -> Seq b -> Bool
isSameLengthSeq (Sequence EmptyT) (Sequence EmptyT) = true
isSameLengthSeq (Sequence (Single x)) (Sequence (Single y)) = true
isSameLengthSeq (Sequence (Deep v1 _ _ _)) (Sequence (Deep v2 _ _ _)) = v1 == v2
isSameLengthSeq _ _ = false

isSameLengthFingerTree : {a b : Set} -> FingerTree a -> FingerTree b -> Bool
isSameLengthFingerTree EmptyT EmptyT = true
isSameLengthFingerTree (Single _) (Single _) = true
isSameLengthFingerTree (Deep v1 _ _ _) (Deep v2 _ _ _) = v1 == v2
isSameLengthFingerTree _ _ = false

isSameLengthList : {a b : Set} -> List a -> List b -> Bool
isSameLengthList [] [] = true
isSameLengthList (_ ∷ _) [] = false
isSameLengthList [] (_ ∷ _) = false 
isSameLengthList (_ ∷ xs) (_ ∷ ys) = isSameLengthList xs ys

nonEmptySeq->nonEmptyFingerTree : {a : Set} -> (xs : Seq a) -> {IsTrue (isNotEmptySequence xs)} -> IsTrue (isNotEmptyFingerTree (getTreeFromSequence xs))
nonEmptySeq->nonEmptyFingerTree (Sequence (Single x)) = IsTrue.itsTrue
nonEmptySeq->nonEmptyFingerTree (Sequence (Deep x x₁ x₂ x₃)) = IsTrue.itsTrue

notEmptyFTree->notEmptyViewRTree : {a : Set} -> {{sa : Sized a}} -> (ss : FingerTree a) -> IsTrue (isNotEmptyFingerTree ss) -> IsTrue (isNotEmptyViewRTree (viewRTree {{sa}} ss))
notEmptyFTree->notEmptyViewRTree xs@(Single _) p with inspect (viewRTree xs)
... | SnocRTree _ _ with≡ _ = IsTrue.itsTrue

notEmptyFTree->notEmptyViewRTree xs@(Deep _ _ _ x) p with inspect (viewRTree xs)
notEmptyFTree->notEmptyViewRTree xs@(Deep _ _ _ (One _)) p | SnocRTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewRTree xs@(Deep _ _ _ (Two _ _)) p | SnocRTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewRTree xs@(Deep _ _ _ (Three _ _ _)) p | SnocRTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewRTree xs@(Deep _ _ _ (Four _ _ _ _)) p | SnocRTree _ _ with≡ _ = IsTrue.itsTrue

notEmptyFTree->notEmptyViewLTree : {a : Set} -> {{sa : Sized a}} -> (ss : FingerTree a) -> IsTrue (isNotEmptyFingerTree ss) -> IsTrue (isNotEmptyViewLTree (viewLTree {{sa}} ss))
notEmptyFTree->notEmptyViewLTree xs@(Single _) p with inspect (viewLTree xs)
... | ConsLTree _ _ with≡ _ = IsTrue.itsTrue

notEmptyFTree->notEmptyViewLTree xs@(Deep _ x _ _) p with inspect (viewLTree xs)
notEmptyFTree->notEmptyViewLTree (Deep _ (One _) _ _) p | ConsLTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewLTree (Deep _ (Two _ _) _ _) p | ConsLTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewLTree (Deep _ (Three _ _ _) _ _) p | ConsLTree _ _ with≡ _ = IsTrue.itsTrue
notEmptyFTree->notEmptyViewLTree (Deep _ (Four _ _ _ _) _ _) p | ConsLTree _ _ with≡ _ = IsTrue.itsTrue


notEmptyViewRTree->notEmptyViewR : {a : Set} -> (ss : ViewRTree (Elem a)) -> IsTrue (isNotEmptyViewRTree ss) -> IsTrue (isNotEmptyViewR (viewRTreeToviewR ss))
notEmptyViewRTree->notEmptyViewR (SnocRTree _ (Element _)) p = IsTrue.itsTrue

notEmptyViewLTree->notEmptyViewL : {a : Set} -> (ss : ViewLTree (Elem a)) -> IsTrue (isNotEmptyViewLTree ss) -> IsTrue (isNotEmptyViewL (viewLTreeToviewL ss))
notEmptyViewLTree->notEmptyViewL (ConsLTree (Element _) _) p = IsTrue.itsTrue

notEmptySeq->notEmptyViewR : {a : Set} -> (ss : Seq a) -> IsTrue (isNotEmptySequence ss) -> IsTrue (isNotEmptyViewR (viewr ss))
notEmptySeq->notEmptyViewR s@(Sequence xs@(Single _)) p = notEmptyViewRTree->notEmptyViewR (viewRTree xs) (notEmptyFTree->notEmptyViewRTree xs (nonEmptySeq->nonEmptyFingerTree s {p}))
notEmptySeq->notEmptyViewR s@(Sequence xs@(Deep _ _ _ _)) p = notEmptyViewRTree->notEmptyViewR (viewRTree xs) (notEmptyFTree->notEmptyViewRTree xs (nonEmptySeq->nonEmptyFingerTree s {p}))

notEmptySeq->notEmptyViewL : {a : Set} -> (ss : Seq a) -> IsTrue (isNotEmptySequence ss) -> IsTrue (isNotEmptyViewL (viewl ss))
notEmptySeq->notEmptyViewL s@(Sequence xs@(Single _)) p = notEmptyViewLTree->notEmptyViewL (viewLTree xs) (notEmptyFTree->notEmptyViewLTree xs (nonEmptySeq->nonEmptyFingerTree s {p}))
notEmptySeq->notEmptyViewL s@(Sequence xs@(Deep _ _ _ _)) p = notEmptyViewLTree->notEmptyViewL (viewLTree xs) (notEmptyFTree->notEmptyViewLTree xs (nonEmptySeq->nonEmptyFingerTree s {p}))

isSameLengthSeq->isSameLengthFingerTree : {a b : Set} -> (xs : Seq a) -> (ys : Seq b) -> IsTrue (isSameLengthSeq xs ys) -> IsTrue (isSameLengthFingerTree (getTreeFromSequence xs) (getTreeFromSequence ys)) 
isSameLengthSeq->isSameLengthFingerTree (Sequence EmptyT) (Sequence EmptyT) p = IsTrue.itsTrue
isSameLengthSeq->isSameLengthFingerTree (Sequence (Single _)) (Sequence (Single _)) p = IsTrue.itsTrue
isSameLengthSeq->isSameLengthFingerTree (Sequence (Deep v1 _ _ _)) (Sequence (Deep v2 _ _ _)) p = p


isSameLengthList->isSameLengthTailList : {a b : Set} -> (s1 : List a) -> (s2 : List b) -> {nx : NonEmpty s1} -> {ny : NonEmpty s2} -> isSameLengthList s1 s2 ≡ isSameLengthList (tail s1 {{nx}}) (tail s2 {{ny}})
isSameLengthList->isSameLengthTailList xss@(x ∷ xs) yss@(y ∷ ys) {nxs} {nys} = 
    begin
        isSameLengthList xss yss
    =⟨⟩ 
        isSameLengthList (x ∷ xs) (y ∷ ys)
    =⟨⟩
        isSameLengthList xs ys
    =⟨⟩ 
        isSameLengthList (tail xss {{nxs}}) (tail yss {{nys}})
    ∎

lengthListTail : {a b : Set} -> (s1 : List a) -> (s2 : List b) -> {nx : NonEmpty s1} -> {ny : NonEmpty s2} -> IsTrue (isSameLengthList s1 s2) -> IsTrue (isSameLengthList (tail s1 {{nx}}) (tail s2 {{ny}}))
lengthListTail s1@(_ ∷ _) s2@(_ ∷ _) {n1} {n2} p with inspect (isSameLengthList->isSameLengthTailList s1 s2 {n1} {n2})
... | refl with≡ x = p

