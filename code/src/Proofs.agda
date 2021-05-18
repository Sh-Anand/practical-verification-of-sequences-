module Proofs where

open import Haskell.Prelude renaming (length to lengthT)

open import DataTypes

open import Project

open import Preconditions


--------------------------
-- Proving functor laws

-- fmap id f ≡ id f
-- fmap (f ∘ g) f ≡ (fmap f ∘ fmap g) f
--------------------------

-- Digits

functorDigitId : {a : Set} -> (d : Digit a) -> fmap id d ≡ id d
functorDigitId (One x) = refl
functorDigitId (Two x x₁) = refl
functorDigitId (Three x x₁ x₂) = refl
functorDigitId (Four x x₁ x₂ x₃) = refl

functorDigitComposition : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (d : Digit a) -> fmap (f ∘ g) d ≡ (fmap f ∘ fmap g) d
functorDigitComposition f g (One x) = refl
functorDigitComposition f g (Two x x₁) = refl
functorDigitComposition f g (Three x x₁ x₂) = refl
functorDigitComposition f g (Four x x₁ x₂ x₃) = refl


-- Nodes

functorNodeId : {a : Set} -> (n : Node a) -> fmap id n ≡ id n
functorNodeId (Node2 x x₁ x₂) = refl
functorNodeId (Node3 x x₁ x₂ x₃) = refl

functorNodeComposition : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (n : Node a) -> fmap (f ∘ g) n ≡ (fmap f ∘ fmap g) n
functorNodeComposition f g (Node2 x x₁ x₂) = refl
functorNodeComposition f g (Node3 x x₁ x₂ x₃) = refl

-- As fmap id n ≡ id n for all n of type Node, we postulate fmap id ≡ id
-- As fmap (f ∘ g) n ≡ (fmap f ∘ fmap g) n for all n of type node, we postulate that fmap (f ∘ g) ≡ (fmap f ∘ fmap g)
postulate
    fmapIdNodePostulate : {a : Set} -> fmap ⦃ NodeFunctor ⦄ {a} (id {a}) ≡ id {Node a}
    fmapCompositionNodePostulate : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> fmap ⦃ NodeFunctor ⦄ (f ∘ g) ≡ (fmap f ∘ fmap g)


-- Elements

functorElemId : {a : Set} -> (e : Elem a) -> fmap id e ≡ id e
functorElemId (Element x) = refl

functorElemComposition : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (e : Elem a) -> fmap (f ∘ g) e ≡ (fmap f ∘ fmap g) e
functorElemComposition f g (Element x) = refl

-- As fmap id e ≡ id e for all e of type Elem, we postulate fmap id ≡ id
-- As fmap (f ∘ g) e ≡ (fmap f ∘ fmap g) e for all n of type Elem, we postulate that fmap (f ∘ g) ≡ (fmap f ∘ fmap g)
postulate
    fmapIdElemPostulate : {a : Set} -> fmap ⦃ ElemFunctor ⦄ {a} (id {a}) ≡ id {Elem a}
    fmapCompositionElemPostulate : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> fmap ⦃ ElemFunctor ⦄ (f ∘ g) ≡ (fmap f ∘ fmap g)



-- FingerTrees

fingerTreeIdDigits : {a : Set} -> (v : Int) -> (pr : Digit a) -> (m : FingerTree (Node a)) -> (sf : Digit a) -> Deep v (fmap id pr) (fmap (fmap id) m) (fmap id sf) ≡ Deep v pr (fmap (fmap id) m) sf
fingerTreeIdDigits v pr m sf = 
    begin
        Deep v (fmap id pr) (fmap (fmap id) m) (fmap id sf)
    =⟨ cong (λ prr → Deep v prr (fmap (fmap id) m) (fmap id sf)) (functorDigitId pr) ⟩
        Deep v pr (fmap (fmap id) m) (fmap id sf)
    =⟨ cong (λ sff → Deep v (id pr) (fmap (fmap id) m) sff) (functorDigitId sf) ⟩
        Deep v pr (fmap (fmap id) m) sf
    ∎

functorFingerTreeId : {a : Set} -> (fT : FingerTree a) -> fmap id fT ≡ id fT
functorFingerTreeId EmptyT = refl
functorFingerTreeId (Single x) = refl
functorFingerTreeId (Deep v pr m sf) = 
    begin
        fmap id (Deep v pr m sf)
    =⟨⟩
        Deep v (fmap id pr) (fmap (fmap id) m) (fmap id sf)
    =⟨ fingerTreeIdDigits v pr m sf ⟩
        Deep v pr (fmap (fmap id) m) sf
    =⟨ cong (λ i → Deep v pr (fmap i m) sf) fmapIdNodePostulate ⟩
        Deep v pr (fmap id m) sf
    =⟨ cong (λ mm → Deep v pr mm sf) (functorFingerTreeId m) ⟩
        id (Deep v pr m sf)
    ∎


functorFingerTreeComposition : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (fT : FingerTree a) -> fmap (f ∘ g) fT ≡ (fmap f ∘ fmap g) fT
functorFingerTreeComposition f g EmptyT = refl
functorFingerTreeComposition f g (Single x) = refl
functorFingerTreeComposition f g (Deep v pr m sf) = 
    begin
        fmap (f ∘ g) (Deep v pr m sf)
    =⟨⟩
        Deep v (fmap (f ∘ g) pr) (fmap (fmap (f ∘ g)) m) (fmap (f ∘ g) sf)
    =⟨ cong (λ prr → Deep v prr (fmap (fmap (f ∘ g)) m) (fmap (f ∘ g) sf)) (functorDigitComposition f g pr) ⟩
        Deep v ((fmap f ∘ fmap g) pr) (fmap (fmap (f ∘ g)) m) (fmap (f ∘ g) sf)
    =⟨ cong (λ sff → Deep v ((fmap f ∘ fmap g) pr) (fmap (fmap (f ∘ g)) m) sff) (functorDigitComposition f g sf) ⟩
        Deep v ((fmap f ∘ fmap g) pr) (fmap (fmap (f ∘ g)) m) ((fmap f ∘ fmap g)  sf)
    =⟨ cong (λ i → Deep v ((fmap f ∘ fmap g) pr) (fmap i m) ((fmap f ∘ fmap g)  sf)) (fmapCompositionNodePostulate f g) ⟩
        Deep v ((fmap f ∘ fmap g) pr) (fmap ((fmap f) ∘ (fmap g)) m) ((fmap f ∘ fmap g)  sf)
    =⟨ cong (λ mm → Deep v ((fmap f ∘ fmap g) pr) mm ((fmap f ∘ fmap g)  sf)) (functorFingerTreeComposition (fmap f) (fmap g) m) ⟩
        Deep v ((fmap f ∘ fmap g) pr) (((fmap (fmap f)) ∘ (fmap (fmap g))) m) ((fmap f ∘ fmap g)  sf)
    =⟨⟩
        (fmap f ∘ fmap g) (Deep v pr m sf)
    ∎


-- Sequences

functorSeqId : {a : Set} -> (xs : Seq a) -> fmap id xs ≡ id xs
functorSeqId (Sequence xs) =
    begin
        fmap id (Sequence xs)
    =⟨⟩
        Sequence (fmap (fmap id) xs)
    =⟨ cong (λ i → Sequence (fmap i xs)) fmapIdElemPostulate ⟩
        Sequence (fmap id xs)
    =⟨ cong (λ fT → Sequence fT) (functorFingerTreeId xs) ⟩
        Sequence xs
    ∎
    
functorSeqComposition : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (xs : Seq a) -> fmap (f ∘ g) xs ≡ (fmap f ∘ fmap g) xs
functorSeqComposition f g (Sequence xs) = 
    begin
        fmap (f ∘ g) (Sequence xs)
    =⟨⟩
        Sequence (fmap (fmap (f ∘ g)) xs)
    =⟨ cong (λ i → Sequence (fmap i xs)) (fmapCompositionElemPostulate f g) ⟩
        Sequence (fmap (fmap f ∘ fmap g) xs)
    =⟨ cong (λ i → Sequence i) (functorFingerTreeComposition (fmap f) (fmap g) xs) ⟩
        Sequence ((fmap (fmap f) ∘ fmap (fmap g)) xs)
    =⟨⟩
        (fmap f ∘ fmap g) (Sequence xs)
    ∎