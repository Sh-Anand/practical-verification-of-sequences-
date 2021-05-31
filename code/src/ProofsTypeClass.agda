module ProofsTypeClass where

open import Haskell.Prelude renaming (length to lengthF)

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

-- postulating to prove a proof that comes later
postulate
    fmapCompositionFingerTreePostulate : {a b c : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> fmap ⦃ FingerTreeFunctor ⦄ (f ∘ g) ≡ (fmap f ∘ fmap g)


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

-- viewR

functorViewRTreeId : {a : Set} -> (v : ViewR a) -> fmap id v ≡ id v
functorViewRTreeId EmptyR = refl
functorViewRTreeId (xs :> x) = 
    begin
        fmap id (xs :> x)
    =⟨⟩
        fmap id xs :> id x
    =⟨ cong (_:> x) (functorSeqId xs) ⟩
        xs :> x
    ∎

functorViewRTreeComposition : {a : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (v : ViewR a) -> fmap (f ∘ g) v ≡ (fmap f ∘ fmap g) v
functorViewRTreeComposition f g EmptyR = refl
functorViewRTreeComposition f g (xs :> x) = 
    begin
        fmap (f ∘ g) (xs :> x)
    =⟨⟩
        fmap (f ∘ g) xs :> (f ∘ g) x
    =⟨ cong (_:> (f ∘ g) x) (functorSeqComposition f g xs) ⟩
        (fmap f ∘ fmap g) xs :> (f ∘ g) x
    =⟨⟩
        (fmap f ∘ fmap g) (xs :> x)
    ∎ 


-- viewL

functorViewLTreeId : {a : Set} -> (v : ViewL a) -> fmap id v ≡ id v
functorViewLTreeId EmptyL = refl
functorViewLTreeId (x :< xs) = 
    begin
        fmap id (x :< xs)
    =⟨⟩
        id x :< fmap id xs
    =⟨ cong (id x :<_) (functorSeqId xs) ⟩
        x :< xs
    ∎

functorViewLTreeComposition : {a : Set} -> (f : (b -> c)) -> (g : (a -> b)) -> (v : ViewL a) -> fmap (f ∘ g) v ≡ (fmap f ∘ fmap g) v
functorViewLTreeComposition f g EmptyL = refl
functorViewLTreeComposition f g (x :< xs) = 
    begin
        fmap (f ∘ g) (x :< xs)
    =⟨⟩
        (f ∘ g) x :< fmap (f ∘ g) xs
    =⟨ cong ((f ∘ g) x :<_) (functorSeqComposition f g xs) ⟩
        (f ∘ g) x :< (fmap f ∘ fmap g) xs
    =⟨⟩
        (fmap f ∘ fmap g) (x :< xs)
    ∎ 



--------------------------
-- Proving traversable laws
-- t ∘ traverse f = traverse (t ∘ f) 
-- traverse Identity = Identity
--------------------------

-- Digits
postulate
    traversableLaw1T : {a : Set} -> {f g : Set -> Set} -> ⦃ _ : Applicative f ⦄ -> ⦃ _ : Applicative g ⦄ -> f a -> g a




---------------------------------------
-- Proving Foldable (Functor) laws
-- 1) foldMap f = fold . fmap f
-- 2) foldMap f . fmap g = foldMap (f . g)

--where fold = foldMap id
---------------------------------------

-- Digits

foldableDigitLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (d : Digit a) -> foldMap f d ≡ ((foldMap id) ∘ (fmap f)) d
foldableDigitLaw1 f (One x) = refl
foldableDigitLaw1 f (Two x x₁) = refl
foldableDigitLaw1 f (Three x x₁ x₂) = refl
foldableDigitLaw1 f (Four x x₁ x₂ x₃) = refl

foldableDigitLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (d : Digit a) -> (foldMap f ∘ fmap g) d ≡ foldMap (f ∘ g) d
foldableDigitLaw2 f g (One x) = refl
foldableDigitLaw2 f g (Two x x₁) = refl
foldableDigitLaw2 f g (Three x x₁ x₂) = refl
foldableDigitLaw2 f g (Four x x₁ x₂ x₃) = refl


-- Nodes

foldableNodeLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (n : Node a) -> foldMap f n ≡ ((foldMap id) ∘ (fmap f)) n
foldableNodeLaw1 f (Node2 x x₁ x₂) = refl
foldableNodeLaw1 f (Node3 x x₁ x₂ x₃) = refl

foldableNodeLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (n : Node a) -> (foldMap f ∘ fmap g) n ≡ foldMap (f ∘ g) n
foldableNodeLaw2 f g (Node2 x x₁ x₂) = refl
foldableNodeLaw2 f g (Node3 x x₁ x₂ x₃) = refl

-- as foldMap f n ≡ ((foldMap id) ∘ (fmap f)) n for all node n, we postulate foldMap f = (foldMap id) . fmap f
-- as foldMap f ∘ fmap g) n ≡ foldMap (f ∘ g) n for all node n, we postulate foldmap f ∘ fmap g ≡ foldMap (f ∘ g)
postulate
    foldableNodePostulate1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> foldMap ⦃ NodeFoldable ⦄ f ≡ (foldMap id) ∘ fmap f 
    foldableNodePostulate2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> foldMap ⦃ NodeFoldable ⦄ f ∘ fmap g ≡ foldMap (f ∘ g)


-- Elements

foldableElemLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (e : Elem a) -> foldMap f e ≡ ((foldMap id) ∘ (fmap f)) e
foldableElemLaw1 f (Element x) = refl

foldableElemLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (e : Elem a) -> (foldMap f ∘ fmap g) e ≡ foldMap (f ∘ g) e
foldableElemLaw2 f g (Element x) = refl

-- element analog to node postulates
postulate
    foldableElemPostulate1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> foldMap ⦃ ElemFoldable ⦄ f ≡ (foldMap id) ∘ fmap f 
    foldableElemPostulate2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> foldMap ⦃ ElemFoldable ⦄ f ∘ fmap g ≡ foldMap (f ∘ g)


-- FingerTrees

{-# TERMINATING #-}
foldableFingerTreeLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (fT : FingerTree a) -> foldMap f fT ≡ ((foldMap id) ∘ (fmap f)) fT
foldableFingerTreeLaw1 f EmptyT = refl
foldableFingerTreeLaw1 f (Single x) = refl
foldableFingerTreeLaw1 f (Deep v pr m sf) = 
    begin
        foldMap f (Deep v pr m sf)
    =⟨⟩
        (foldMap f pr) <> (foldMap (foldMap f) m) <> (foldMap f sf)
    =⟨ cong (λ prr → prr <> (foldMap (foldMap f) m) <> (foldMap f sf)) (foldableDigitLaw1 f pr) ⟩
        ((foldMap id) ∘ (fmap f)) pr <> (foldMap (foldMap f) m) <> (foldMap f sf)
    =⟨ cong (λ sff → ((foldMap id) ∘ (fmap f)) pr <> (foldMap (foldMap f) m) <> sff) (foldableDigitLaw1 f sf) ⟩
        ((foldMap id) ∘ (fmap f)) pr <> (foldMap (foldMap f) m) <> ((foldMap id) ∘ (fmap f)) sf
    =⟨ cong (λ i → ((foldMap id) ∘ (fmap f)) pr <> (foldMap i m) <> ((foldMap id) ∘ (fmap f)) sf) (foldableNodePostulate1 f) ⟩
        ((foldMap id) ∘ (fmap f)) pr <> (foldMap ((foldMap id) ∘ (fmap f)) m) <> ((foldMap id) ∘ (fmap f)) sf
    =⟨ cong (λ mm → ((foldMap id) ∘ (fmap f)) pr <> mm <> ((foldMap id) ∘ (fmap f)) sf) (foldableFingerTreeLaw1 ((foldMap id) ∘ (fmap f)) m) ⟩
        ((foldMap id) ∘ (fmap f)) pr <> (((foldMap id) ∘ (fmap ((foldMap id) ∘ (fmap f)))) m) <> ((foldMap id) ∘ (fmap f)) sf
    =⟨ cong (λ i → ((foldMap id) ∘ (fmap f)) pr <> ((foldMap id) ∘ i) m <> ((foldMap id) ∘ (fmap f)) sf) (fmapCompositionFingerTreePostulate (foldMap id) (fmap f)) ⟩ 
        ((foldMap id) ∘ (fmap f)) pr <> (((foldMap id) ∘ (fmap (foldMap id))) ∘ (fmap (fmap f))) m <> ((foldMap id) ∘ (fmap f)) sf
    =⟨ sym (cong (λ mm → ((foldMap id) ∘ (fmap f)) pr <> mm <> ((foldMap id) ∘ (fmap f)) sf) ((foldableFingerTreeLaw1 (foldMap id) (fmap (fmap f) m) ))) ⟩ 
        ((foldMap id) ∘ (fmap f)) pr <> (((foldMap (foldMap id)) ∘ (fmap (fmap f))) m) <> ((foldMap id) ∘ (fmap f)) sf
    =⟨⟩
        ((foldMap id) ∘ (fmap f)) (Deep v pr m sf)
    ∎

foldableFingerTreeLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (fT : FingerTree a) -> (foldMap f ∘ fmap g) fT ≡ foldMap (f ∘ g) fT
foldableFingerTreeLaw2 f g EmptyT = refl
foldableFingerTreeLaw2 f g (Single x) = refl
foldableFingerTreeLaw2 f g (Deep v pr m sf) = 
    begin
        (foldMap f ∘ fmap g) (Deep v pr m sf)
    =⟨⟩
        foldMap f (Deep v (fmap g pr) (fmap (fmap g) m) (fmap g sf))
    =⟨⟩
        (foldMap f ∘ fmap g) pr <> (foldMap (foldMap f) (fmap (fmap g) m)) <> (foldMap f ∘ fmap g) sf
    =⟨ cong (λ prr → prr <> (foldMap (foldMap f) (fmap (fmap g) m)) <> (foldMap f ∘ fmap g) sf ) (foldableDigitLaw2 f g pr) ⟩
        foldMap (f ∘ g) pr <> (foldMap (foldMap f) (fmap (fmap g) m)) <> (foldMap f ∘ fmap g) sf
    =⟨ cong (λ sff → foldMap (f ∘ g) pr <> (foldMap (foldMap f) (fmap (fmap g) m)) <> sff) (foldableDigitLaw2 f g sf) ⟩
        foldMap (f ∘ g) pr <> (foldMap (foldMap f) ∘ fmap (fmap g)) m <> foldMap (f ∘ g) sf
    =⟨ cong (λ mm → foldMap (f ∘ g) pr <> mm <> foldMap (f ∘ g) sf) (foldableFingerTreeLaw2 (foldMap f) (fmap g) m) ⟩
        foldMap (f ∘ g) pr <> foldMap (foldMap f ∘ fmap g) m <> foldMap (f ∘ g) sf
    =⟨ cong (λ i → foldMap (f ∘ g) pr <> foldMap i m <> foldMap (f ∘ g) sf) (foldableNodePostulate2 f g) ⟩ 
        foldMap (f ∘ g) pr <> foldMap (foldMap (f ∘ g)) m <> foldMap (f ∘ g) sf
    =⟨⟩
        foldMap (f ∘ g) (Deep v pr m sf)
    ∎


-- Sequences

foldableSeqLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (xs : Seq a) -> foldMap f xs ≡ ((foldMap id) ∘ (fmap f)) xs
foldableSeqLaw1 f (Sequence xs) = 
    begin
        foldMap f (Sequence xs)
    =⟨⟩
        foldMap (foldMap f) xs
    =⟨ foldableFingerTreeLaw1 (foldMap f) xs ⟩
        (foldMap id ∘ fmap (foldMap f)) xs 
    =⟨ cong (λ i → (foldMap id ∘ fmap i) xs) (foldableElemPostulate1 f) ⟩
        (foldMap id ∘ fmap (foldMap id ∘ fmap f)) xs 
    =⟨ cong (λ i → (foldMap id ∘ i) xs) (fmapCompositionFingerTreePostulate (foldMap id) (fmap f)) ⟩
        (foldMap id ∘ fmap (foldMap id) ∘ fmap (fmap f)) xs 
    =⟨ sym (foldableFingerTreeLaw1 (foldMap id) (fmap (fmap f) xs)) ⟩ 
        ((foldMap id) ∘ (fmap f)) (Sequence xs)
    ∎

foldableSeqLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (xs : Seq a) -> (foldMap f ∘ fmap g) xs ≡ foldMap (f ∘ g) xs
foldableSeqLaw2 f g (Sequence xs) =
    begin
        (foldMap f ∘ fmap g) (Sequence xs)
    =⟨⟩
        foldMap f (Sequence (fmap (fmap g) xs))
    =⟨⟩
        (foldMap (foldMap f) ∘ fmap (fmap g)) xs
    =⟨ foldableFingerTreeLaw2 (foldMap f) (fmap g) xs ⟩
        (foldMap (foldMap f ∘ fmap g)) xs
    =⟨ cong (λ i → foldMap i xs) (foldableElemPostulate2 f g) ⟩
        foldMap (f ∘ g) (Sequence xs)
    ∎

-- viewR

foldableViewRLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (v : ViewR a) -> foldMap f v ≡ ((foldMap id) ∘ (fmap f)) v
foldableViewRLaw1 f EmptyR = refl
foldableViewRLaw1 f (xs :> x) = 
    begin
        foldMap f (xs :> x)
    =⟨⟩
        foldMap f xs <> f x
    =⟨ cong (_<> f x) (foldableSeqLaw1 f xs) ⟩
        ((foldMap id) ∘ (fmap f)) xs <> f x
    =⟨⟩
        ((foldMap id) ∘ (fmap f)) (xs :> x)
    ∎

foldableViewRLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (v : ViewR a) -> (foldMap f ∘ fmap g) v ≡ foldMap (f ∘ g) v
foldableViewRLaw2 f g EmptyR = refl
foldableViewRLaw2 f g (xs :> x) = 
    begin
        (foldMap f ∘ fmap g) (xs :> x)
    =⟨⟩
        (foldMap f ∘ fmap g) xs <> (f ∘ g) x
    =⟨ cong (_<> (f ∘ g) x) (foldableSeqLaw2 f g xs) ⟩
        foldMap (f ∘ g) xs <> (f ∘ g) x
    =⟨⟩
        foldMap (f ∘ g) (xs :> x)
    ∎


-- viewL

foldableViewLLaw1 : {a m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : a -> m) -> (v : ViewL a) -> foldMap f v ≡ ((foldMap id) ∘ (fmap f)) v
foldableViewLLaw1 f EmptyL = refl
foldableViewLLaw1 f (x :< xs) = 
    begin
        foldMap f (x :< xs)
    =⟨⟩
        f x <> foldMap f xs
    =⟨ cong (f x <>_) (foldableSeqLaw1 f xs) ⟩
        f x <> ((foldMap id) ∘ (fmap f)) xs
    =⟨⟩
        ((foldMap id) ∘ (fmap f)) (x :< xs)
    ∎

foldableViewLLaw2 : {a b m : Set} -> ⦃ _ : Monoid m ⦄ -> (f : b -> m) -> (g : a -> b) -> (v : ViewL a) -> (foldMap f ∘ fmap g) v ≡ foldMap (f ∘ g) v
foldableViewLLaw2 f g EmptyL = refl
foldableViewLLaw2 f g (x :< xs) = 
    begin
        (foldMap f ∘ fmap g) (x :< xs)
    =⟨⟩
        (f ∘ g) x <> (foldMap f ∘ fmap g) xs
    =⟨ cong ((f ∘ g) x <>_) (foldableSeqLaw2 f g xs) ⟩
        (f ∘ g) x <> foldMap (f ∘ g) xs
    =⟨⟩
        foldMap (f ∘ g) (x :< xs)
    ∎