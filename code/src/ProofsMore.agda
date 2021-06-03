module ProofsMore where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Project

open import Preconditions

open import ProofAssistant




listSimplify : {a : Set} -> (v : Int) -> (pr : Digit a) -> (m : FingerTree (Node a)) -> (sf : Digit  a) -> toList (Deep v pr m sf) ≡ foldr _∷_ (foldr (flip (foldr _∷_)) (foldr _∷_ [] sf) m) pr
listSimplify v pr m sf = refl

listPrependConact : {a : Set} -> (x : a) -> (xs : List a) -> x ∷ xs ≡ (x ∷ []) ++ xs
listPrependConact x xs = refl


-------------------------------------------------
-- foldr _∷_ (z1 ++ z2) x ≡ foldr _∷_ z1 x ++ z2
-------------------------------------------------

-- Digits

foldrListSplitDigit : {a : Set} -> (z1 z2 : List a) -> (d : Digit a) -> foldr _∷_ (z1 ++ z2) d ≡ foldr _∷_ z1 d ++ z2
foldrListSplitDigit z1 z2 (One x) = refl
foldrListSplitDigit z1 z2 (Two x x₁) = refl
foldrListSplitDigit z1 z2 (Three x x₁ x₂) = refl
foldrListSplitDigit z1 z2 (Four x x₁ x₂ x₃) = refl

-- Nodes

foldrListSplitNode : {a : Set} -> (z1 z2 : List a) -> (n : Node a) -> foldr _∷_ (z1 ++ z2) n ≡ foldr _∷_ z1 n ++ z2
foldrListSplitNode z1 z2 (Node2 x x₁ x₂) = refl
foldrListSplitNode z1 z2 (Node3 x x₁ x₂ x₃) = refl


-----------------------
-- Prepend laws
-----------------------

unWrapElemNode : {a : Set} -> (n : Nat) -> Node^ n (Elem a) -> Node^ n a
unWrapElemNode zero (Element a) = a
unWrapElemNode (suc n) (Node2 v a b) = Node2 v (unWrapElemNode n a) (unWrapElemNode n b)
unWrapElemNode (suc n) (Node3 v a b c) = Node3 v (unWrapElemNode n a) (unWrapElemNode n b) (unWrapElemNode n c)

splitDigitFoldr : {a : Set} -> (z : List a) -> (d : Digit (Elem a)) -> foldr (flip (foldr _∷_)) z d ≡ foldr (flip (foldr _∷_)) [] d ++ z
splitDigitFoldr z (One (Element x)) = refl
splitDigitFoldr z (Two (Element x) (Element x₁)) = refl
splitDigitFoldr z (Three (Element x) (Element x₁) (Element x₂)) = refl
splitDigitFoldr z (Four (Element x) (Element x₁) (Element x₂) (Element x₃)) = refl

splitNode^Foldr : {a : Set} -> (n : Nat) -> (z : List a) -> (nd : Node^ n (Elem a)) -> node^Folder n nd z ≡ node^Folder n nd [] ++ z
splitNode^Foldr zero z (Element x) = refl
splitNode^Foldr (suc n) z (Node2 v a b) = 
    begin
        node^Folder (suc n) (Node2 v a b) z
    =⟨⟩
        flip (foldr (node^Folder n)) (Node2 v a b) z
    =⟨⟩
        node^Folder n a (node^Folder n b z)
    =⟨ splitNode^Foldr n (node^Folder n b z) a ⟩
        node^Folder n a [] ++ node^Folder n b z
    =⟨ cong (node^Folder n a [] ++_) (splitNode^Foldr n z b) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ z
    =⟨ associativeConcatList (node^Folder n a []) (node^Folder n b []) z ⟩
        (node^Folder n a [] ++ node^Folder n b []) ++ z
    =⟨ cong (_++ z) (sym (splitNode^Foldr n (node^Folder n b []) a)) ⟩
        (node^Folder n a (node^Folder n b [])) ++ z
    =⟨⟩
        flip (foldr (node^Folder n)) (Node2 v a b) [] ++ z
    =⟨⟩
        node^Folder (suc n) (Node2 v a b) [] ++ z
    ∎

splitNode^Foldr (suc n) z (Node3 v a b c) = 
    begin
        node^Folder (suc n) (Node3 v a b c) z 
    =⟨⟩
        node^Folder n a (node^Folder n b (node^Folder n c z))
    =⟨ splitNode^Foldr n (node^Folder n b (node^Folder n c z)) a ⟩
        node^Folder n a [] ++ node^Folder n b (node^Folder n c z)
    =⟨ cong (node^Folder n a [] ++_) (splitNode^Foldr n (node^Folder n c z) b) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c z
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ xs) (splitNode^Foldr n z c) ⟩
        node^Folder n a [] ++ (node^Folder n b [] ++ (node^Folder n c [] ++ z))
    =⟨ associativeConcatList (node^Folder n a []) (node^Folder n b []) (node^Folder n c [] ++ z) ⟩
        (node^Folder n a [] ++ node^Folder n b []) ++ (node^Folder n c [] ++ z)
    =⟨ associativeConcatList (node^Folder n a [] ++ node^Folder n b []) (node^Folder n c []) z ⟩
        ((node^Folder n a [] ++ node^Folder n b []) ++ node^Folder n c []) ++ z
    =⟨ cong (_++ z) (sym (associativeConcatList (node^Folder n a []) (node^Folder n b []) (node^Folder n c []))) ⟩
        (node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c []) ++ z
    =⟨ cong (λ xs → (node^Folder n a [] ++ xs) ++ z) (sym (splitNode^Foldr n (node^Folder n c []) b)) ⟩
        (node^Folder n a [] ++ node^Folder n b (node^Folder n c [])) ++ z
    =⟨ cong (_++ z) (sym (splitNode^Foldr n (node^Folder n b (node^Folder n c [])) a )) ⟩
        node^Folder n a (node^Folder n b (node^Folder n c [])) ++ z
    ∎

splitDigitNode^Foldr : {a : Set} -> (n : Nat) -> (z : List a) -> (d : Digit (Node^ n (Elem a))) -> foldr (node^Folder n) z d ≡ foldr (node^Folder n) [] d ++ z
splitDigitNode^Foldr n z (One x) = 
    begin
        node^Folder n x z
    =⟨ splitNode^Foldr n z x ⟩
        node^Folder n x [] ++ z
    ∎
splitDigitNode^Foldr n z (Two x x₁) = 
    begin
        node^Folder n x (node^Folder n x₁ z)
    =⟨ splitNode^Foldr n (node^Folder n x₁ z) x ⟩
        node^Folder n x [] ++ node^Folder n x₁ z
    =⟨ cong (node^Folder n x [] ++_) (splitNode^Foldr n z x₁) ⟩
        node^Folder n x [] ++ node^Folder n x₁ [] ++ z
    =⟨ associativeConcatList (node^Folder n x []) (node^Folder n x₁ []) z ⟩
        (node^Folder n x [] ++ node^Folder n x₁ []) ++ z
    =⟨ cong (_++ z) (sym (splitNode^Foldr n (node^Folder n x₁ []) x)) ⟩
        foldr (node^Folder n) [] (Two x x₁) ++ z
    ∎
splitDigitNode^Foldr n z (Three a b c) = 
    begin
        node^Folder n a (node^Folder n b (node^Folder n c z))
    =⟨ splitNode^Foldr n (node^Folder n b (node^Folder n c z)) a ⟩
        node^Folder n a [] ++ node^Folder n b (node^Folder n c z)
    =⟨ cong (node^Folder n a [] ++_) (splitNode^Foldr n (node^Folder n c z) b) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c z
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ xs) (splitNode^Foldr n z c) ⟩
        (node^Folder n a [] ++ (node^Folder n b [] ++ (node^Folder n c [] ++ z)))
    =⟨ associativeConcatList (node^Folder n a []) (node^Folder n b []) (node^Folder n c [] ++ z) ⟩
        (node^Folder n a [] ++ node^Folder n b []) ++ (node^Folder n c [] ++ z)
    =⟨ associativeConcatList (node^Folder n a [] ++ node^Folder n b []) (node^Folder n c []) z ⟩
        ((node^Folder n a [] ++ node^Folder n b []) ++ node^Folder n c []) ++ z
    =⟨ cong (_++ z) (sym (associativeConcatList (node^Folder n a []) (node^Folder n b []) (node^Folder n c []))) ⟩
        (node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c []) ++ z
    =⟨ cong (λ xs → (node^Folder n a [] ++ xs) ++ z) (sym (splitNode^Foldr n (node^Folder n c []) b)) ⟩
        (node^Folder n a [] ++ node^Folder n b (node^Folder n c [])) ++ z
    =⟨ cong (_++ z) (sym (splitNode^Foldr n (node^Folder n b (node^Folder n c [])) a)) ⟩
        node^Folder n a (node^Folder n b (node^Folder n c [])) ++ z
    ∎
splitDigitNode^Foldr n z (Four a b c d) = 
    begin
        node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d z)))
    =⟨ splitNode^Foldr n (node^Folder n b (node^Folder n c (node^Folder n d z))) a ⟩
        node^Folder n a [] ++ node^Folder n b (node^Folder n c (node^Folder n d z))
    =⟨ cong (node^Folder n a [] ++_) (splitNode^Foldr n (node^Folder n c (node^Folder n d z)) b) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c (node^Folder n d z)
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ xs) (splitNode^Foldr n (node^Folder n d z) c) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c [] ++ node^Folder n d z
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c [] ++ xs) (splitNode^Foldr n z d) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c [] ++ node^Folder n d [] ++ z
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ xs) (associativeConcatList (node^Folder n c []) (node^Folder n d []) z) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ (node^Folder n c [] ++ node^Folder n d []) ++ z
    =⟨ cong (λ xs → node^Folder n a [] ++ node^Folder n b [] ++ xs ++ z) (sym (splitNode^Foldr n (node^Folder n d []) c)) ⟩
        node^Folder n a [] ++ node^Folder n b [] ++ node^Folder n c (node^Folder n d []) ++ z
    =⟨ cong (λ xs → node^Folder n a [] ++ xs) (associativeConcatList (node^Folder n b []) (node^Folder n c (node^Folder n d [])) z) ⟩
        node^Folder n a [] ++ (node^Folder n b [] ++ node^Folder n c (node^Folder n d [])) ++ z
    =⟨ cong (λ xs → node^Folder n a [] ++ xs ++ z)  (sym (splitNode^Foldr n (node^Folder n c (node^Folder n d [])) b)) ⟩
        node^Folder n a [] ++ node^Folder n b (node^Folder n c (node^Folder n d [])) ++ z
    =⟨ associativeConcatList (node^Folder n a []) (node^Folder n b (node^Folder n c (node^Folder n d []))) z ⟩
        (node^Folder n a [] ++ node^Folder n b (node^Folder n c (node^Folder n d []))) ++ z
    =⟨ cong (_++ z) (sym (splitNode^Foldr n (node^Folder n b (node^Folder n c (node^Folder n d []))) a)) ⟩ 
        node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d []))) ++ z
    ∎

splitConsTree : {a : Set} -> (n : Nat) -> (z : List a) -> (x : Node^ n (Elem a)) -> (m : FingerTree (Node^ n (Elem a))) 
                        -> foldr (node^Folder n) z (consTree ⦃ sizedNode^ n ⦄ x m) ≡ (node^Folder n x []) ++ (foldr (node^Folder n) z m)
splitConsTree n z x EmptyT = 
    begin
        foldr (node^Folder n) z (Single x)
    =⟨⟩
        node^Folder n x z
    =⟨ splitNode^Foldr n z x ⟩
        node^Folder n x [] ++ z
    =⟨⟩
        node^Folder n x [] ++ (foldr (node^Folder n) z EmptyT)
    ∎
splitConsTree n z x (Single x₁) =
    begin
        foldr (node^Folder n) z (Deep (size ⦃ sizedNode^ n ⦄  x + size ⦃ sizedNode^ n ⦄ x₁) (One x) EmptyT (One x₁))
    =⟨⟩
        foldr (node^Folder n) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z (One x₁)) EmptyT) (One x)
    =⟨ splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z (One x₁)) EmptyT) (One x) ⟩
        foldr (node^Folder n ) [] (One x) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z (One x₁)) EmptyT)
    =⟨⟩ 
        foldr (node^Folder n ) [] (One x) ++ (foldr (node^Folder n) z (One x₁))
    =⟨⟩
        node^Folder n x [] ++ (foldr (node^Folder n) z (Single x₁))
    ∎
splitConsTree n z x (Deep v (One a) m sf) = 
    begin
         foldr (node^Folder n) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Two x a)
    =⟨ splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Two x a) ⟩
         node^Folder n x (node^Folder n a []) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (_++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (splitNode^Foldr n (node^Folder n a []) x) ⟩
        (node^Folder n x [] ++ node^Folder n a []) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ sym (associativeConcatList (node^Folder n x []) (node^Folder n a []) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) ⟩
        node^Folder n x [] ++ node^Folder n a [] ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (node^Folder n x [] ++_) (sym (splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (One a))) ⟩
        (node^Folder n x []) ++ (foldr (node^Folder n) z (Deep v (One a) m sf))
    ∎
splitConsTree n z x (Deep v (Two a b) m sf) = 
    begin
        foldr (node^Folder n) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Three x a b)
    =⟨ splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Three x a b) ⟩
        node^Folder n x (node^Folder n a (node^Folder n b [])) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (_++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (splitNode^Foldr n (node^Folder n a (node^Folder n b [])) x) ⟩
        (node^Folder n x [] ++ node^Folder n a (node^Folder n b [])) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ sym (associativeConcatList (node^Folder n x []) (node^Folder n a (node^Folder n b [])) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) ⟩
        node^Folder n x [] ++ node^Folder n a (node^Folder n b []) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (node^Folder n x [] ++_) (sym (splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Two a b))) ⟩
        (node^Folder n x []) ++ (foldr (node^Folder n) z (Deep v (Two a b) m sf))
    ∎
splitConsTree n z x (Deep v (Three a b c) m sf) = 
    begin
        foldr (node^Folder n) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Four x a b c) 
    =⟨ splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Four x a b c) ⟩
        node^Folder n x (node^Folder n a (node^Folder n b (node^Folder n c []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (_++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (splitNode^Foldr n (node^Folder n a (node^Folder n b (node^Folder n c []))) x) ⟩
        (node^Folder n x [] ++ (node^Folder n a (node^Folder n b (node^Folder n c [])))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ sym (associativeConcatList (node^Folder n x []) (node^Folder n a (node^Folder n b (node^Folder n c []))) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) ⟩
        node^Folder n x [] ++ (node^Folder n a (node^Folder n b (node^Folder n c []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (node^Folder n x [] ++_) (sym (splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Three a b c))) ⟩
        (node^Folder n x []) ++ (foldr (node^Folder n) z (Deep v (Three a b c) m sf))
    ∎
splitConsTree n z x (Deep v (Four a b c d) m sf) = 
    begin
        foldr (node^Folder n) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) (consTree ⦃ sizedNode^ (suc n) ⦄ (node3 ⦃ sizedNode^ n ⦄ b c d) m)) (Two x a) 
    =⟨ splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) (consTree ⦃ sizedNode^ (suc n) ⦄ (node3 ⦃ sizedNode^ n ⦄ b c d) m)) (Two x a) ⟩
        node^Folder n x (node^Folder n a []) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) (consTree ⦃ sizedNode^ (suc n) ⦄ (node3 ⦃ sizedNode^ n ⦄ b c d) m))
    =⟨ cong (node^Folder n x (node^Folder n a []) ++_) (splitConsTree (suc n) (foldr (node^Folder n) z sf) (node3 ⦃ sizedNode^ n ⦄ b c d) m) ⟩
        node^Folder n x (node^Folder n a []) ++ node^Folder (suc n) (node3 ⦃ sizedNode^ n }} b c d) [] ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨⟩
        node^Folder n x (node^Folder n a []) ++ node^Folder n b (node^Folder n c (node^Folder n d [])) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ associativeConcatList (node^Folder n x (node^Folder n a [])) (node^Folder n b (node^Folder n c (node^Folder n d []))) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) ⟩
        (node^Folder n x (node^Folder n a []) ++ node^Folder n b (node^Folder n c (node^Folder n d []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (λ xs → (xs ++ (node^Folder n b (node^Folder n c (node^Folder n d [])))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (splitNode^Foldr n (node^Folder n a []) x) ⟩
        ((node^Folder n x [] ++ node^Folder n a []) ++ node^Folder n b (node^Folder n c (node^Folder n d []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (_++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (sym (associativeConcatList (node^Folder n x []) (node^Folder n a []) (node^Folder n b (node^Folder n c (node^Folder n d []))))) ⟩
        (node^Folder n x [] ++ node^Folder n a [] ++ node^Folder n b (node^Folder n c (node^Folder n d []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (λ xs → (node^Folder n x [] ++ xs) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) (sym (splitNode^Foldr n (node^Folder n b (node^Folder n c (node^Folder n d []))) a)) ⟩
        (node^Folder n x [] ++ node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d [])))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ sym (associativeConcatList (node^Folder n x []) (node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d [])))) (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)) ⟩
        node^Folder n x [] ++ node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d []))) ++ (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ cong (node^Folder n x [] ++_) (sym (splitDigitNode^Foldr n (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m) (Four a b c d))) ⟩ 
        (node^Folder n x []) ++ (foldr (node^Folder n) z (Deep v (Four a b c d) m sf))
    ∎


seqPrepend : {a : Set} -> (x : a) -> (xs : Seq a) -> toList (x <| xs) ≡ x ∷ (toList xs)
seqPrepend x Empty = refl
seqPrepend x (Sequence (Single x₁)) = refl
seqPrepend x (Sequence (Deep v (One x₁) m sf)) = refl
seqPrepend x (Sequence (Deep v (Two x₁ x₂) m sf)) = refl
seqPrepend x (Sequence (Deep v (Three x₁ x₂ x₃) m sf)) = refl
seqPrepend x (Sequence (Deep v (Four a@(Element y) b@(Element x₁) c@(Element x₂) d@(Element x₃)) m sf)) = 
    begin
        toList (Sequence (Deep (1 + v) (Two (Element x) a) (consTree (node3 b c d) m) sf))
    =⟨⟩
        (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) (consTree (node3 b c d) m)) (Two (Element x) (Element y)))
    =⟨⟩
        x ∷ (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) (consTree (node3 b c d) m)) (One (Element y)))
    =⟨ cong (x ∷_) (splitDigitFoldr (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) (consTree (node3 b c d) m)) (One (Element y))) ⟩
        x ∷ ((foldr (flip (foldr _∷_)) [] (One (Element y))) ++ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) (consTree (node3 b c d) m)))
    =⟨⟩
        x ∷ y ∷ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) (consTree (node3 b c d) m))
    =⟨ cong (λ xs → x ∷ y ∷ xs) (splitConsTree 1 (foldr (flip (foldr _∷_)) [] sf) (node3 b c d) m) ⟩
        x ∷ y ∷ ((foldr (flip (foldr _∷_)) [] (node3 b c d)) ++ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) m))
    =⟨⟩
        x ∷ y ∷ x₁ ∷ x₂ ∷ x₃ ∷ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) m)
    =⟨⟩
        x ∷ (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf) m) (Four a b c d))
    =⟨⟩
        x ∷ toList (Sequence (Deep v (Four a b c d) m sf))
    ∎


--

------------------------------
-- Simple roundtrip properties
------------------------------

fromListRoundtrip : {a : Set} -> (xs : List a) -> xs ≡ toList (fromList xs)
fromListRoundtrip [] = refl
fromListRoundtrip (x ∷ xs) = 
    begin
        x ∷ xs
    =⟨ cong (x ∷_) (fromListRoundtrip xs) ⟩
        x ∷ toList (foldr _<|_ (Sequence EmptyT) xs)
    =⟨ sym (seqPrepend x (foldr _<|_ (Sequence EmptyT) xs)) ⟩
        toList (x <| (foldr _<|_ (Sequence EmptyT) xs))
    =⟨⟩ 
        toList (foldr _<|_ (Sequence EmptyT) (x ∷ xs))
    =⟨⟩ 
        toList (fromList (x ∷ xs))
    ∎

toListRoundtrip : {a : Set} -> (xs : Seq a) -> toList xs ≡ toList (fromList (toList xs))
toListRoundtrip xs = 
    begin
        toList xs
    =⟨ fromListRoundtrip (toList xs) ⟩
        toList (fromList (toList xs))
    ∎