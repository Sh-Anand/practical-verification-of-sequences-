module ProofsSized where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Preconditions

open import ProofsTypeClass

open import Project

open import ProofAssistant



sizeElemIsOne : {a : Set} -> ⦃ _ : (Sized (Elem a)) ⦄ -> (e : Elem a) -> size e ≡ 1
sizeElemIsOne (Element x) = refl

sizeUnchangedElemFmap : {a b : Set} -> ⦃ _ : Sized a ⦄ -> ⦃ _ : Sized b ⦄ -> (f : a -> b) -> (e : Elem a) -> size e ≡ size (fmap f e)
sizeUnchangedElemFmap f (Element x) = refl


sizeUnchangedFingerTreeFmap : {a b : Set} -> ⦃ _ : Sized a ⦄ -> ⦃ _ : Sized b ⦄ -> (f : (Elem a) -> (Elem b)) -> (fT : FingerTree (Elem a)) -> size fT ≡ size (fmap f fT)
sizeUnchangedFingerTreeFmap f EmptyT = refl
sizeUnchangedFingerTreeFmap f (Single (Element x)) = refl
sizeUnchangedFingerTreeFmap f (Deep v pr m sf) = refl

sizeDigitFoldSplit : {a : Set} -> (xs : List a) -> (d : Digit (Elem a)) -> size d + lengthList xs ≡ lengthList (foldr (flip (foldr _∷_)) xs d)
sizeDigitFoldSplit xs (One (Element x)) = refl
sizeDigitFoldSplit xs (Two (Element x) (Element x₁)) = 
    begin
        2 + lengthList xs
    =⟨ associativeInt 1 1 (lengthList xs) ⟩
        1 + (1 + lengthList xs)
    =⟨⟩
        lengthList (x ∷ x₁ ∷ xs)
    =⟨⟩
        lengthList (foldr (flip (foldr _∷_)) xs (Two (Element x) (Element x₁)))
    ∎
sizeDigitFoldSplit xs (Three (Element x) (Element x₁) (Element x₂)) = 
    begin
        (((1 + 1) + 1) + lengthList xs)
    =⟨ associativeInt (1 + 1) 1 (lengthList xs) ⟩
        (1 + 1) + (1 + lengthList xs)
    =⟨ associativeInt 1 1 (1 + lengthList xs) ⟩
        lengthList (foldr (flip (foldr _∷_)) xs (Three (Element x) (Element x₁) (Element x₂)))
    ∎
sizeDigitFoldSplit xs (Four (Element x) (Element x₁) (Element x₂) (Element x₃)) = 
    begin
        1 + 1 + 1 + 1 + lengthList xs
    =⟨ associativeInt (1 + 1 + 1) 1 (lengthList xs) ⟩
        1 + 1 + 1 + (1 + lengthList xs)
    =⟨ associativeInt (1 + 1) 1 (1 + lengthList xs) ⟩
        1 + 1 + (1 + (1 + lengthList xs))
    =⟨ associativeInt 1 1 (1 + (1 + lengthList xs)) ⟩
        lengthList (foldr (flip (foldr _∷_)) xs (Four (Element x) (Element x₁) (Element x₂) (Element x₃)))
    ∎

sizeNodeFoldSplit : {a : Set} -> (z : List a) -> (n : Node (Elem a)) -> (lengthList ∘ (foldr (flip (foldr _∷_)) z)) n ≡ size n + lengthList z
sizeNodeFoldSplit z (Node2 x (Element x₁) (Element x₂)) = 
    begin
        lengthList (x₁ ∷ x₂ ∷ z)
    =⟨⟩
        1 + (1 + lengthList z)
    =⟨ sym (associativeInt 1 1 (lengthList z)) ⟩
        size (Element x₁) + size (Element x₂) + lengthList z
    =⟨⟩ 
        size (Node2 x (Element x₁) (Element x₂)) + lengthList z
    ∎
sizeNodeFoldSplit z (Node3 x (Element x₁) (Element x₂) (Element x₃)) = 
    begin
        lengthList (x₁ ∷ x₂ ∷ x₃ ∷ z)
    =⟨⟩
        1 + (1 + (1 + lengthList z))
    =⟨ sym (associativeInt 1 1 (1 + lengthList z)) ⟩
        2 + (1 + lengthList z)
    =⟨ sym (associativeInt 2 1 (lengthList z)) ⟩
        3 + lengthList z
    ∎



sizeNode^FoldSplit : {a : Set} -> (n : Nat) -> (z : List a) -> (nd : (Node^ n (Elem a)))
                   -> size ⦃ sizedNode^ n ⦄  nd + lengthList z ≡ lengthList ((node^Folder n) nd z)
sizeNode^FoldSplit zero z (Element x) = 
    begin
        (size ⦃ sizedNode^ zero ⦄ (Element x)) + lengthList z
    =⟨⟩
        1 + lengthList z
    =⟨⟩
        lengthList ((flip (foldr _∷_)) (Element x) z)
    ∎
sizeNode^FoldSplit (suc n) z (Node2 v x₁ x₂) = 
    begin
        size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ + lengthList z
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ x₁) (size ⦃ sizedNode^ n ⦄ x₂) (lengthList z) ⟩ 
        size ⦃ sizedNode^ n ⦄ x₁ + (size ⦃ sizedNode^ n ⦄ x₂ + lengthList z)
    =⟨ cong ((size ⦃ sizedNode^ n ⦄ x₁) +_) (sizeNode^FoldSplit n z x₂) ⟩
        size ⦃ sizedNode^ n ⦄ x₁ + lengthList (node^Folder n x₂ z)
    =⟨ sizeNode^FoldSplit n (node^Folder n x₂ z) x₁ ⟩
        lengthList (node^Folder n x₁ (node^Folder n x₂ z))
    =⟨⟩
        lengthList (foldr (node^Folder n) z (Node2 v x₁ x₂))
    =⟨⟩
        lengthList ((node^Folder (suc n) (Node2 v x₁ x₂) z))
    ∎
sizeNode^FoldSplit (suc n) z (Node3 v x₁ x₂ x₃) = 
    begin
        size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ + size ⦃ sizedNode^ n ⦄ x₃ + lengthList z
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂) (size ⦃ sizedNode^ n ⦄ x₃) (lengthList z) ⟩ 
        size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ + (size ⦃ sizedNode^ n ⦄ x₃ + lengthList z)
    =⟨ cong (size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ +_) (sizeNode^FoldSplit n z x₃) ⟩
        size ⦃ sizedNode^ n ⦄ x₁ + size ⦃ sizedNode^ n ⦄ x₂ + lengthList (node^Folder n x₃ z)
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ x₁) (size ⦃ sizedNode^ n ⦄ x₂) (lengthList (node^Folder n x₃ z)) ⟩ 
        size ⦃ sizedNode^ n ⦄ x₁ + (size ⦃ sizedNode^ n ⦄ x₂ + lengthList (node^Folder n x₃ z))
    =⟨ cong ((size ⦃ sizedNode^ n ⦄ x₁) +_) (sizeNode^FoldSplit n (node^Folder n x₃ z) x₂) ⟩
        size ⦃ sizedNode^ n ⦄ x₁ + lengthList (node^Folder n x₂ (node^Folder n x₃ z))
    =⟨ sizeNode^FoldSplit n (node^Folder n x₂ (node^Folder n x₃ z)) x₁ ⟩
        lengthList (node^Folder n x₁ (node^Folder n x₂ (node^Folder n x₃ z)))
    =⟨⟩
        lengthList (foldr (node^Folder n) z (Node3 v x₁ x₂ x₃))
    =⟨⟩
        lengthList ((node^Folder (suc n) (Node3 v x₁ x₂ x₃) z))
    ∎

sizeDigitNode^FoldSplit : {a : Set} -> (n : Nat) -> (z : List a) -> (d : Digit (Node^ n (Elem a)))
                   -> size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ d + lengthList z ≡ lengthList (foldr (node^Folder n) z d)
sizeDigitNode^FoldSplit n z (One a) = 
    begin
        size ⦃ sizedNode^ n ⦄ a + lengthList z
    =⟨ sizeNode^FoldSplit n z a ⟩
        lengthList (node^Folder n a z)
    =⟨⟩ 
        lengthList (foldr (node^Folder n) z (One a))
    ∎
sizeDigitNode^FoldSplit n z (Two a b) = 
    begin
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + lengthList z
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a) (size ⦃ sizedNode^ n ⦄ b) (lengthList z) ⟩
        size ⦃ sizedNode^ n ⦄ a + (size ⦃ sizedNode^ n ⦄ b + lengthList z)
    =⟨ cong (size ⦃ sizedNode^ n ⦄ a +_) (sizeNode^FoldSplit n z b) ⟩
        size ⦃ sizedNode^ n ⦄ a + lengthList (node^Folder n b z)
    =⟨ sizeNode^FoldSplit n (node^Folder n b z) a ⟩
        lengthList (node^Folder n a (node^Folder n b z))
    =⟨⟩
        lengthList (foldr (node^Folder n) z (Two a b))
    ∎
sizeDigitNode^FoldSplit n z (Three a b c) = 
    begin
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c + lengthList z
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b) (size ⦃ sizedNode^ n ⦄ c) (lengthList z) ⟩
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + (size ⦃ sizedNode^ n ⦄ c + lengthList z)
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a) (size ⦃ sizedNode^ n ⦄ b) (size ⦃ sizedNode^ n ⦄ c + lengthList z) ⟩
        size ⦃ sizedNode^ n ⦄ a + (size ⦃ sizedNode^ n ⦄ b + (size ⦃ sizedNode^ n ⦄ c + lengthList z))
    =⟨ cong (λ c → size ⦃ sizedNode^ n ⦄ a + (size ⦃ sizedNode^ n ⦄ b + c)) (sizeNode^FoldSplit n z c) ⟩
        size ⦃ sizedNode^ n ⦄ a + (size ⦃ sizedNode^ n ⦄ b + lengthList (node^Folder n c z))
    =⟨ cong (size ⦃ sizedNode^ n ⦄ a +_) (sizeNode^FoldSplit n (node^Folder n c z) b) ⟩
        size ⦃ sizedNode^ n ⦄ a + lengthList (node^Folder n b (node^Folder n c z))
    =⟨ sizeNode^FoldSplit n (node^Folder n b (node^Folder n c z)) a ⟩
        lengthList (node^Folder n a (node^Folder n b (node^Folder n c z)))
    ∎
sizeDigitNode^FoldSplit n z (Four a b c d) = 
    begin
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c + size ⦃ sizedNode^ n ⦄ d + lengthList z
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c) (size ⦃ sizedNode^ n ⦄ d) (lengthList z) ⟩
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c + (size ⦃ sizedNode^ n ⦄ d + lengthList z)
    =⟨ cong (size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c +_) (sizeNode^FoldSplit n z d) ⟩
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + size ⦃ sizedNode^ n ⦄ c + lengthList (node^Folder n d z)
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b) (size ⦃ sizedNode^ n ⦄ c) (lengthList (node^Folder n d z)) ⟩
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + (size ⦃ sizedNode^ n ⦄ c + lengthList (node^Folder n d z))
    =⟨ cong (size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b +_) (sizeNode^FoldSplit n (node^Folder n d z) c) ⟩
        size ⦃ sizedNode^ n ⦄ a + size ⦃ sizedNode^ n ⦄ b + lengthList (node^Folder n c (node^Folder n d z))
    =⟨ associativeInt (size ⦃ sizedNode^ n ⦄ a) (size ⦃ sizedNode^ n ⦄ b) (lengthList (node^Folder n c (node^Folder n d z))) ⟩
        size ⦃ sizedNode^ n ⦄ a + (size ⦃ sizedNode^ n ⦄ b + lengthList (node^Folder n c (node^Folder n d z)))
    =⟨ cong (size ⦃ sizedNode^ n ⦄ a +_) (sizeNode^FoldSplit n (node^Folder n c (node^Folder n d z)) b) ⟩
        size ⦃ sizedNode^ n ⦄ a + lengthList (node^Folder n b (node^Folder n c (node^Folder n d z)))
    =⟨ sizeNode^FoldSplit n (node^Folder n b (node^Folder n c (node^Folder n d z))) a ⟩
        lengthList (node^Folder n a (node^Folder n b (node^Folder n c (node^Folder n d z))))
    ∎


sizeFingerTreeFoldSplit : {a : Set} -> (n : Nat) -> (z : List a) -> (xs : FingerTree (Node^ n (Elem a))) -> {IsTrue (isValidFingerTree ⦃ sizedNode^ n ⦄ xs)} 
                        -> size ⦃ FingerTreeSized ⦃ sizedNode^ n ⦄ ⦄ xs + lengthList z ≡ lengthList (foldr (node^Folder n) z xs)
sizeFingerTreeFoldSplit n z EmptyT = 
    begin
        0 + lengthList z
    =⟨ identityInt (lengthList z) ⟩
        lengthList z
    ∎
sizeFingerTreeFoldSplit n z (Single x) = 
    begin
        size ⦃ sizedNode^ n ⦄ x + lengthList z
    =⟨ sizeNode^FoldSplit n z x ⟩
        lengthList ((node^Folder n) x z)
    =⟨⟩  
        lengthList (foldr (node^Folder n) z (Single x))
    ∎ 
sizeFingerTreeFoldSplit n z (Deep v pr m sf) {valid} = 
    begin 
        v + lengthList z
    =⟨ cong (_+ lengthList z) (integerEqualityEquivalence valid) ⟩
        size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m + size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ sf + lengthList z
    =⟨ associativeInt (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m) (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ sf) (lengthList z) ⟩
        size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m + (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ sf + lengthList z)
    =⟨ cong (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m +_) (sizeDigitNode^FoldSplit n z sf) ⟩
        size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m + lengthList (foldr (node^Folder n) z sf)
    =⟨ associativeInt (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr) (size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m) (lengthList (foldr (node^Folder n) z sf)) ⟩
        size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + (size ⦃ FingerTreeSized ⦃ sizedNode^ (suc n) ⦄ ⦄ m + lengthList (foldr (node^Folder n) z sf))
    =⟨ cong (size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr +_) (sizeFingerTreeFoldSplit (suc n) (foldr (node^Folder n) z sf) m { isTrueFingerTreeSub ⦃ sizedNode^ n ⦄ v pr m sf valid } ) ⟩
        size ⦃ DigitSized ⦃ sizedNode^ n ⦄ ⦄ pr + lengthList (foldr (node^Folder (suc n)) (foldr (node^Folder n) z sf) m)
    =⟨ sizeDigitNode^FoldSplit n (foldr (flip (foldr (node^Folder n))) (foldr (node^Folder n) z sf) m) pr ⟩
        lengthList (foldr (node^Folder n) (foldr (flip (foldr (node^Folder n))) (foldr (node^Folder n) z sf) m) pr)
    =⟨⟩
        lengthList (foldr (node^Folder n) z (Deep v pr m sf))
    ∎



sizeUnchangedToList : {a : Set} -> (xs : Seq a) -> {IsTrue (isValidSeq xs)} -> size xs ≡ lengthList (toList xs)
sizeUnchangedToList (Sequence xs) {valid} =
    begin
        size (Sequence xs)
    =⟨⟩
        size xs
    =⟨ sym (identityInt (size xs)) ⟩
        0 + size xs
    =⟨ commutativeInt 0 (size xs) ⟩
        size xs + 0
    =⟨ sizeFingerTreeFoldSplit 0 [] xs {valid} ⟩
        lengthList (foldr (flip (foldr _∷_)) [] xs)
    =⟨⟩
        lengthList (toList (Sequence xs))
    ∎

sizeIncrementConsTree : {a : Set} -> ⦃ aSized : Sized a ⦄ -> (x : a) -> (fT : FingerTree a) -> size (consTree x fT) ≡ size fT + size x 
sizeIncrementConsTree x EmptyT = 
    begin
        size (Single x)
    =⟨⟩
        size x
    =⟨ sym (identityInt (size x)) ⟩
        0 + size x
    ∎
sizeIncrementConsTree x (Single y) = 
    begin
        size (Deep (size x + 0 + size y) (One x) EmptyT (One y))
    =⟨⟩
        size x + 0 + size y
    =⟨ associativeInt (size x) 0 (size y) ⟩
        size x + (0 + size y) 
    =⟨ cong ((size x) +_) (identityInt (size y)) ⟩
        size x + size y
    =⟨ commutativeInt (size x) (size y) ⟩
        size y + size x
    =⟨⟩
        size (Single y) + size x
    ∎

sizeIncrementConsTree x (Deep v (One a) m sf) = 
    begin
        size (Deep (size x + v) (One a) m sf)
    =⟨⟩
        size x + v
    =⟨ commutativeInt (size x) v ⟩
        v + size x
    =⟨⟩
        size (Deep v (One a) m sf) + size x
    ∎
sizeIncrementConsTree x (Deep v (Two a b) m sf) = 
    begin
        size x + v
    =⟨ commutativeInt (size x) v ⟩
        v + size x
    ∎
sizeIncrementConsTree x (Deep v (Three a b c) m sf) = 
    begin         
        size x + v     
    =⟨ commutativeInt (size x) v ⟩         
        v + size x     
    ∎
sizeIncrementConsTree x (Deep v (Four a b c d) m sf) = 
    begin         
        size x + v     
    =⟨ commutativeInt (size x) v ⟩         
        v + size x     
    ∎

sizeIncrementPrepend : {a : Set} -> (x : a) -> (xs : Seq a) -> size (x <| xs) ≡ 1 + size xs
sizeIncrementPrepend x (Sequence xs) = 
    begin
        size (Sequence (consTree (Element x) xs))
    =⟨⟩
        size (consTree (Element x) xs)
    =⟨ sizeIncrementConsTree (Element x) xs ⟩
        size xs + size (Element x)
    =⟨⟩
        size xs + 1
    =⟨ commutativeInt (size xs) 1 ⟩
        1 + size xs
    =⟨⟩ 
        1 + size (Sequence xs)
    ∎

sizeIncrementPrependEquivalentToList : {a : Set} -> (x : a) -> (xs : Seq a) -> {IsTrue (isValidSeq xs)} -> size (x <| xs) ≡ lengthList (x ∷ toList xs)
sizeIncrementPrependEquivalentToList x xs {valid} = 
    begin
        size (x <| xs)
    =⟨ sizeIncrementPrepend x xs ⟩
        1 + size xs
    =⟨ cong (1 +_) (sizeUnchangedToList xs {valid}) ⟩
        1 + lengthList (toList xs)
    =⟨⟩
        lengthList (x ∷ toList xs) 
    ∎

sizeIncrementSnocTree : {a : Set} -> ⦃ _ : Sized a ⦄ -> (xs : FingerTree a) -> (x : a) ->  size (snocTree xs x) ≡ size xs + size x
sizeIncrementSnocTree EmptyT x = 
    begin
        size (Single x)
    =⟨⟩
        size x
    =⟨ sym (identityInt (size x)) ⟩
        0 + size x
    ∎
sizeIncrementSnocTree (Single x) y = 
    begin
        size (Deep (size x + 0 + size y) (One x) EmptyT (One y))
    =⟨⟩
        size x + 0 + size y
    =⟨ associativeInt (size x) 0 (size y) ⟩
        size x + (0 + size y) 
    =⟨ cong ((size x) +_) (identityInt (size y)) ⟩
        size x + size y
    =⟨⟩
        size (Single x) + size y
    ∎
sizeIncrementSnocTree (Deep v pr m (One x₁)) x = refl
sizeIncrementSnocTree (Deep v pr m (Two x₁ x₂)) x = refl
sizeIncrementSnocTree (Deep v pr m (Three x₁ x₂ x₃)) x = refl
sizeIncrementSnocTree (Deep v pr m (Four x₁ x₂ x₃ x₄)) x = refl

sizeIncrementAppend : {a : Set} -> (xs : Seq a) -> (x : a) -> size (xs |> x) ≡ size xs + 1
sizeIncrementAppend (Sequence xs) x = 
    begin
        size ((Sequence xs) |> x)
    =⟨⟩ 
        size (Sequence (snocTree xs (Element x)))
    =⟨⟩
        size (snocTree xs (Element x))
    =⟨ sizeIncrementSnocTree xs (Element x) ⟩
        size (Sequence xs) + size (Element x) 
    =⟨⟩ 
        size (Sequence xs) + 1
    ∎

sizeIncrementAppendEquivalentToList : {a : Set} -> (xs : Seq a) -> (x : a) -> {IsTrue (isValidSeq xs)} -> size (xs |> x) ≡ lengthList (toList xs ++ (x ∷ []))
sizeIncrementAppendEquivalentToList xs x {valid} = 
    begin
        size (xs |> x)
    =⟨ sizeIncrementAppend xs x ⟩
        size xs + 1
    =⟨ cong (_+ 1) (sizeUnchangedToList xs {valid}) ⟩
       lengthList (toList xs) + 1 
    =⟨ sym (lengthListConcat (toList xs) (x ∷ [])) ⟩
        lengthList (toList xs ++ (x ∷ []))
    ∎ 


sizeDigitFoldSeqSplit : {a : Set} -> (xs : Seq a) -> (d : Digit (Elem a)) -> size d + size xs ≡ size (foldr (flip (foldr _<|_)) xs d)
sizeDigitFoldSeqSplit xs (One (Element x)) = 
    begin
        1 + size xs
    =⟨ sym (sizeIncrementPrepend x xs) ⟩
        size (x <| xs)
    ∎
sizeDigitFoldSeqSplit xs (Two (Element x) (Element x₁)) = 
    begin
        1 + 1 + size xs
    =⟨ associativeInt 1 1 (size xs) ⟩
        1 + (1 + size xs)
    =⟨ cong (1 +_) (sym (sizeIncrementPrepend x₁ xs)) ⟩
        1 + size (x₁ <| xs)
    =⟨ sym (sizeIncrementPrepend x (x₁ <| xs)) ⟩
        size (x <| (x₁ <| xs))
    ∎
sizeDigitFoldSeqSplit xs (Three (Element x) (Element x₁) (Element x₂)) = 
    begin
        1 + 1 + 1 + size xs
    =⟨ associativeInt (1 + 1) 1 (size xs) ⟩
        1 + 1 + (1 + size xs) 
    =⟨ cong (1 + 1 +_) (sym (sizeIncrementPrepend x₂ xs)) ⟩
        1 + 1 + size (x₂ <| xs)
    =⟨ associativeInt 1 1 (size (x₂ <| xs)) ⟩
        1 + (1 + size (x₂ <| xs))
    =⟨ cong (1 +_) (sym (sizeIncrementPrepend x₁ (x₂ <| xs))) ⟩
        1 + size (x₁ <| (x₂ <| xs))
    =⟨ sym (sizeIncrementPrepend x (x₁ <| (x₂ <| xs))) ⟩
        size (x <| (x₁ <| (x₂ <| xs)))
    ∎
sizeDigitFoldSeqSplit xs (Four (Element x) (Element x₁) (Element x₂) (Element x₃)) = 
    begin
        1 + 1 + 1 + 1 + size xs
    =⟨ associativeInt (1 + 1 + 1) 1 (size xs) ⟩
        1 + 1 + 1 + (1 + size xs)
    =⟨ cong (1 + 1 + 1 +_) (sym (sizeIncrementPrepend x₃ xs)) ⟩
        1 + 1 + 1 + size (x₃ <| xs)
    =⟨ associativeInt (1 + 1) 1 (size (x₃ <| xs)) ⟩
        1 + 1 + (1 + size (x₃ <| xs))
    =⟨ cong (1 + 1 +_) (sym (sizeIncrementPrepend x₂ (x₃ <| xs))) ⟩
        1 + 1 + size (x₂ <| (x₃ <| xs))
    =⟨ associativeInt 1 1 (size (x₂ <| (x₃ <| xs))) ⟩
        1 + (1 + size (x₂ <| (x₃ <| xs)))
    =⟨ cong (1 +_) (sym (sizeIncrementPrepend x₁ (x₂ <| (x₃ <| xs)))) ⟩
        1 + size (x₁ <| (x₂ <| (x₃ <| xs)))
    =⟨ sym (sizeIncrementPrepend x (x₁ <| (x₂ <| (x₃ <| xs)))) ⟩
        size (x <| (x₁ <| (x₂ <| (x₃ <| xs))))
    ∎

sizeUnchangedFromList : {a : Set} -> (xs : List a) -> lengthList xs ≡ size (fromList xs)
sizeUnchangedFromList [] = refl
sizeUnchangedFromList (x ∷ xs) = 
    begin
        lengthList (x ∷ xs)
    =⟨⟩
        1 + lengthList xs
    =⟨ cong (1 +_) (sizeUnchangedFromList xs) ⟩
        1 + size (foldr _<|_ empty xs)
    =⟨ sym (sizeIncrementPrepend x (foldr _<|_ empty xs)) ⟩
        size (x <| (foldr _<|_ empty xs))
    =⟨⟩ 
        size (foldr _<|_ empty (x ∷ xs))
    ∎

sizeUnchangedToFromList : {a : Set} -> (xs : Seq a) -> {IsTrue (isValidSeq xs)} -> size xs ≡ size (fromList (toList xs))
sizeUnchangedToFromList Empty = refl
sizeUnchangedToFromList (Sequence (Single (Element x))) = refl
sizeUnchangedToFromList (Sequence (Deep v pr m sf)) {valid} = 
    begin
        size (Sequence (Deep v pr m sf))
    =⟨ sizeUnchangedToList (Sequence (Deep v pr m sf)) {valid} ⟩
        lengthList (toList (Sequence (Deep v pr m sf)))
    =⟨ sizeUnchangedFromList (toList (Sequence (Deep v pr m sf))) ⟩
        size (fromList (toList (Sequence (Deep v pr m sf))))
    ∎