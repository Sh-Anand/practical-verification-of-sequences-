module ProofsTemp where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Project

open import Preconditions

open import ProofAssistant

open import ProofsMore

appendTree1FoldrSplit : {a : Set} -> (nn : Nat) 
                -> (m1 m2 : FingerTree (Node^ nn (Elem a))) -> (n : (Node^ nn (Elem a)))
                    -> foldr (node^Folder nn) [] (appendTree1 ⦃ sizedNode^ nn ⦄ m1 n m2)
                        ≡ foldr (node^Folder nn) [] m1 ++ (node^Folder nn n []) ++ foldr (node^Folder nn) [] m2

appendTree2FoldrSplit : {a : Set} -> (nn : Nat) 
                -> (m1 m2 : FingerTree (Node^ nn (Elem a))) -> (n1 n2 : (Node^ nn (Elem a)))
                    -> foldr (node^Folder nn) [] (appendTree2 ⦃ sizedNode^ nn ⦄ m1 n1 n2 m2)
                        ≡ foldr (node^Folder nn) (node^Folder nn n1 []) m1 ++ node^Folder nn n2 (foldr (node^Folder nn) [] m2)
appendTree2FoldrSplit nn m1 m2 n1 n2 = {!   !}



appendDigits1FoldrSplit : {a : Set} -> (nn : Nat) -> (m1 m2 : FingerTree (Node (Node^ nn (Elem a)))) -> (n : Node^ nn (Elem a)) -> (sf1 pr2 : Digit (Node^ nn (Elem a))) 
                        -> foldr (node^Folder (suc nn)) [] (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2)
                            ≡ foldr (node^Folder (suc nn)) (foldr (node^Folder nn) [] sf1) m1 ++ node^Folder nn n [] ++ foldr (node^Folder nn) (foldr (node^Folder (suc nn)) [] m2) pr2
appendDigits1FoldrSplit nn m1 m2 n (One a) (One b) = 
    begin
        fnn [] (addDigits1 ⦃ sizedNode^ nn ⦄ m1 (One a) n (One b) m2)
    =⟨⟩
        fnn [] (appendTree1 ⦃ sizedNode^ (suc nn) ⦄ m1 (node3 ⦃ sizedNode^ nn ⦄ a n b) m2)
    =⟨ appendTree1FoldrSplit (suc nn) m1 m2 (node3 ⦃ sizedNode^ nn ⦄ a n b) ⟩
        fnn [] m1 ++ node^Folder nn a (node^Folder nn n (node^Folder nn b [])) ++ fnn [] m2
    =⟨ cong (λ xs → fnn [] m1 ++ xs ++ fnn [] m2) (splitNode^Foldr nn (node^Folder nn n (node^Folder nn b [])) a) ⟩
        fnn [] m1 ++ (((fn [] (One a)) ++ node^Folder nn n (node^Folder nn b [])) ++ fnn [] m2)
    =⟨ associativeConcatList (fnn [] m1) ((fn [] (One a)) ++ node^Folder nn n (node^Folder nn b [])) (fnn [] m2) ⟩
        (fnn [] m1 ++ ((fn [] (One a)) ++ node^Folder nn n (node^Folder nn b []))) ++ fnn [] m2
    =⟨ cong (_++ fnn [] m2) (associativeConcatList (fnn [] m1) (fn [] (One a)) (node^Folder nn n (node^Folder nn b []))) ⟩
        ((fnn [] m1 ++ (fn [] (One a))) ++ node^Folder nn n (node^Folder nn b [])) ++ fnn [] m2
    =⟨ cong (λ xs → (xs ++ node^Folder nn n (node^Folder nn b [])) ++ fnn [] m2) (sym (splitFoldrFingerTree (suc nn) (fn [] (One a)) m1)) ⟩
        ((fnn (fn [] (One a)) m1) ++ node^Folder nn n (node^Folder nn b [])) ++ fnn [] m2
    =⟨ sym (associativeConcatList (fnn (fn [] (One a)) m1) (node^Folder nn n (node^Folder nn b [])) (fnn [] m2)) ⟩
        fnn (fn [] (One a)) m1 ++ node^Folder nn n (node^Folder nn b []) ++ fnn [] m2
    =⟨ cong (λ xs → fnn (fn [] (One a)) m1 ++ xs ++ fnn [] m2) (splitNode^Foldr nn (node^Folder nn b []) n) ⟩
        fnn (fn [] (One a)) m1 ++ (node^Folder nn n [] ++ fn [] (One b)) ++ fnn [] m2
    =⟨ cong (fnn (fn [] (One a)) m1 ++_) (sym (associativeConcatList (node^Folder nn n []) (fn [] (One b)) (fnn [] m2))) ⟩
        fnn (fn [] (One a)) m1 ++ node^Folder nn n [] ++ fn [] (One b) ++ fnn [] m2
    =⟨ cong (λ xs → fnn (fn [] (One a)) m1 ++ node^Folder nn n [] ++ xs) (sym (splitDigitNode^Foldr nn (fnn [] m2) (One b))) ⟩
        fnn (fn [] (One a)) m1 ++ node^Folder nn n [] ++ fn (fnn [] m2) (One b)
    ∎
        where fnn = foldr (node^Folder (suc nn))
              fn = foldr (node^Folder nn)
appendDigits1FoldrSplit nn m1 m2 n (One a) (Two b c) = 
    begin
        fnn [] (addDigits1 ⦃ sizedNode^ nn ⦄ m1 (One a) n (Two b c) m2)
    =⟨⟩
        fnn [] (appendTree2 ⦃ sizedNode^ (suc nn) ⦄ m1 (node2 ⦃ sizedNode^ nn ⦄ a n) (node2 ⦃ sizedNode^ nn ⦄ b c) m2)
    =⟨ {!   !} ⟩
        fnn (node^Folder (suc nn) (node2 ⦃ sizedNode^ nn ⦄ a n) []) m1 ++ node^Folder (suc nn) (node2 ⦃ sizedNode^ nn ⦄ b c) (fnn [] m2)
    =⟨⟩
        fnn (node^Folder (suc nn) (node2 ⦃ sizedNode^ nn ⦄ a n) []) m1 ++ fn (fnn [] m2) (Two b c)
    =⟨ {!   !} ⟩
        fnn (fn [] (One a)) m1 ++ node^Folder nn n [] ++ fn (fnn [] m2) (Two b c)
    ∎
        where fnn = foldr (node^Folder (suc nn))
              fn = foldr (node^Folder nn)
appendDigits1FoldrSplit nn m1 m2 n (One a) (Three b c d) = {!   !}
appendDigits1FoldrSplit nn m1 m2 n (One a) (Four b c d e) = {!   !}
appendDigits1FoldrSplit nn m1 m2 n (Two a b) pr2 = {!   !}
appendDigits1FoldrSplit nn m1 m2 n (Three a b c) pr2 = {!   !}
appendDigits1FoldrSplit nn m1 m2 n (Four a b c d) pr2 = {!   !}




appendTree1FoldrSplit nn EmptyT m2 n = 
    begin
        foldr (node^Folder nn) [] (consTree ⦃ sizedNode^ nn ⦄ n m2)
    =⟨ splitConsTree nn [] n m2 ⟩
        (node^Folder nn n []) ++ foldr (node^Folder nn) [] m2
    ∎
appendTree1FoldrSplit {a} nn (Single x) m2 n = 
    begin
        foldr (node^Folder nn) [] (appendTree1 ⦃ sizedNode^ nn ⦄ (Single x) n m2)
    =⟨ cong (foldr (node^Folder nn) []) (appendTree1Singlexs ⦃ sizedNode^ nn ⦄ x n m2) ⟩
        foldr (node^Folder nn) [] (consTree ⦃ sizedNode^ nn ⦄ x (consTree ⦃ sizedNode^ nn ⦄ n m2))
    =⟨ splitConsTree nn [] x (consTree ⦃ sizedNode^ nn ⦄ n m2) ⟩
        foldr (node^Folder nn) [] (Single x) ++ foldr (node^Folder nn) [] (consTree ⦃ sizedNode^ nn ⦄ n m2)
    =⟨ cong (foldr (node^Folder nn) [] (Single x) ++_) (splitConsTree nn [] n m2) ⟩
        foldr (node^Folder nn) [] (Single x) ++ (node^Folder nn n []) ++ foldr (node^Folder nn) [] m2
    ∎
appendTree1FoldrSplit nn (Deep v pr m sf) EmptyT n = 
    begin
        foldr (node^Folder nn) [] (appendTree1 ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n EmptyT)
    =⟨ cong (foldr (node^Folder nn) []) (appendTree1xsEmpty ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n) ⟩
        foldr (node^Folder nn) [] (snocTree ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n)
    =⟨ splitSnocTree nn [] (Deep v pr m sf) n ⟩
        foldr (node^Folder nn) [] (Deep v pr m sf) ++ (node^Folder nn n [])
    =⟨ cong (foldr (node^Folder nn) [] (Deep v pr m sf) ++_) (identityConcatList (node^Folder nn n [])) ⟩
        foldr (node^Folder nn) [] (Deep v pr m sf) ++ (node^Folder nn n []) ++ []
    ∎
appendTree1FoldrSplit nn (Deep v pr m sf) (Single x) n = 
    begin
        foldr (node^Folder nn) [] (appendTree1 ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n (Single x))
    =⟨ cong (foldr (node^Folder nn) []) (appendTree1xsSingle ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n x) ⟩
        foldr (node^Folder nn) [] (snocTree ⦃ sizedNode^ nn ⦄ (snocTree ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n) x)
    =⟨ splitSnocTree nn [] (snocTree ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n) x ⟩
        foldr (node^Folder nn) [] (snocTree ⦃ sizedNode^ nn ⦄ (Deep v pr m sf) n) ++ foldr (node^Folder nn) [] (Single x)
    =⟨ cong (_++ foldr (node^Folder nn) [] (Single x)) (splitSnocTree nn [] (Deep v pr m sf) n) ⟩
        (foldr (node^Folder nn) [] (Deep v pr m sf) ++ (node^Folder nn n [])) ++ foldr (node^Folder nn) [] (Single x)
    =⟨ sym (associativeConcatList (foldr (node^Folder nn) [] (Deep v pr m sf)) (node^Folder nn n []) (foldr (node^Folder nn) [] (Single x))) ⟩
        foldr (node^Folder nn) [] (Deep v pr m sf) ++ (node^Folder nn n []) ++ foldr (node^Folder nn) [] (Single x)
    ∎
appendTree1FoldrSplit nn (Deep v1 pr1 m1 sf1) (Deep v2 pr2 m2 sf2) n = 
    begin
        foldr (node^Folder nn) [] (appendTree1 ⦃ sizedNode^ nn ⦄ (Deep v1 pr1 m1 sf1) n (Deep v2 pr2 m2 sf2))
    =⟨⟩
        foldr (node^Folder nn) (foldr (node^Folder (suc nn)) (foldr (node^Folder nn) [] sf2) (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2)) pr1
    =⟨ splitDigitNode^Foldr nn (foldr (node^Folder (suc nn)) (foldr (node^Folder nn) [] sf2) (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2)) pr1 ⟩
        foldr (node^Folder nn) [] pr1 ++ foldr (node^Folder (suc nn)) (foldr (node^Folder nn) [] sf2) (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2)
    =⟨ cong (foldr (node^Folder nn) [] pr1 ++_) (splitFoldrFingerTree (suc nn) (foldr (node^Folder nn) [] sf2) (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2))  ⟩
        foldr (node^Folder nn) [] pr1 ++ foldr (node^Folder (suc nn)) [] (addDigits1 ⦃ sizedNode^ nn ⦄ m1 sf1 n pr2 m2) ++ foldr (node^Folder nn) [] sf2
    =⟨ cong (λ xs → h1 ++ xs ++ h4) (appendDigits1FoldrSplit  nn m1 m2 n sf1 pr2) ⟩
        h1 ++ (h2 ++ node^Folder nn n [] ++ h3) ++ h4
    =⟨ cong (h1 ++_) (sym (associativeConcatList h2 (node^Folder nn n [] ++ h3) h4)) ⟩
        h1 ++ (h2 ++ (node^Folder nn n [] ++ h3) ++ h4)
    =⟨ cong (λ xs → (h1 ++ h2 ++ xs)) (sym (associativeConcatList (node^Folder nn n []) h3 h4)) ⟩
        h1 ++ h2 ++ node^Folder nn n [] ++ h3 ++ h4
    =⟨ cong (λ xs → h1 ++ h2 ++ node^Folder nn n [] ++ xs ++ h4) (splitDigitNode^Foldr nn (foldr (node^Folder (suc nn)) [] m2) pr2) ⟩
        h1 ++ h2 ++ node^Folder nn n [] ++ (foldr (node^Folder nn) [] pr2 ++ foldr (node^Folder (suc nn)) [] m2) ++ h4
    =⟨ cong (λ xs → h1 ++ h2 ++ node^Folder nn n [] ++ xs) (sym (associativeConcatList (foldr (node^Folder nn) [] pr2) (foldr (node^Folder (suc nn)) [] m2) h4)) ⟩
        h1 ++ h2 ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] pr2 ++ foldr (node^Folder (suc nn)) [] m2 ++ h4
    =⟨ cong (λ xs → h1 ++ h2 ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] pr2 ++ xs) (sym (splitFoldrFingerTree (suc nn) h4 m2)) ⟩
        h1 ++ h2 ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] pr2 ++ foldr (node^Folder (suc nn)) h4 m2 
    =⟨ cong (λ xs → h1 ++ h2 ++ node^Folder nn n [] ++ xs) (sym (splitDigitNode^Foldr nn (foldr (node^Folder (suc nn)) h4 m2) pr2)) ⟩
        h1 ++ h2 ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] (Deep v2 pr2 m2 sf2)
    =⟨ associativeConcatList h1 h2 (node^Folder nn n [] ++ foldr (node^Folder nn) [] (Deep v2 pr2 m2 sf2)) ⟩
        (h1 ++ h2) ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] (Deep v2 pr2 m2 sf2)
    =⟨ cong (λ xs → (xs ++ node^Folder nn n [] ++ foldr (node^Folder nn) [] (Deep v2 pr2 m2 sf2))) (sym (splitDigitNode^Foldr nn h2 pr1)) ⟩
        foldr (node^Folder nn) [] (Deep v1 pr1 m1 sf1) ++ (node^Folder nn n []) ++ foldr (node^Folder nn) [] (Deep v2 pr2 m2 sf2)
    ∎
        where h1 = foldr (node^Folder nn) [] pr1
              h2 = foldr (node^Folder (suc nn)) (foldr (node^Folder nn) [] sf1) m1
              h3 = foldr (node^Folder nn) (foldr (node^Folder (suc nn)) [] m2) pr2
              h4 = foldr (node^Folder nn) [] sf2




addDigits0FoldrSplit : {a : Set} -> (z : List a) -> (m1 m2 : FingerTree (Node (Elem a))) -> (sf1 pr2 : Digit (Elem a)) 
                    -> (foldr (flip (foldr (flip (foldr _∷_)))) [] (addDigits0 m1 sf1 pr2 m2)) 
                    ≡ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1 ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2
addDigits0FoldrSplit z m1 m2 (One a@(Element x)) (One b@(Element y)) = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 m1 (node2 a b) m2)
    =⟨ appendTree1FoldrSplit 1 m1 m2 (node2 a b) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (x ∷ y ∷ []) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    =⟨ associativeConcatList (foldr (flip (foldr (flip (foldr _∷_)))) [] m1) (x ∷ y ∷ []) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) ⟩
        (foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (x ∷ y ∷ [])) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    =⟨ cong (_++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2) (associativeConcatList (foldr (flip (foldr (flip (foldr _∷_)))) [] m1) (x ∷ []) (y ∷ [])) ⟩
        ((foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (x ∷ [])) ++ (y ∷ [])) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    =⟨ sym (associativeConcatList (foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (x ∷ [])) (y ∷ []) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2)) ⟩
        (foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (x ∷ [])) ++ (y ∷ []) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    =⟨ cong (_++ (y ∷ []) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2) (sym (splitFoldrFingerTree 1 (x ∷ []) m1)) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) (x ∷ []) m1 ++ (y ∷ []) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    =⟨⟩
        foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] (One a)) m1 ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) (One b)
    ∎
addDigits0FoldrSplit z m1 m2 (One a) (Two b c) = {!   !}
addDigits0FoldrSplit z m1 m2 (One a) (Three b c d) = {!   !}
addDigits0FoldrSplit z m1 m2 (One a) (Four b c d e) = {!   !}
addDigits0FoldrSplit z m1 m2 (Two a b) pr2 = {!   !}
addDigits0FoldrSplit z m1 m2 (Three a b c) pr2 = {!   !}
addDigits0FoldrSplit z m1 m2 (Four a b c d) pr2 = {!   !}