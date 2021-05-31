module ProofsTemp where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Project

open import Preconditions

open import ProofAssistant

open import ProofsMore


appendTree1FoldrSplit : {a : Set} -> (m1 m2 : FingerTree (Node (Elem a))) -> (n : Node (Elem a))
                    -> foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 m1 n m2)
                        ≡ foldr (flip (foldr (flip (foldr _∷_)))) [] m1 ++ (foldr (flip (foldr _∷_)) [] n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
appendTree1FoldrSplit EmptyT m2 n = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (consTree n m2)
    =⟨ splitConsTree 1 [] n m2 ⟩
        (foldr (flip (foldr _∷_)) [] n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    ∎
appendTree1FoldrSplit (Single x) m2 n = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 (Single x) n m2)
    =⟨ cong (foldr (flip (foldr (flip (foldr _∷_)))) []) (appendTree1Singlexs x n m2) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (consTree x (consTree n m2))
    =⟨ splitConsTree 1 [] x (consTree n m2) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] (consTree n m2)
    =⟨ cong (foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x) ++_) (splitConsTree 1 [] n m2) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x) ++ (foldr (flip (foldr _∷_)) [] n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2
    ∎
appendTree1FoldrSplit (Deep v pr m sf) EmptyT n = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 (Deep v pr m sf) n EmptyT)
    =⟨ cong (foldr (flip (foldr (flip (foldr _∷_)))) []) (appendTree1xsEmpty (Deep v pr m sf) n) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (snocTree (Deep v pr m sf) n)
    =⟨ splitSnocTree 1 [] (Deep v pr m sf) n ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf) ++ (foldr (flip (foldr _∷_)) [] n)
    =⟨ cong (λ xs → foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf) ++ xs) (identityConcatList (foldr (flip (foldr _∷_)) [] n)) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf) ++ (foldr (flip (foldr _∷_)) [] n) ++ []
    ∎
appendTree1FoldrSplit (Deep v pr m sf) (Single x) n = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 (Deep v pr m sf) n (Single x))
    =⟨ cong (foldr (flip (foldr (flip (foldr _∷_)))) []) (appendTree1xsSingle (Deep v pr m sf) n x) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (snocTree (snocTree (Deep v pr m sf) n) x)
    =⟨ splitSnocTree 1 [] (snocTree (Deep v pr m sf) n) x ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (snocTree (Deep v pr m sf) n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x)
    =⟨ cong (_++ foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x)) (splitSnocTree 1 [] (Deep v pr m sf) n) ⟩
        (foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf) ++ (foldr (flip (foldr _∷_)) [] n)) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x)
    =⟨ sym (associativeConcatList (foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf)) (foldr (flip (foldr _∷_)) [] n) (foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x))) ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v pr m sf) ++ (foldr (flip (foldr _∷_)) [] n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] (Single x)
    ∎ 
appendTree1FoldrSplit (Deep v1 pr1 m1 sf1) (Deep v2 pr2 m2 sf2) n = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep (v1 + size n + v2) pr1 (addDigits1 m1 sf1 n pr2 m2) sf2)
    =⟨⟩
        foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr (flip (foldr (flip (foldr _∷_)))))) (foldr (flip (foldr (flip (foldr _∷_)))) [] sf2) (addDigits1 m1 sf1 n pr2 m2)) pr1
    =⟨ {!   !} ⟩
        foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v1 pr1 m1 sf1) ++ (foldr (flip (foldr _∷_)) [] n) ++ foldr (flip (foldr (flip (foldr _∷_)))) [] (Deep v2 pr2 m2 sf2)
    ∎


addDigits0FoldrSplit : {a : Set} -> (z : List a) -> (m1 m2 : FingerTree (Node (Elem a))) -> (sf1 pr2 : Digit (Elem a)) 
                    -> (foldr (flip (foldr (flip (foldr _∷_)))) [] (addDigits0 m1 sf1 pr2 m2)) 
                    ≡ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1 ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2
addDigits0FoldrSplit z m1 m2 (One a@(Element x)) (One b@(Element y)) = 
    begin
        foldr (flip (foldr (flip (foldr _∷_)))) [] (appendTree1 m1 (node2 a b) m2)
    =⟨ appendTree1FoldrSplit m1 m2 (node2 a b) ⟩
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