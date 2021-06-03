{-# OPTIONS --allow-unsolved-metas #-}

module ProofsConcat where

open import Haskell.Prelude renaming (length to lengthF)

open import DataTypes

open import Project

open import Preconditions

open import ProofAssistant

open import ProofsMore


addDigits0FoldrSplit : {a : Set} -> (z : List a) -> (m1 m2 : FingerTree (Node (Elem a))) -> (sf1 pr2 : Digit (Elem a)) 
                    -> (foldr (flip (foldr (flip (foldr _∷_)))) [] (addDigits0 m1 sf1 pr2 m2)) 
                    ≡ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1 ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2
addDigits0FoldrSplit z m1 m2 sf1 pr2 = {!   !}



appendTree0FoldrSplit : {a : Set} -> (z : List a) -> (xs ys : FingerTree (Elem a)) 
            -> foldr (flip (foldr _∷_)) z (appendTree0 xs ys) ≡ foldr (flip (foldr _∷_)) [] xs ++ foldr (flip (foldr _∷_)) z ys
appendTree0FoldrSplit z EmptyT ys = refl
appendTree0FoldrSplit z (Single x@(Element a)) ys = 
    begin
        foldr (flip (foldr _∷_)) z (appendTree0 (Single x) ys)
    =⟨ cong (foldr (flip (foldr _∷_)) z) (appendTree0Singlexs x ys) ⟩
        foldr (flip (foldr _∷_)) z (consTree x ys)
    =⟨ splitConsTree 0 z x ys ⟩
        a ∷ [] ++ foldr (flip (foldr _∷_)) z ys
    ∎
appendTree0FoldrSplit z xs@(Deep v pr m sf) EmptyT = 
    begin
        foldr (flip (foldr _∷_)) z (appendTree0 xs EmptyT)
    =⟨ cong (foldr (flip (foldr _∷_)) z) (appendTree0xsEmpty xs) ⟩
        foldr (flip (foldr _∷_)) z xs
    =⟨ splitFoldrFingerTree 0 z xs ⟩
        foldr (flip (foldr _∷_)) [] xs ++ z
    ∎
appendTree0FoldrSplit z xs@(Deep v pr m sf) (Single x@(Element a)) = 
    begin
        foldr (flip (foldr _∷_)) z (appendTree0 xs (Single x))
    =⟨ cong (foldr (flip (foldr _∷_)) z ) (appendTree0xsSingle xs x) ⟩
        foldr (flip (foldr _∷_)) z (snocTree xs x)
    =⟨ splitSnocTree 0 z xs x ⟩
        foldr (flip (foldr _∷_)) [] xs ++ a ∷ z
    ∎
appendTree0FoldrSplit z (Deep v1 pr1 m1 sf1) (Deep v2 pr2 m2 sf2) =
    begin
        foldr (flip (foldr _∷_)) z (Deep (v1 + v2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2)
    =⟨⟩
        foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) z sf2) (addDigits0 m1 sf1 pr2 m2)) pr1
    =⟨ splitDigitNode^Foldr 0 (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) z sf2) (addDigits0 m1 sf1 pr2 m2)) pr1 ⟩
        foldr (flip (foldr _∷_)) [] pr1 ++ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) z sf2) (addDigits0 m1 sf1 pr2 m2))
    =⟨ cong (foldr (flip (foldr _∷_)) [] pr1 ++_) (splitFoldrFingerTree 1 (foldr (flip (foldr _∷_)) z sf2) (addDigits0 m1 sf1 pr2 m2)) ⟩
        foldr (flip (foldr _∷_)) [] pr1 ++ (foldr (flip (foldr (flip (foldr _∷_)))) [] (addDigits0 m1 sf1 pr2 m2)) ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (λ xs → foldr (flip (foldr _∷_)) [] pr1 ++ xs ++ (foldr (flip (foldr _∷_)) z sf2)) (addDigits0FoldrSplit [] m1 m2 sf1 pr2) ⟩
        foldr (flip (foldr _∷_)) [] pr1 ++ (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1
        ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2) ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (foldr (flip (foldr _∷_)) [] pr1 ++_) (sym (associativeConcatList (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1) 
                                                        (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2) (foldr (flip (foldr _∷_)) z sf2))) ⟩
        foldr (flip (foldr _∷_)) [] pr1 ++ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1
        ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2 ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ associativeConcatList (foldr (flip (foldr _∷_)) [] pr1) (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1) 
                            (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2 ++ (foldr (flip (foldr _∷_)) z sf2)) ⟩
        (foldr (flip (foldr _∷_)) [] pr1 ++ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1)
        ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2 ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (_++ (foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2 ++ (foldr (flip (foldr _∷_)) z sf2))) 
            (sym (splitDigitNode^Foldr 0 (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) [] sf1) m1) pr1)) ⟩
        foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1)
        ++ foldr (flip (foldr _∷_)) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2 ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (λ xs → foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ xs ++ (foldr (flip (foldr _∷_)) z sf2)) (splitDigitNode^Foldr 0 (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) pr2) ⟩
        foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ (foldr (flip (foldr _∷_)) [] pr2 ++ (foldr (flip (foldr (flip (foldr _∷_)))) [] m2)) ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++_) (sym (associativeConcatList (foldr (flip (foldr _∷_)) [] pr2) (foldr (flip (foldr (flip (foldr _∷_)))) [] m2) (foldr (flip (foldr _∷_)) z sf2))) ⟩
        foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ foldr (flip (foldr _∷_)) [] pr2 ++ foldr (flip (foldr (flip (foldr _∷_)))) [] m2 ++ (foldr (flip (foldr _∷_)) z sf2)
    =⟨ cong (λ xs → foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ foldr (flip (foldr _∷_)) [] pr2 ++ xs) (sym (splitFoldrFingerTree 1 (foldr (flip (foldr _∷_)) z sf2) m2)) ⟩
        foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ foldr (flip (foldr _∷_)) [] pr2 ++ foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) z sf2) m2
    =⟨ cong (λ xs → (foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1)) ++ xs) (sym (splitDigitNode^Foldr 0 (foldr (flip (foldr (flip (foldr _∷_)))) (foldr (flip (foldr _∷_)) z sf2) m2) pr2))  ⟩
        foldr (flip (foldr _∷_)) [] (Deep v1 pr1 m1 sf1) ++ foldr (flip (foldr _∷_)) z (Deep v2 pr2 m2 sf2)
    ∎






associativeAppendTree0 : {a : Set} -> (z : List a) -> (xs ys zs : FingerTree (Elem a)) 
                -> foldr (flip (foldr _∷_)) z (appendTree0 (appendTree0 xs ys) zs) ≡ foldr (flip (foldr _∷_)) z (appendTree0 xs (appendTree0 ys zs))
associativeAppendTree0 z xs ys zs = 
    begin
        foldr (flip (foldr _∷_)) z (appendTree0 (appendTree0 xs ys) zs)
    =⟨ appendTree0FoldrSplit z (appendTree0 xs ys) zs ⟩
        foldr (flip (foldr _∷_)) [] (appendTree0 xs ys) ++ foldr (flip (foldr _∷_)) z zs
    =⟨ cong (_++ foldr (flip (foldr _∷_)) z zs) (appendTree0FoldrSplit [] xs ys) ⟩
        (foldr (flip (foldr _∷_)) [] xs ++ foldr (flip (foldr _∷_)) [] ys) ++ foldr (flip (foldr _∷_)) z zs
    =⟨ sym (associativeConcatList (foldr (flip (foldr _∷_)) [] xs) (foldr (flip (foldr _∷_)) [] ys) (foldr (flip (foldr _∷_)) z zs)) ⟩
        foldr (flip (foldr _∷_)) [] xs ++ foldr (flip (foldr _∷_)) [] ys ++ foldr (flip (foldr _∷_)) z zs
    =⟨ cong (foldr (flip (foldr _∷_)) [] xs ++_) (sym (appendTree0FoldrSplit z ys zs)) ⟩
        foldr (flip (foldr _∷_)) [] xs ++ foldr (flip (foldr _∷_)) z (appendTree0 ys zs)
    =⟨ sym (appendTree0FoldrSplit z xs (appendTree0 ys zs)) ⟩
        foldr (flip (foldr _∷_)) z (appendTree0 xs (appendTree0 ys zs))
    ∎








associativeConcatSeq : {a : Set} -> (xs ys zs : Seq a) -> toList ((xs >< ys) >< zs) ≡ toList (xs >< (ys >< zs))
associativeConcatSeq (Sequence xs) (Sequence ys) (Sequence zs) = 
    begin
        toList (Sequence (appendTree0 (appendTree0 xs ys) zs))
    =⟨⟩
        foldr (flip (foldr _∷_)) [] (appendTree0 (appendTree0 xs ys) zs)
    =⟨ associativeAppendTree0 [] xs ys zs ⟩
        foldr (flip (foldr _∷_)) [] (appendTree0 xs (appendTree0 ys zs))
    =⟨⟩
        toList (Sequence (appendTree0 xs (appendTree0 ys zs)))
    ∎