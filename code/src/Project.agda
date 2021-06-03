module Project where

open import Haskell.Prelude
  hiding (scanl; scanr; scanl1; scanr1; splitAt; take; drop; filter; lookup; zipWith; zip; zipWith3; zip3; reverse; length; unzip)

open import DataTypes

open import Preconditions



{-# FOREIGN AGDA2HS
{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternGuards #-}
{-# OPTIONS_HADDOCK not-home #-}
import Prelude hiding (scanl, scanr, scanl1, scanr1, splitAt, take, drop, filter, lookup, zipWith, zip, zipWith3, zip3, reverse)
import Data.Foldable
#-}

open import Agda.Builtin.Nat renaming (_+_ to _+Nat_; _==_ to _==Nat_; _-_ to _-Nat_; _<_ to _<Nat_; _*_ to _*Nat_)
open import Agda.Builtin.Word


-- Basic Seqs
-- O(1) EmptyT sequence.
pattern Empty = Sequence EmptyT
--{-# COMPILE AGDA2HS Empty #-}

-- TODO DEFINE OTHER
--  PATTERNS!!

---------------
-- Construction
---------------

-- An empty sequence
empty : {a : Set} -> Seq a
empty = Sequence EmptyT
{-# COMPILE AGDA2HS empty #-}

-- A singleton sequence.
singleton : {a : Set} -> a -> Seq a
singleton x = Sequence (Single (Element x))
{-# COMPILE AGDA2HS singleton #-}

-- <| helper
consTree : {a : Set} -> {{Sized a}} -> a -> FingerTree a -> FingerTree a
consTree a EmptyT = Single a
consTree a (Single b) = deep (One a) EmptyT (One b)
consTree a (Deep s (Four b c d e) m sf) = (Deep (size a + s) (Two a b) (consTree (node3 c d e) m) sf)
consTree a (Deep s (Three b c d) m sf) =
    Deep (size a + s) (Four a b c d) m sf
consTree a (Deep s (Two b c) m sf) =
    Deep (size a + s) (Three a b c) m sf
consTree a (Deep s (One b) m sf) =
    Deep (size a + s) (Two a b) m sf
{-# COMPILE AGDA2HS consTree #-}    

-- Add an element to the left end of a sequence.
_<|_ : {a : Set} -> a -> Seq a -> Seq a
x <| Sequence xs = Sequence (consTree (Element x) xs)
{-# COMPILE AGDA2HS _<|_ #-}


-- |> helper
snocTree : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> FingerTree a
snocTree EmptyT a = Single a
snocTree (Single a) b = deep (One a) EmptyT (One b)
snocTree (Deep s pr m (Four a b c d)) e = (Deep (s + size e) pr (snocTree m (node3 a b c)) (Two d e))
snocTree (Deep s pr m (Three a b c)) d =
    Deep (s + size d) pr m (Four a b c d)
snocTree (Deep s pr m (Two a b)) c =
    Deep (s + size c) pr m (Three a b c)
snocTree (Deep s pr m (One a)) b =
    Deep (s + size b) pr m (Two a b)
{-# COMPILE AGDA2HS snocTree #-}

-- Add an element to the right end of a sequence.
_|>_ : {a : Set} -> Seq a -> a -> Seq a
Sequence xs |> x = Sequence (snocTree xs (Element x))
{-# COMPILE AGDA2HS _|>_ #-}

--Machine generate code taken from the source of Data.Sequence.Internal
appendTree0 : {a : Set} -> ⦃ Sized a ⦄ -> FingerTree a -> FingerTree a -> FingerTree a
addDigits0 : {a : Set} -> ⦃ Sized a ⦄ -> FingerTree (Node a) -> Digit a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree1 : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> FingerTree a -> FingerTree a
addDigits1 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Digit a -> a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree2 : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> a -> FingerTree a -> FingerTree a
addDigits2 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Digit a -> a -> a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree3 : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> a -> a -> FingerTree a -> FingerTree a
addDigits3 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Digit a -> a -> a -> a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)
appendTree4 : {a : Set} -> {{Sized a}} -> FingerTree a -> a -> a -> a -> a -> FingerTree a -> FingerTree a
addDigits4 : {a : Set} -> {{Sized a}} -> FingerTree (Node a) -> Digit a -> a -> a -> a -> a -> Digit a -> FingerTree (Node a) -> FingerTree (Node a)

appendTree0 EmptyT xs = xs
appendTree0 xs EmptyT = 
    xs
appendTree0 (Single x) xs =
    consTree x xs
appendTree0 xs (Single x) = 
    snocTree xs x
appendTree0 (Deep s1 pr1 m1 sf1) (Deep s2 pr2 m2 sf2) =
    Deep (s1 + s2) pr1 (addDigits0 m1 sf1 pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree0 #-}

addDigits0 m1 (One a) (One b) m2 =
    appendTree1 m1 (node2 a b) m2
addDigits0 m1 (One a) (Two b c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (One a) (Three b c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (One a) (Four b c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits0 m1 (Two a b) (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Two a b) (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Two a b) (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits0 m1 (Three a b c) (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Three a b c) (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Three a b c) (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits0 m1 (Four a b c d) (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits0 m1 (Four a b c d) (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits0 m1 (Four a b c d) (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
{-# COMPILE AGDA2HS addDigits0 #-}

appendTree1 EmptyT a xs =
    consTree a xs
appendTree1 xs a EmptyT =
    snocTree xs a
appendTree1 (Single x) a xs =
    consTree x (consTree a xs)
appendTree1 xs a (Single x) =
    snocTree (snocTree xs a) x
appendTree1 (Deep s1 pr1 m1 sf1) a (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + s2) pr1 (addDigits1 m1 sf1 a pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree1 #-}    

addDigits1 m1 (One a) b (One c) m2 =
    appendTree1 m1 (node3 a b c) m2
addDigits1 m1 (One a) b (Two c d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (One a) b (Three c d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (One a) b (Four c d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits1 m1 (Two a b) c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Two a b) c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Two a b) c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits1 m1 (Three a b c) d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Three a b c) d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Three a b c) d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits1 m1 (Four a b c d) e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits1 m1 (Four a b c d) e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits1 m1 (Four a b c d) e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
{-# COMPILE AGDA2HS addDigits1 #-}

appendTree2 EmptyT a b xs =
    consTree a (consTree b xs)
appendTree2 xs a b EmptyT =
    snocTree (snocTree xs a) b
appendTree2 (Single x) a b xs =
    consTree x (consTree a (consTree b xs))
appendTree2 xs a b (Single x) =
    snocTree (snocTree (snocTree xs a) b) x
appendTree2 (Deep s1 pr1 m1 sf1) a b (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + s2) pr1 (addDigits2 m1 sf1 a b pr2 m2) sf2 
{-# COMPILE AGDA2HS appendTree2 #-} 

addDigits2 m1 (One a) b c (One d) m2 =
    appendTree2 m1 (node2 a b) (node2 c d) m2
addDigits2 m1 (One a) b c (Two d e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (One a) b c (Three d e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (One a) b c (Four d e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits2 m1 (Two a b) c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Two a b) c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Two a b) c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits2 m1 (Three a b c) d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Three a b c) d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Three a b c) d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits2 m1 (Four a b c d) e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits2 m1 (Four a b c d) e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits2 m1 (Four a b c d) e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
{-# COMPILE AGDA2HS addDigits2 #-}

appendTree3 EmptyT a b c xs =
    consTree a (consTree b (consTree c xs))
appendTree3 xs a b c EmptyT =
    snocTree (snocTree (snocTree xs a) b) c
appendTree3 (Single x) a b c xs =
    consTree x (consTree a (consTree b (consTree c xs)))
appendTree3 xs a b c (Single x) =
    snocTree (snocTree (snocTree (snocTree xs a) b) c) x
appendTree3 (Deep s1 pr1 m1 sf1) a b c (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + s2) pr1 (addDigits3 m1 sf1 a b c pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree3 #-} 

addDigits3 m1 (One a) b c d (One e) m2 =
    appendTree2 m1 (node3 a b c) (node2 d e) m2
addDigits3 m1 (One a) b c d (Two e f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (One a) b c d (Three e f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (One a) b c d (Four e f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits3 m1 (Two a b) c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Two a b) c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Two a b) c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits3 m1 (Three a b c) d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Three a b c) d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Three a b c) d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits3 m1 (Four a b c d) e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits3 m1 (Four a b c d) e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits3 m1 (Four a b c d) e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
{-# COMPILE AGDA2HS addDigits3 #-}

appendTree4 EmptyT a b c d xs =
    consTree a (consTree b (consTree c (consTree d xs)))
appendTree4 xs a b c d EmptyT =
    snocTree (snocTree (snocTree (snocTree xs a) b) c) d
appendTree4 (Single x) a b c d xs =
    consTree x (consTree a (consTree b (consTree c (consTree d xs))))
appendTree4 xs a b c d (Single x) =
    snocTree (snocTree (snocTree (snocTree (snocTree xs a) b) c) d) x
appendTree4 (Deep s1 pr1 m1 sf1) a b c d (Deep s2 pr2 m2 sf2) =
    Deep (s1 + size a + size b + size c + size d + s2) pr1 (addDigits4 m1 sf1 a b c d pr2 m2) sf2
{-# COMPILE AGDA2HS appendTree4 #-} 

addDigits4 m1 (One a) b c d e (One f) m2 =
    appendTree2 m1 (node3 a b c) (node3 d e f) m2
addDigits4 m1 (One a) b c d e (Two f g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (One a) b c d e (Three f g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (One a) b c d e (Four f g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (One g) m2 =
    appendTree3 m1 (node3 a b c) (node2 d e) (node2 f g) m2
addDigits4 m1 (Two a b) c d e f (Two g h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Two a b) c d e f (Three g h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Two a b) c d e f (Four g h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (One h) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node2 g h) m2
addDigits4 m1 (Three a b c) d e f g (Two h i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Three a b c) d e f g (Three h i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Three a b c) d e f g (Four h i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (One i) m2 =
    appendTree3 m1 (node3 a b c) (node3 d e f) (node3 g h i) m2
addDigits4 m1 (Four a b c d) e f g h (Two i j) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node2 g h) (node2 i j) m2
addDigits4 m1 (Four a b c d) e f g h (Three i j k) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node2 j k) m2
addDigits4 m1 (Four a b c d) e f g h (Four i j k l) m2 =
    appendTree4 m1 (node3 a b c) (node3 d e f) (node3 g h i) (node3 j k l) m2
{-# COMPILE AGDA2HS addDigits4 #-}

-- Concatenates two sequences
_><_ : {a : Set} -> Seq a -> Seq a -> Seq a
Sequence xs >< Sequence ys = Sequence (appendTree0 xs ys)
{-# COMPILE AGDA2HS _><_ #-}



{-# TERMINATING #-}
unfoldr' : {a b : Set} -> (b -> Maybe (a × b)) -> Seq a -> b → Seq a
unfoldr' f as b = maybe as (λ tpl -> case tpl of 
                                    λ {
                                        (a , b') -> unfoldr' f (as |> a) b' 
                                    }) (f b)
{-# COMPILE AGDA2HS unfoldr' #-}

-- | Builds a sequence from a seed value.  Takes time linear in the
-- number of generated elements.  /WARNING:/ If the number of generated
-- elements is infinite, this method will not terminate.
unfoldr : {a b : Set} -> (b -> Maybe (a × b)) -> b -> Seq a
unfoldr f = unfoldr' f empty
{-# COMPILE AGDA2HS unfoldr #-}


{-# TERMINATING #-}
unfoldl' : {a b : Set} -> (b -> Maybe (b × a)) -> Seq a -> b → Seq a
unfoldl' f as b = maybe as (λ tpl -> case tpl of 
                                    λ {
                                        (b' , a) -> unfoldl' f (a <| as) b' 
                                    }) (f b)
{-# COMPILE AGDA2HS unfoldl' #-}

-- | @'unfoldl' f x@ is equivalent to @'reverse' ('unfoldr' ('fmap' swap . f) x)@.
unfoldl : {a b : Set} -> (b -> Maybe (b × a)) -> b -> Seq a
unfoldl f = unfoldl' f empty
{-# COMPILE AGDA2HS unfoldl #-}

{-# TERMINATING #-}
--  Constructs a sequence by repeated application of a function to a seed value.
iterateN : {a : Set} -> Int -> (a -> a) -> a -> Seq a
iterateN n f a = if n == 0 then Sequence EmptyT else a' <| iterateN (n - 1) f a'
                where a' = (f a)
{-# COMPILE AGDA2HS iterateN #-}

--Takes a list and converts it to a Sequence
fromList : {a : Set} -> List a -> Seq a
fromList xs = foldr (_<|_) (Sequence EmptyT) xs
{-# COMPILE AGDA2HS fromList #-}

--Make this more efficient!
apSeq : {a b : Set} -> Seq (a -> b) -> Seq a -> Seq b
apSeq fs xs = fromList (toList fs <*> (toList xs)) 
{-# COMPILE AGDA2HS apSeq #-}

instance
  SeqApplicative : Applicative Seq
  SeqApplicative .pure = singleton
  SeqApplicative ._<*>_ = apSeq
{-# COMPILE AGDA2HS SeqApplicative #-}


instance
  SeqMonad : Monad Seq
  SeqMonad ._>>=_ xs f = foldl (λ ys x -> ys >< (f x)) empty xs
{-# COMPILE AGDA2HS SeqMonad #-}

instance
  SeqSemigroup : Semigroup (Seq a)
  SeqSemigroup ._<>_ = _><_
{-# COMPILE AGDA2HS SeqSemigroup #-}

instance
  SeqMonoid : Monoid (Seq a)
  SeqMonoid .mempty = empty
{-# COMPILE AGDA2HS SeqMonoid #-}



pullL : {a : Set} -> {{Sized a}} -> Int -> FingerTree (Node a) -> Digit a -> FingerTree a
pullL s m sf = case viewLTree m of
    λ {
        EmptyLTree            -> digitToTree' s sf
      ; (ConsLTree pr m')     -> Deep s (nodeToDigit pr) m' sf
    }
{-# COMPILE AGDA2HS pullL #-}

pullR : {a : Set} -> {{Sized a}} -> Int -> Digit a -> FingerTree (Node a) -> FingerTree a
pullR s pr m = case viewRTree m of
    λ {
        EmptyRTree            -> digitToTree' s pr
      ; (SnocRTree m' sf)     -> Deep s pr m' (nodeToDigit sf)
    }
{-# COMPILE AGDA2HS pullR #-}



----------
--Scans
----------
--  INEFFICIENT SCANS! FIX

scanlList : (b → a → b) → b → List a → List b
scanlList f z []       = z ∷ []
scanlList f z (x ∷ xs) = z ∷ scanlList f (f z x) xs
{-# COMPILE AGDA2HS scanlList #-}

scanrList : (a → b → b) → b → List a → List b
scanrList f z [] = z ∷ []
scanrList f z (x ∷ xs) =
  case scanrList f z xs of λ where
    [] -> [] -- impossible
    qs@(q ∷ _) -> f x q ∷ qs
{-# COMPILE AGDA2HS scanrList #-}


scanl : {a b : Set} -> (a -> b -> a) -> a -> Seq b -> Seq a
scanl f z xs = fromList (scanlList f z (toList xs))
{-# COMPILE AGDA2HS scanl #-}


scanr : {a b : Set} -> (a -> b -> b) -> b -> Seq a -> Seq b
scanr f z xs = fromList (scanrList f z (toList xs))
{-# COMPILE AGDA2HS scanr #-}



safeScanL1 : {a : Set} -> (a -> a -> a) -> (vl : ViewL a) -> {IsTrue (isNotEmptyViewL vl)} -> Seq a
safeScanL1 _ EmptyL = error "scanl1 takes a nonempty sequence as argument"
safeScanL1 f (x :< xs) = scanl f x xs
{-# COMPILE AGDA2HS safeScanL1 #-}

safeScanR1 : {a : Set} -> (a -> a -> a) -> (vr : ViewR a) -> {IsTrue (isNotEmptyViewR vr)} -> Seq a
safeScanR1 _ EmptyR = error "scanr1 takes a nonempty sequence as argument"
safeScanR1 f (xs :> x) = scanr f x xs
{-# COMPILE AGDA2HS safeScanR1 #-}

scanl1 : {a : Set} -> (a -> a -> a) -> (xs : Seq a) -> {IsTrue (isNotEmptySequence xs)} -> Seq a
scanl1 f xs {notEmpty} = safeScanL1 f (viewl xs) {notEmptySeq->notEmptyViewL xs notEmpty}
{-# COMPILE AGDA2HS scanl1 #-}

scanr1 : {a : Set} -> (a -> a -> a) -> (xs : Seq a) -> {IsTrue (isNotEmptySequence xs)} -> Seq a
scanr1 f xs {notEmpty} = safeScanR1 f (viewr xs) {notEmptySeq->notEmptyViewR xs notEmpty}
{-# COMPILE AGDA2HS scanr1 #-}



-----------
-- Sublists
-----------

tailsDigit : {a : Set} -> Digit a -> Digit (Digit a)
tailsDigit (One a) = One (One a)
tailsDigit (Two a b) = Two (Two a b) (One b)
tailsDigit (Three a b c) = Three (Three a b c) (Two b c) (One c)
tailsDigit (Four a b c d) = Four (Four a b c d) (Three b c d) (Two c d) (One d)
{-# COMPILE AGDA2HS tailsDigit #-}

initsDigit : {a : Set} -> Digit a -> Digit (Digit a)
initsDigit (One a) = One (One a)
initsDigit (Two a b) = Two (One a) (Two a b)
initsDigit (Three a b c) = Three (One a) (Two a b) (Three a b c)
initsDigit (Four a b c d) = Four (One a) (Two a b) (Three a b c) (Four a b c d)
{-# COMPILE AGDA2HS initsDigit #-}

tailsNode : {a : Set} -> Node a -> Node (Digit a)
tailsNode (Node2 s a b) = Node2 s (Two a b) (One b)
tailsNode (Node3 s a b c) = Node3 s (Three a b c) (Two b c) (One c)
{-# COMPILE AGDA2HS tailsNode #-}

initsNode : {a : Set} -> Node a -> Node (Digit a)
initsNode (Node2 s a b) = Node2 s (One a) (Two a b)
initsNode (Node3 s a b c) = Node3 s (One a) (Two a b) (Three a b c)
{-# COMPILE AGDA2HS initsNode #-}


-- | Given a function to apply to tails of a tree, applies that function
-- to every tail of the specified tree.
tailsTree : {a b : Set} -> {{Sized a}} -> (FingerTree a -> b) -> FingerTree a -> FingerTree b
tailsTree {a} {b} _ EmptyT = EmptyT
tailsTree {a} {b} f (Single x) = Single (f (Single x))
tailsTree {a} {b} f (Deep n pr m sf) =
    Deep n (fmap (\ pr' -> f (deep pr' m sf)) (tailsDigit pr))
        (tailsTree f' m)
        (fmap (f ∘ digitToTree) (tailsDigit sf))
  where
    f' : FingerTree (Node a) -> Node b
    f' ms = case viewLTree ms of
        λ {
            EmptyLTree          -> Node2 2 (f EmptyT) (f EmptyT) --impossible
          ; (ConsLTree node m') -> fmap (\ pr' -> f (deep pr' m' sf)) (tailsNode node)
        }
{-# COMPILE AGDA2HS tailsTree #-}                 


-- | Given a function to apply to inits of a tree, applies that function
-- to every init of the specified tree.
initsTree : {a b : Set} -> {{Sized a}} -> (FingerTree a -> b) -> FingerTree a -> FingerTree b
initsTree {a} {b} _ EmptyT = EmptyT
initsTree {a} {b} f (Single x) = Single (f (Single x))
initsTree {a} {b} f (Deep n pr m sf) =
    Deep n (fmap (f ∘ digitToTree) (initsDigit pr))
        (initsTree f' m)
        (fmap (f ∘ deep pr m) (initsDigit sf))
  where
    f' : FingerTree (Node a) -> Node b
    f' ms = case viewRTree ms of 
        λ {
            EmptyRTree          -> Node2 2 (f EmptyT) (f EmptyT) --impossible
          ; (SnocRTree m' node) -> fmap (\ sf' -> f (deep pr m' sf')) (initsNode node)
        }
{-# COMPILE AGDA2HS initsTree #-}  

-- | \( O(n) \).  Returns a sequence of all suffixes of this sequence, longest first.  For example,
tails : {a : Set} -> Seq a -> Seq (Seq a)
tails (Sequence xs) = Sequence (tailsTree (Element ∘ Sequence) xs) |> empty
{-# COMPILE AGDA2HS tails #-} 

-- Returns a sequence of all prefixes of this sequence, shortest first. 
inits : {a : Set} -> Seq a -> Seq (Seq a)
inits (Sequence xs) = empty <| Sequence (initsTree (Element ∘ Sequence) xs)
{-# COMPILE AGDA2HS inits #-} 


-----------
-- Indexing
-----------

lookupNode : {a : Set} -> {{Sized a}} -> Int -> Node a -> Int × a
lookupNode i (Node2 _ a b) = if i < sa then (i , a) 
                                       else ((i - sa) , b)
                           where
                                sa = size a
lookupNode i (Node3 _ a b c) = if i < sa then (i , a)
                                         else (if i < sab then ((i - sa) , b)
                                                          else ((i - sab) , c))
                            where
                                sa = size a
                                sab = sa + size b
{-# COMPILE AGDA2HS lookupNode #-} 

lookupDigit : {a : Set} -> {{Sized a}} -> Int -> Digit a -> Int × a
lookupDigit i (One a) = i , a
lookupDigit i (Two a b) = if i < sa then i , a
                                    else (i - sa) , b
                        where
                            sa = size a
lookupDigit i (Three a b c) = if i < sa then i , a
                                        else (if i < sab then (i - sa) , b
                                                         else (i - sab) , c)
                            where
                                sa = size a
                                sab = sa + size b
lookupDigit i (Four a b c d) = if i < sa then i , a
                                         else (if i < sab then (i - sa) , b
                                                          else (if i < sabc then (i - sab) , c
                                                                            else (i - sabc) , d))
                            where
                                sa = size a
                                sab = sa + size b
                                sabc = sab + size c
{-# COMPILE AGDA2HS lookupDigit #-} 

-- again unnecessary complications in pattern matching because agda won't believe me
lookupTree : {a : Set} -> {{Sized a}} -> Int -> (xs : FingerTree a) -> {IsTrue (isNotEmptyFingerTree xs)} -> Int × a
lookupTree _ EmptyT = error "lookupTree of empty tree"
lookupTree i (Single x) = i , x
lookupTree i (Deep _ pr EmptyT sf) = let spr = size pr
                                     in if i < spr then lookupDigit i pr
                                                   else lookupDigit (i - spr) sf
lookupTree i (Deep _ pr m@(Single _) sf) = let spr = size pr
                                               spm = spr + size m
                                            in  if i < spr then lookupDigit i pr
                                                                else (if i < spm then (case (lookupTree (i - spr) m {IsTrue.itsTrue}) of
                                                                λ {
                                                                    (i' , xs) -> lookupNode i' xs
                                                                }
                                                            )
                                                                                 else lookupDigit (i - spm) sf)
lookupTree i (Deep _ pr m@(Deep _ _ _ _) sf) =  let spr = size pr
                                                    spm = spr + size m
                                                 in  if i < spr then lookupDigit i pr
                                                                else (if i < spm then (case (lookupTree (i - spr) m {IsTrue.itsTrue}) of
                                                                λ {
                                                                    (i' , xs) -> lookupNode i' xs
                                                                }
                                                            )
                                                                                 else lookupDigit (i - spm) sf)
{-# COMPILE AGDA2HS lookupTree #-} 


-- lookup The element at the specified position,
-- counting from 0. If the specified position is negative or at
-- least the length of the sequence, 'lookup' returns 'Nothing'.
lookup : {a : Set} -> Int -> (ss : Seq a) -> {IsTrue (isNotEmptySequence ss)} -> Maybe a
lookup i ss@(Sequence xs) {notEmpty} = if i >= 0 && i < (size xs) && (isNotEmptyFingerTree xs) then (case (lookupTree i xs {nonEmptySeq->nonEmptyFingerTree ss {notEmpty}}) of 
                        λ {
                            (_ , Element x) -> Just x
                        })
                        else Nothing
{-# COMPILE AGDA2HS lookup #-} 

--infix flipped version of lookup
_!?_ : {a : Set} -> (ss : Seq a) -> {IsTrue (isNotEmptySequence ss)} -> Int -> Maybe a
_!?_ xs {notEmpty} i = lookup i xs {notEmpty}
{-# COMPILE AGDA2HS _!?_ #-}

errorIfNothing : {a : Set} -> (m : Maybe a) -> {IsTrue (isNotNothing m)} -> a
errorIfNothing Nothing = error "index out of bounds"
errorIfNothing (Just x) = x
{-# COMPILE AGDA2HS errorIfNothing #-}

--!? except it throws an error when the integer is negative or greater than the size of the sequence
index : {a : Set} -> (xs : Seq a) -> (i : Int) -> {notEmpty : IsTrue (isNotEmptySequence xs)} -> {IsTrue (isNotNothing (lookup i xs {notEmpty}))} -> a
index xs i {notEmpty} {notNothing} = errorIfNothing (lookup i xs {notEmpty}) {notNothing}
{-# COMPILE AGDA2HS index #-}

data Split (a : Set) : Set
    where Pivot : FingerTree (Node a) -> Node a -> FingerTree (Node a) -> Split a
{-# COMPILE AGDA2HS Split #-}


splitSuffixN : {a : Set} -> {{Sized a}} -> Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) -> Split a
splitSuffixN i s pr m (One a) = Pivot (pullR (s - size a) pr m) a EmptyT
splitSuffixN i s pr m (Two a b) = if i < sa then Pivot (pullR (s - size a - size b) pr m) a (Single b) else Pivot (Deep (s - size b) pr m (One a)) b EmptyT
                                where sa = size a

splitSuffixN i s pr m (Three a b c) = if i < sa then Pivot (pullR (s - sab - size c) pr m) a (deep (One b) EmptyT (One c))
                                                else (if i < sab then Pivot (Deep (s - size b - size c) pr m (One a)) b (Single c) 
                                                                 else Pivot (Deep (s - size c) pr m (Two a b)) c EmptyT) 
                                    where sa      = size a
                                          sab     = sa + size b

splitSuffixN i s pr m (Four a b c d) = if i < sa then Pivot (pullR (s - sa - sbcd) pr m) a (Deep sbcd (Two b c) EmptyT (One d))
                                                 else (if i < sab then Pivot (Deep (s - sbcd) pr m (One a)) b (Deep scd (One c) EmptyT (One d))
                                                                  else (if i < sabc then Pivot (Deep (s - scd) pr m (Two a b)) c (Single d)
                                                                                    else Pivot (Deep (s - sd) pr m (Three a b c)) d EmptyT ) )
                                    where sa      = size a
                                          sab     = sa + size b
                                          sabc    = sab + size c
                                          sd      = size d
                                          scd     = size c + sd
                                          sbcd    = size b + scd
{-# COMPILE AGDA2HS splitSuffixN #-}

splitSuffixE : {a : Set} -> Int -> Int -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> Digit (Elem a) -> ((FingerTree (Elem a)) × (FingerTree (Elem a)))
splitSuffixE i s pr m (One a) = pullR (s - 1) pr m , Single a
splitSuffixE i s pr m (Two a b) = if i == 0 then pullR (s - 2) pr m , Deep 2 (One a) EmptyT (One b)
                                            else Deep (s - 1) pr m (One a) , Single b
splitSuffixE i s pr m (Three a b c) = if i == 0 then pullR (s - 3) pr m , Deep 3 (Two a b) EmptyT (One c)
                                                else (if i == 1 then Deep (s - 2) pr m (One a) , Deep 2 (One b) EmptyT (One c)
                                                                else Deep (s - 1) pr m (Two a b) , Single c)
splitSuffixE i s pr m (Four a b c d) = if i == 0 then pullR (s - 4) pr m , Deep 4 (Two a b) EmptyT (Two c d)
                                                 else (if i == 1 then Deep (s - 3) pr m (One a) , Deep 3 (Two b c) EmptyT (One d)
                                                                 else (if i == 2 then Deep (s - 2) pr m (Two a b) , Deep 2 (One c) EmptyT (One d)
                                                                                 else Deep (s - 1) pr m (Three a b c) , Single d))
{-# COMPILE AGDA2HS splitSuffixE #-}

splitPrefixN : {a : Set} -> {{Sized a}} -> Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a) -> Split a
splitPrefixN i s (One a) m sf = Pivot EmptyT a (pullL (s - size a) m sf)
splitPrefixN i s (Two a b) m sf = if i < sa then Pivot EmptyT a (Deep (s - sa) (One b) m sf) 
                                            else Pivot (Single a) b (pullL (s - sa - size b) m sf)
                                where
                                    sa = size a
splitPrefixN i s (Three a b c) m sf = if i < sa then Pivot EmptyT a (Deep (s - sa) (Two b c) m sf)
                                                else (if i < sab then Pivot (Single a) b (Deep (s - sab) (One c) m sf)
                                                                 else Pivot (Deep sab (One a) EmptyT (One b)) c (pullL (s - sab - size c) m sf))
                                    where
                                        sa      = size a
                                        sab     = sa + size b
splitPrefixN i s (Four a b c d) m sf = if i < sa then Pivot EmptyT a $ Deep (s - sa) (Three b c d) m sf
                                                 else (if i < sab then Pivot (Single a) b $ Deep (s - sab) (Two c d) m sf
                                                                  else (if i < sabc then Pivot (Deep sab (One a) EmptyT (One b)) c $ Deep (s - sabc) (One d) m sf
                                                                                    else Pivot (Deep sabc (Two a b) EmptyT (One c)) d $ pullL (s - sabc - size d) m sf))
                                    where
                                        sa      = size a
                                        sab     = sa + size b
                                        sabc    = sab + size c
{-# COMPILE AGDA2HS splitPrefixN #-}

splitPrefixE : {a : Set} -> Int -> Int -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> Digit (Elem a) -> (FingerTree (Elem a)) × (FingerTree (Elem a))
splitPrefixE i s (One a) m sf = EmptyT , Deep s (One a) m sf
splitPrefixE i s (Two a b) m sf = if i == 0 then EmptyT , Deep s (Two a b) m sf
                                            else Single a , Deep (s - 1) (One b) m sf
splitPrefixE i s (Three a b c) m sf = if i == 0 then EmptyT , Deep s (Three a b c) m sf
                                                else (if i == 1 then Single a , Deep (s - 1) (Two b c) m sf
                                                                else Deep 2 (One a) EmptyT (One b) , Deep (s - 2) (One c) m sf)
splitPrefixE i s (Four a b c d) m sf = if i == 0 then EmptyT , Deep s (Four a b c d) m sf
                                                 else (if i == 1 then Single a , Deep (s - 1) (Three b c d) m sf
                                                                 else (if i == 2 then Deep 2 (One a) EmptyT (One b) , Deep (s - 2) (Two c d) m sf
                                                                                 else Deep 3 (Two a b) EmptyT (One c) , Deep (s - 3) (One d) m sf))
{-# COMPILE AGDA2HS splitPrefixE #-}

splitMiddleE : {a : Set} -> Int -> Int -> Int -> Digit (Elem a) -> FingerTree (Node (Elem a)) -> Node (Elem a) -> FingerTree (Node (Elem a)) -> Digit (Elem a)
             -> (FingerTree (Elem a)) × (FingerTree (Elem a))
splitMiddleE i s spr pr ml (Node2 _ a b) mr sf = if (i < 1) then (pullR sprml pr ml) , (Deep (s - sprml) (Two a b) mr sf)
                                                            else Deep sprmla pr ml (One a) , Deep (s - sprmla) (One b) mr sf
                                                where
                                                    sprml   = spr + size ml
                                                    sprmla  = 1 + sprml
splitMiddleE i s spr pr ml (Node3 _ a b c) mr sf = if i == 0 then (pullR sprml pr ml) , (Deep (s - sprml) (Three a b c) mr sf)
                                                             else (if i == 1 then (Deep sprmla pr ml (One a)) , (Deep (s - sprmla) (Two b c) mr sf)
                                                                             else Deep sprmlab pr ml (Two a b) , Deep (s - sprmlab) (One c) mr sf)
                                                where
                                                    sprml   = spr + size ml
                                                    sprmla  = 1 + sprml
                                                    sprmlab = sprmla + 1
{-# COMPILE AGDA2HS splitMiddleE #-}

splitMiddleN : {a : Set} -> {{Sized a}} -> Int -> Int -> Int -> Digit (Node a) -> FingerTree (Node (Node a)) -> Node (Node a) -> FingerTree (Node (Node a)) -> Digit (Node a)
             -> Split a
splitMiddleN i s spr pr ml (Node2 _ a b) mr sf = if i < sa then Pivot (pullR sprml pr ml) a (Deep (s - sprmla) (One b) mr sf)
                                                           else Pivot (Deep sprmla pr ml (One a)) b (pullL (s - sprmla - size b) mr sf)
                                                where
                                                    sa      = size a
                                                    sprml   = spr + size ml
                                                    sprmla  = sa + sprml
splitMiddleN i s spr pr ml (Node3 _ a b c) mr sf = if i < sa then Pivot (pullR sprml pr ml) a (Deep (s - sprmla) (Two b c) mr sf)
                                                             else (if i < sab then Pivot (Deep sprmla pr ml (One a)) b (Deep (s - sprmlab) (One c) mr sf)
                                                                              else Pivot (Deep sprmlab pr ml (Two a b)) c (pullL (s - sprmlab - size c) mr sf))
                                                    where
                                                        sa      = size a
                                                        sab     = sa + size b
                                                        sprml   = spr + size ml
                                                        sprmla  = sa + sprml
                                                        sprmlab = sprmla + size b
{-# COMPILE AGDA2HS splitMiddleN #-}

--The following two functions are needlessly complicated (have two extra cases) because I have to convince agda that it actually works

splitTreeN : {a : Set} -> {{Sized a}} -> Int -> (ft : FingerTree (Node a)) -> {IsTrue (isNotEmptyFingerTree ft)} -> Split a
splitTreeN i EmptyT = error "splitTreeN of empty tree"
splitTreeN i (Single x) = Pivot EmptyT x EmptyT
splitTreeN i (Deep s pr m@EmptyT sf) = if i < spr then splitPrefixN i s pr m sf
                                                else splitSuffixN (i - spr) s pr m sf
                                    where
                                        spr = size pr
                                        im = i - spr
splitTreeN i (Deep s pr m@(Single _) sf) = let spr = size pr
                                               spm = spr + size m
                                               im = i - spr
                                            in (if i < spr then splitPrefixN i s pr m sf
                                                        else (if i < spm then (case (splitTreeN im m {IsTrue.itsTrue}) of 
                                                                        λ {
                                                                            (Pivot ml xs mr) -> splitMiddleN (im - size ml) s spr pr ml xs mr sf
                                                                        })
                                                                         else splitSuffixN (i - spm) s pr m sf))

splitTreeN i (Deep s pr m@(Deep _ _ _ _) sf) = let spr = size pr
                                                   spm = spr + size m
                                                   im = i - spr
                                                in if i < spr then splitPrefixN i s pr m sf
                                                              else (if i < spm then (case (splitTreeN im m {IsTrue.itsTrue}) of 
                                                                        λ {
                                                                            (Pivot ml xs mr) -> splitMiddleN (im - size ml) s spr pr ml xs mr sf
                                                                        })
                                                                               else splitSuffixN (i - spm) s pr m sf)

{-# COMPILE AGDA2HS splitTreeN #-}

splitTreeE : {a : Set} -> Int -> FingerTree (Elem a) -> (FingerTree (Elem a)) × (FingerTree (Elem a))
splitTreeE i EmptyT = EmptyT , EmptyT
splitTreeE i t@(Single _) = if i <= 0 then (EmptyT , t)
                                      else (t , EmptyT)

splitTreeE i (Deep s pr m@EmptyT sf) = if i < spr then splitPrefixE i s pr m sf
                                                  else splitSuffixE (i - spr) s pr m sf
                                where
                                    spr     = size pr
                                    im      = i - spr

splitTreeE i (Deep s pr m@(Single _) sf) = let spr = size pr 
                                               spm = spr + size m
                                               im = i - spr
                                            in if i < spr then splitPrefixE i s pr m sf
                                                      else (if i < spm then (case splitTreeN im m {IsTrue.itsTrue} of 
                                                            λ {
                                                                (Pivot ml xs mr) -> splitMiddleE (im - size ml) s spr pr ml xs mr sf
                                                            })
                                                                        else splitSuffixE (i - spm) s pr m sf)


splitTreeE i (Deep s pr m@(Deep _ _ _ _) sf) = let spr = size pr
                                                   spm = spr + size m
                                                   im = i - spr
                                                in if i < spr then splitPrefixE i s pr m sf
                                                          else (if i < spm then (case splitTreeN im m {IsTrue.itsTrue} of 
                                                            λ {
                                                                (Pivot ml xs mr) -> splitMiddleE (im - size ml) s spr pr ml xs mr sf
                                                            })
                                                                            else splitSuffixE (i - spm) s pr m sf)
{-# COMPILE AGDA2HS splitTreeE #-}

-- finally the function we've been waiting for
-- Splits a sequence at the given position
splitAt : {a : Set} -> Int -> Seq a -> Seq a × Seq a
splitAt i xs@(Sequence t) = case splitTreeE i t of
                        λ {   
                            (l , r) -> (Sequence l , Sequence r)
                        }
{-# COMPILE AGDA2HS splitAt #-}

--takes the first n elements
take : {a : Set} -> Int -> Seq a -> Seq a
take i xs = fst (splitAt i xs)
{-# COMPILE AGDA2HS take #-}

--drops the first n elements
drop : {a : Set} -> Int -> Seq a -> Seq a 
drop i xs = snd (splitAt i xs)
{-# COMPILE AGDA2HS drop #-}

adjustNode : {a : Set} -> {{Sized a}} -> (Int -> a -> a) -> Int -> Node a -> Node a
adjustNode f i (Node2 s a b) = if i < sa then (let fia = f i a 
                                               in (seq fia (Node2 s fia b)))
                                         else (let fisab = f (i - sa) b 
                                               in (seq fisab (Node2 s a fisab)))
                                where
                                    sa = size a
adjustNode f i (Node3 s a b c) = if i < sa then (let fia = f i a 
                                                 in (seq fia (Node3 s fia b c)))
                                           else (if i < sab then (let fisab = f (i - sa) b 
                                                                   in (seq fisab  (Node3 s a fisab c)))
                                                             else (let fisabc = f (i - sab) c 
                                                                   in (seq fisabc (Node3 s a b fisabc))))
                                where
                                    sa = size a
                                    sab = sa + size b
{-# COMPILE AGDA2HS adjustNode #-}

adjustDigit : {a : Set} -> {{Sized a}} -> (Int -> a -> a) -> Int -> Digit a -> Digit a
adjustDigit f i (One a) = One (f i a)
adjustDigit f i (Two a b) = if i < sa then (let fia = f i a 
                                            in (seq fia (Two fia b)))
                                      else (let fisab = f (i - sa) b 
                                            in (seq fisab (Two a fisab)))
                            where
                                sa = size a
adjustDigit f i (Three a b c) = if i < sa then (let fia = f i a 
                                                in (seq fia (Three fia b c)))
                                          else (if i < sab then (let fisab = f (i - sa) b 
                                                                 in (seq fisab (Three a fisab c)))
                                                           else (let fisabc = f (i - sab) c 
                                                                 in (seq fisabc (Three a b fisabc))))
                                where
                                    sa = size a
                                    sab = sa + size b
adjustDigit f i (Four a b c d) = if i < sa then (let fia = f i a 
                                                 in (seq fia (Four fia b c d)))
                                           else (if i < sab then (let fisab = f (i - sa) b 
                                                                  in (seq fisab (Four a fisab c d)))
                                                            else (if i < sabc then (let fisabc = f (i - sab) c 
                                                                                    in (seq fisabc (Four a b fisabc d)))
                                                                              else (let fisabcd = f (i - sabc) d 
                                                                                    in (seq fisabcd (Four a b c fisabcd)))))
                                where
                                    sa = size a
                                    sab = sa + size b
                                    sabc = sab + size c
{-# COMPILE AGDA2HS adjustDigit #-}

adjustTree : {a : Set} -> {{Sized a}} -> (Int -> a -> a) -> Int -> FingerTree a -> FingerTree a
adjustTree _ _ EmptyT = EmptyT -- Unreachable
adjustTree f i (Single x) = Single (f i x)
adjustTree f i (Deep s pr m sf) = if i < spr then Deep s (adjustDigit f i pr) m sf
                                             else (if i < spm then Deep s pr (adjustTree (adjustNode f) (i - spr) m) sf
                                                              else Deep s pr m (adjustDigit f (i - spm) sf))
                                where
                                    spr = size pr
                                    spm = spr + size m
{-# COMPILE AGDA2HS adjustTree #-}

updateNode : {a : Set} -> Elem a -> Int -> Node (Elem a) -> Node (Elem a)
updateNode v i (Node2 s a b) = if i < sa then Node2 s v b
                                         else Node2 s a v
                                where
                                    sa = size a
updateNode v i (Node3 s a b c) = if i < sa then Node3 s v b c
                                           else (if i < sab then Node3 s a v c
                                                            else Node3 s a b v)
                                where
                                    sa = size a
                                    sab = sa + size b
{-# COMPILE AGDA2HS updateNode #-}

updateDigit : {a : Set} -> Elem a -> Int -> Digit (Elem a) -> Digit (Elem a)
updateDigit v i (One _) = One v
updateDigit v i (Two a b) = if i < sa then Two v b
                                      else Two a v
                            where
                                sa = size a
updateDigit v i (Three a b c) = if i < sa then Three v b c
                                          else (if i < sab then Three a v c
                                                           else Three a b v)
                                where
                                    sa = size a
                                    sab = sa + size b
updateDigit v i (Four a b c d) = if i < sa then Four v b c d
                                           else (if i < sab then Four a v c d
                                                            else (if i < sabc then Four a b v d
                                                                              else Four a b c v))
                                where
                                    sa = size a
                                    sab = sa + size b
                                    sabc = sab + size c
{-# COMPILE AGDA2HS updateDigit #-}


updateTree : {a : Set} -> Elem a -> Int -> FingerTree (Elem a) -> FingerTree (Elem a)
updateTree _ _ EmptyT = EmptyT -- Unreachable
updateTree v i (Single _) = Single v
updateTree v i (Deep s pr m sf) = if i < spr then Deep s (updateDigit v i pr) m sf
                                             else (if i < spm then Deep s pr (adjustTree (updateNode v) (i - spr) m) sf
                                                              else Deep s pr m (updateDigit v (i - spm) sf))
                                where
                                    spr = size pr
                                    spm = spr + size m
{-# COMPILE AGDA2HS updateTree #-}

-- Replaces element at specified position. 
update : {a : Set} -> Int -> a -> Seq a -> Seq a
update i x (Sequence xs) = Sequence (updateTree (Element x) i xs)
{-# COMPILE AGDA2HS update #-}

-- Update the element at the specified position.
adjust : {a : Set} -> (a -> a) -> Int -> Seq a -> Seq a
adjust f i (Sequence xs) = Sequence (adjustTree (λ i' -> seq i' (fmap f)) i xs)
{-# COMPILE AGDA2HS adjust #-}

-- stricts the value first before updating
adjust' : {a : Set} -> (a -> a) -> Int -> (xs : Seq a) -> {IsTrue (isNotEmptySequence xs)} -> Seq a
adjust' f i xs {notEmpty} = case (_!?_ xs {notEmpty} i) of
                λ {
                    Nothing -> xs
                  ; (Just x) -> let x' = f x
                              in (seq x' (update i x' xs))
                }
{-# COMPILE AGDA2HS adjust' #-}

data Ins (a : Set) : Set where
    InsOne : a -> Ins a
    InsTwo : a -> a -> Ins a
{-# COMPILE AGDA2HS Ins #-}

data InsDigNode (a : Set) : Set where
    InsLeftDig : Digit a -> InsDigNode a
    InsDigitNode : Digit a -> Node a -> InsDigNode a
{-# COMPILE AGDA2HS InsDigNode #-}

data InsNodeDig (a : Set) : Set where
    InsRightDig : Digit a -> InsNodeDig a
    InsNodeDigit : Node a -> Digit a -> InsNodeDig a
{-# COMPILE AGDA2HS InsNodeDig #-}

insLeftDigit : {a : Set} -> {{Sized a}} -> (Int -> a -> Ins a) -> Int -> Digit a -> InsDigNode a
insLeftDigit f i (One a) = case f i a of
                    λ  {
                         (InsOne a') -> InsLeftDig $ One a'
                       ; (InsTwo a1 a2) -> InsLeftDig $ Two a1 a2
                    }
insLeftDigit f i (Two a b) = let sa = size a
                             in (if i < sa then (case f i a of
                                            λ {
                                                (InsOne a') -> InsLeftDig $ Two a' b
                                              ; (InsTwo a1 a2) -> InsLeftDig $ Three a1 a2 b
                                            })
                                       else (case f (i - sa) b of
                                            λ {
                                                (InsOne b') -> InsLeftDig $ Two a b'
                                              ; (InsTwo b1 b2) -> InsLeftDig $ Three a b1 b2
                                            }))
insLeftDigit f i (Three a b c) = let sa = size a
                                     sab = sa + size b
                                 in (if i < sa then (case f i a of
                                                λ {
                                                    (InsOne a') -> InsLeftDig $ Three a' b c
                                                  ; (InsTwo a1 a2) -> InsLeftDig $ Four a1 a2 b c
                                                })
                                            else (if i < sab then (case f (i - sa) b of
                                                                λ {
                                                                    (InsOne b') -> InsLeftDig $ Three a b' c
                                                                  ; (InsTwo b1 b2) -> InsLeftDig $ Four a b1 b2 c
                                                                })
                                                             else (case f (i - sab) c of
                                                                λ {
                                                                    (InsOne c') -> InsLeftDig $ Three a b c'
                                                                  ; (InsTwo c1 c2) -> InsLeftDig $ Four a b c1 c2
                                                                })))
insLeftDigit f i (Four a b c d) = let sa = size a
                                      sab = sa + size b
                                      sabc = sab + size c
                                  in (if i < sa then (case f i a of
                                            λ {
                                                (InsOne a') -> InsLeftDig $ Four a' b c d
                                              ; (InsTwo a1 a2) -> InsDigitNode (Two a1 a2) (node3 b c d)
                                            })
                                            else (if i < sab then (case f (i - sa) b of
                                                                λ {
                                                                    (InsOne b') -> InsLeftDig $ Four a b' c d
                                                                  ; (InsTwo b1 b2) -> InsDigitNode (Two a b1) (node3 b2 c d)
                                                                })
                                                             else (if i < sabc then (case f (i - sab) c of
                                                                                    λ {
                                                                                        (InsOne c') -> InsLeftDig $ Four a b c' d
                                                                                      ; (InsTwo c1 c2) -> InsDigitNode (Two a b) (node3 c1 c2 d)
                                                                                    })
                                                                                else (case f (i - sabc) d of
                                                                                    λ {
                                                                                        (InsOne d') -> InsLeftDig $ Four a b c d'
                                                                                      ; (InsTwo d1 d2) -> InsDigitNode (Two a b) (node3 c d1 d2)
                                                                                    }))))
{-# COMPILE AGDA2HS insLeftDigit #-}

insRightDigit : {a : Set} -> {{Sized a}} -> (Int -> a -> Ins a) -> Int -> Digit a -> InsNodeDig a
insRightDigit f i (One a) = case f i a of
                        λ {
                            (InsOne a') -> InsRightDig $ One a'
                          ; (InsTwo a1 a2) -> InsRightDig $ Two a1 a2
                        }
insRightDigit f i (Two a b) = let sa = size a
                              in (if i < sa then (case f i a of
                                            λ {
                                                (InsOne a') -> InsRightDig $ Two a' b
                                              ; (InsTwo a1 a2) -> InsRightDig $ Three a1 a2 b
                                            })
                                        else (case f (i - sa) b of
                                            λ {
                                                (InsOne b') -> InsRightDig $ Two a b'
                                              ; (InsTwo b1 b2) -> InsRightDig $ Three a b1 b2    
                                            }))
insRightDigit f i (Three a b c) = let sa = size a
                                      sab = sa + size b
                                  in (if i < sa then (case f i a of
                                                λ {
                                                    (InsOne a') -> InsRightDig $ Three a' b c
                                                  ; (InsTwo a1 a2) -> InsRightDig $ Four a1 a2 b c
                                                })
                                            else (if i < sab then (case f (i - sa) b of
                                                                λ {
                                                                    (InsOne b') -> InsRightDig $ Three a b' c
                                                                  ; (InsTwo b1 b2) -> InsRightDig $ Four a b1 b2 c
                                                                })
                                                             else (case f (i - sab) c of
                                                                λ {
                                                                    (InsOne c') -> InsRightDig $ Three a b c'
                                                                  ; (InsTwo c1 c2) -> InsRightDig $ Four a b c1 c2
                                                                })))
insRightDigit f i (Four a b c d) = let sa = size a
                                       sab = sa + size b
                                       sabc = sab + size c
                                   in (if i < sa then (case f i a of
                                                λ {
                                                    (InsOne a') -> InsRightDig $ Four a' b c d
                                                  ; (InsTwo a1 a2) -> InsNodeDigit (node3 a1 a2 b) (Two c d)
                                                })
                                             else (if i < sab then (case f (i - sa) b of
                                                                λ {
                                                                    (InsOne b') -> InsRightDig $ Four a b' c d
                                                                  ; (InsTwo b1 b2) -> InsNodeDigit (node3 a b1 b2) (Two c d)
                                                                })
                                                              else (if i < sabc then (case f (i - sab) c of
                                                                                    λ {
                                                                                        (InsOne c') -> InsRightDig $ Four a b c' d
                                                                                      ; (InsTwo c1 c2) -> InsNodeDigit (node3 a b c1) (Two c2 d)
                                                                                    })
                                                                                else (case f (i - sabc) d of
                                                                                    λ {
                                                                                        (InsOne d') -> InsRightDig $ Four a b c d'
                                                                                      ; (InsTwo d1 d2) -> InsNodeDigit (node3 a b c) (Two d1 d2)
                                                                                    }))))
{-# COMPILE AGDA2HS insRightDigit #-}

insNode : {a : Set} -> {{Sized a}} -> (Int -> a -> Ins a) -> Int -> Node a -> Ins (Node a)
insNode f i (Node2 s a b) = if i < (size a) then (case f i a of
                                        λ {
                                            (InsOne n) -> InsOne $ Node2 (s + 1) n b
                                          ; (InsTwo m n) -> InsOne $ Node3 (s + 1) m n b
                                        })
                                      else (case f (i - (size a)) b of
                                        λ {
                                            (InsOne n) -> InsOne $ Node2 (s + 1) a n
                                          ; (InsTwo m n) -> InsOne $ Node3 (s + 1) a m n
                                        })
insNode f i (Node3 s a b c) = let sa = size a
                                  sab = size b
                              in (if i < sa then (case f i a of
                                            λ {
      (InsOne n) -> InsOne $ Node3 (s + 1) n b c
     ;(InsTwo m n) -> InsTwo (Node2 (sa + 1) m n) (Node2 (s - sa) b c)
                                            })
                                        else (if i < sab then (case f (i - sa) b of
                                                        λ {
      (InsOne n) -> InsOne $ Node3 (s + 1) a n c
     ;(InsTwo m n) -> InsTwo (node2 a m) (node2 n c)
                                                        })
                                                         else (case f (i - sab) c of
                                                            λ {
      (InsOne n) -> InsOne $ Node3 (s + 1) a b n
     ;(InsTwo m n) -> InsTwo (Node2 sab a b) (Node2 (s - sab + 1) m n)
                                                            })))
{-# COMPILE AGDA2HS insNode #-}

insTree : {a : Set} -> {{Sized a}} -> (Int -> a -> Ins a) ->
             Int -> FingerTree a -> FingerTree a
insTree _ _ EmptyT = EmptyT -- Unreachable
insTree f i (Single x) = case f i x of
                            λ {
  (InsOne x') -> Single x'
 ;(InsTwo m n) -> deep (One m) EmptyT (One n)
                            }
insTree f i (Deep s pr m sf) = let spr = size pr
                                   spm = spr + size m
                               in (if i < spr then (case insLeftDigit f i pr of
                                            λ {
     (InsLeftDig pr') -> Deep (s + 1) pr' m sf
    ;(InsDigitNode pr' n) -> seq m (Deep (s + 1) pr' (consTree n m) sf)
                                            })
                                          else (if i < spm then (Deep (s + 1) pr (insTree (insNode f) (i - spr) m) sf)
                                                           else (case insRightDigit f (i - spm) sf of
                                                            λ {
     (InsRightDig sf') -> Deep (s + 1) pr m sf'
    ;(InsNodeDigit n sf') -> seq m (Deep (s + 1) pr (snocTree m n) sf')
                                                            })))
{-# COMPILE AGDA2HS insTree #-}

-- insert element at the given position
insertAt : {a : Set} -> Int -> a -> Seq a -> Seq a 
insertAt i a (Sequence xs) = Sequence (insTree (λ x -> seq x (InsTwo (Element a))) i xs)
{-# COMPILE AGDA2HS insertAt #-}


--------
-- Folds
--------

-- | 'foldlWithIndex' is a version of 'foldl' that also provides access
-- to the index of each element.
foldlWithIndex : {a b : Set} -> (b -> Int -> a -> b) -> b -> Seq a -> b
foldlWithIndex f z xs = foldl (\ g x i -> f (g (i - 1)) i x) (const z) xs (length xs - 1)
{-# COMPILE AGDA2HS foldlWithIndex #-} 

-- | 'foldrWithIndex' is a version of 'foldr' that also provides access
-- to the index of each element.
foldrWithIndex : {a b : Set} -> (Int -> a -> b -> b) -> b -> Seq a -> b
foldrWithIndex f z xs = foldr (\ x g i -> f i x (g (i + 1))) (const z) xs 0
{-# COMPILE AGDA2HS foldrWithIndex #-}


foldWithIndexDigit : {a b : Set} -> {{Sized a}} -> (b -> b -> b) -> (Int -> a -> b) -> Int -> Digit a -> b
foldWithIndexDigit _ f s (One a) = f s a
foldWithIndexDigit g f s (Two a b) = g (f s a) (f sPsa b)
  where
    sPsa = s + size a
foldWithIndexDigit g f s (Three a b c) = g (g (f s a) (f sPsa b)) (f sPsab c)
  where
    sPsa = s + size a
    sPsab = sPsa + size b
foldWithIndexDigit g f s (Four a b c d) =
    g (g (g (f s a) (f sPsa b)) (f sPsab c)) (f sPsabc d)
  where
    sPsa = s + size a
    sPsab = sPsa + size b
    sPsabc = sPsab + size c
{-# COMPILE AGDA2HS foldWithIndexDigit #-}

foldWithIndexNode : {a m : Set} -> {{Sized a}} -> (m -> m -> m) -> (Int -> a -> m) -> Int -> Node a -> m
foldWithIndexNode g f s (Node2 _ a b) = g (f s a) (f sPsa b)
  where
    sPsa = s + size a
foldWithIndexNode g f s (Node3 _ a b c) = g (g (f s a) (f sPsa b)) (f sPsab c)
  where
    sPsa = s + size a
    sPsab = sPsa + size b
{-# COMPILE AGDA2HS foldWithIndexNode #-}


foldMapWithIndexDigitE : {a : Set} -> {m : Set} -> {{Monoid m}} -> (Int -> Elem a -> m) -> Int -> Digit (Elem a) -> m
foldMapWithIndexDigitE f i t = foldWithIndexDigit (_<>_) f i t
{-# COMPILE AGDA2HS foldMapWithIndexDigitE #-}

foldMapWithIndexDigitN : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> Node a -> m) -> Int -> Digit (Node a) -> m
foldMapWithIndexDigitN f i t = foldWithIndexDigit (_<>_) f i t
{-# COMPILE AGDA2HS foldMapWithIndexDigitN #-}

foldMapWithIndexNodeE : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> Elem a -> m) -> Int -> Node (Elem a) -> m
foldMapWithIndexNodeE f i t = foldWithIndexNode (_<>_) f i t
{-# COMPILE AGDA2HS foldMapWithIndexNodeE #-}

foldMapWithIndexNodeN : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> Node a -> m) -> Int -> Node (Node a) -> m
foldMapWithIndexNodeN f i t = foldWithIndexNode (_<>_) f i t
{-# COMPILE AGDA2HS foldMapWithIndexNodeN #-}

foldMapWithIndexTreeN : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> Node a -> m) -> Int -> FingerTree (Node a) -> m
foldMapWithIndexTreeN _ _ EmptyT = mempty
foldMapWithIndexTreeN f s (Single xs) = f s xs
foldMapWithIndexTreeN f s (Deep _ pr m sf) =
               foldMapWithIndexDigitN f s pr <>
               foldMapWithIndexTreeN (foldMapWithIndexNodeN f) sPspr m <>
               foldMapWithIndexDigitN f sPsprm sf
    where
      sPspr = s + size pr
      sPsprm = sPspr + size m
{-# COMPILE AGDA2HS foldMapWithIndexTreeN #-}

foldMapWithIndexTreeE : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> Elem a -> m) -> Int -> FingerTree (Elem a) -> m
foldMapWithIndexTreeE _ _ EmptyT = mempty
foldMapWithIndexTreeE f s (Single xs) = f s xs
foldMapWithIndexTreeE f s (Deep _ pr m sf) =
               foldMapWithIndexDigitE f s pr <>
               foldMapWithIndexTreeN (foldMapWithIndexNodeE f) sPspr m <>
               foldMapWithIndexDigitE f sPsprm sf
    where
      sPspr = s + size pr
      sPsprm = sPspr + size m
{-# COMPILE AGDA2HS foldMapWithIndexTreeE #-}

-- A generalization of 'foldMap', 'foldMapWithIndex' takes a folding
-- function that also depends on the element's index, and applies it to every
-- element in the sequence.
foldMapWithIndex : {a : Set} -> {{Sized a}} -> {m : Set} -> {{Monoid m}} -> (Int -> a -> m) -> Seq a -> m
foldMapWithIndex {a} {m} f' (Sequence xs') = foldMapWithIndexTreeE (lift_elem f') 0 xs'
 where
  lift_elem : (Int -> a -> m) -> (Int -> Elem a -> m)
  lift_elem g = λ s e -> case e of
                    λ { 
                      (Element a) -> g s a
                    }
{-# COMPILE AGDA2HS foldMapWithIndex #-}
---------------------------
-- Indexing with predicates
---------------------------

-- find all indices of elements that satisfy the predicate from the left of the list
findIndicesL : {a : Set} -> (a -> Bool) -> Seq a -> List Int
findIndicesL p xs = foldrWithIndex (λ i x is -> if p x then i ∷ is else is) [] xs
{-# COMPILE AGDA2HS findIndicesL #-}

-- find all indices of elements that satisfy the predicate from the right of the list
findIndicesR : {a : Set} -> (a -> Bool) -> Seq a -> List Int
findIndicesR p xs = foldlWithIndex (λ is i x -> if p x then i ∷ is else is) [] xs
{-# COMPILE AGDA2HS findIndicesR #-}

listToMaybe' : {a : Set} -> List a -> Maybe a
listToMaybe' = foldr (\ x _ -> Just x) Nothing
{-# COMPILE AGDA2HS listToMaybe' #-}

-- finds the index of the leftmost element that satisfies p, if any exist
findIndexL : {a : Set} -> (a -> Bool) -> Seq a -> Maybe Int
findIndexL p = listToMaybe' ∘ findIndicesL p
{-# COMPILE AGDA2HS findIndexL #-}

-- finds the index of the rightmost element that satisfies p, if any exist.
findIndexR : {a : Set} -> (a -> Bool) -> Seq a -> Maybe Int
findIndexR p = listToMaybe' ∘ findIndicesR p
{-# COMPILE AGDA2HS findIndexR #-}

-- finds the indices of the specified element, from left to right (i.e. in ascending order).
elemIndicesL : {a : Set} -> {{Eq a}} -> a -> Seq a -> List Int
elemIndicesL x = findIndicesL (x ==_)
{-# COMPILE AGDA2HS elemIndicesL #-}

-- finds the indices of the specified element, from right to left (i.e. in descending order).
elemIndicesR : {a : Set} -> {{Eq a}} -> a -> Seq a -> List Int
elemIndicesR x = findIndicesR (x ==_)
{-# COMPILE AGDA2HS elemIndicesR #-}

-- finds the leftmost index of the specified element, if it is present, and otherwise 'Nothing'.
elemIndexL : {a : Set} -> {{Eq a}} -> a -> Seq a -> Maybe Int
elemIndexL x = findIndexL (x ==_)
{-# COMPILE AGDA2HS elemIndexL #-}

-- finds the rightmost index of the specified element, if it is present, and otherwise 'Nothing'.
elemIndexR : {a : Set} -> {{Eq a}} -> a -> Seq a -> Maybe Int
elemIndexR x = findIndexR (x ==_)
{-# COMPILE AGDA2HS elemIndexR #-}

----------------------
-- Sequential searches
----------------------

-- takes a predicate p and a sequence xs and returns a sequence of those elements which satisfy the predicate.
filter : {a : Set} -> (a -> Bool) -> Seq a -> Seq a
filter p = foldl (\ xs x -> if p x then xs |> x else xs) empty
{-# COMPILE AGDA2HS filter #-}

-- takes a predicate p and a sequence xs and returns sequences of those elements which do and do not satisfy the predicate.
partition : {a : Set} -> (a -> Bool) -> Seq a -> Seq a × Seq a
partition {a} p = foldl part (empty , empty)
  where
    part : Seq a × Seq a -> a → Seq a × Seq a
    part (xs , ys) x = if p x then (xs |> x) , ys
                              else xs , (ys |> x)
{-# COMPILE AGDA2HS partition #-}

-- applied to a predicate p and a sequence x\s, returns a pair whose first element is the longest prefix (possibly empty) of xs of elements that
-- do not satisfy p and the second element is the remainder of the sequence.
breakl : {a : Set} -> (a -> Bool) -> Seq a -> Seq a × Seq a
breakl p xs = foldr (\ i _ -> splitAt i xs) (xs , empty) (findIndicesL p xs)
{-# COMPILE AGDA2HS breakl #-}

-- mirror of breakl
breakr : {a : Set} -> (a -> Bool) -> Seq a -> Seq a × Seq a
breakr {a} p xs = foldr (\ i _ -> flipPair (splitAt (i + 1) xs)) (xs , empty) (findIndicesR p xs)
  where 
    flipPair : Seq a × Seq a -> Seq a × Seq a
    flipPair (x , y) = (y , x)
{-# COMPILE AGDA2HS breakr #-}

-- applied to a predicate p and a sequence xs, returns a pair whose first element is the longest prefix (possibly empty) of xs of elements that
-- satisfy p and the second element is the remainder of the sequence.
spanl : {a : Set} -> (a -> Bool) -> Seq a -> Seq a × Seq a
spanl p = breakl (not ∘ p)
{-# COMPILE AGDA2HS spanl #-}

-- applied to a predicate p and a sequence xs, returns a pair whose /first/ element is the longest /suffix/ (possibly empty) of xs of elements that
-- satisfy p and the second element is the remainder of the sequence.
spanr : {a : Set} -> (a -> Bool) -> Seq a -> Seq a × Seq a
spanr p = breakr (not ∘ p)
{-# COMPILE AGDA2HS spanr #-}

--  applied to a predicate p and a sequence xs, returns the longest prefix (possibly empty) of xs of elements that satisfy p.
takeWhileL : {a : Set} -> (a -> Bool) -> Seq a -> Seq a
takeWhileL p = fst ∘ spanl p
{-# COMPILE AGDA2HS takeWhileL #-}

-- reverse of takeWhileL
takeWhileR : {a : Set} -> (a -> Bool) -> Seq a -> Seq a
takeWhileR p = fst ∘ spanr p
{-# COMPILE AGDA2HS takeWhileR #-}

-- dropWhileL p xs returns the suffix remaining after takeWhileL p xs.
dropWhileL : {a : Set} -> (a -> Bool) -> Seq a -> Seq a
dropWhileL p = snd ∘ spanl p
{-# COMPILE AGDA2HS dropWhileL #-}

-- reverse of dropWhileL
dropWhileR : {a : Set} -> (a -> Bool) -> Seq a -> Seq a
dropWhileR p = snd ∘ spanr p
{-# COMPILE AGDA2HS dropWhileR #-}


-------
--Zips
-------

splitMapDigit : {a s : Set} -> {{Sized a}} -> (Int -> s -> (s × s)) -> (s -> a -> b) -> s -> Digit a -> Digit b
splitMapDigit _    f s (One a) = One (f s a)
splitMapDigit splt f s (Two a b) = Two (f (fst s') a) (f (snd s') b)
  where
    s' = splt (size a) s
splitMapDigit splt f s (Three a b c) = Three (f (fst s') a) (f (fst r') b) (f (snd r') c)
  where
    s' = splt (size a) s
    r' = splt (size b) (snd s')

splitMapDigit splt f s (Four a b c d) = Four (f (fst s') a) (f (fst s'') b) (f (snd s'') c) (f (snd middle) d)
  where
    s' = splt (size a) s
    middle = splt (size b + size c) (snd s')
    s'' = splt (size b) (fst middle)
{-# COMPILE AGDA2HS splitMapDigit #-}

splitMapNode : {a s : Set} -> {{Sized a}} -> (Int -> s -> (s × s)) -> (s -> a -> b) -> s -> Node a -> Node b
splitMapNode splt f s (Node2 ns a b) = Node2 ns (f (fst s') a) (f (snd s') b)
  where
    s' = splt (size a) s
splitMapNode splt f s (Node3 ns a b c) = Node3 ns (f (fst s') a) (f (fst s'') b) (f (snd s'') c)
  where
    s' = splt (size a) s
    s'' = splt (size b) (snd s')
{-# COMPILE AGDA2HS splitMapNode #-}

splitMapTreeN : {a b s : Set} -> {{Sized a}} -> (Int -> s -> (s × s)) -> (s -> Node a -> b) -> s -> FingerTree (Node a) -> FingerTree b
splitMapTreeN _ _ _ EmptyT = EmptyT
splitMapTreeN _ f s (Single xs) = Single $ f s xs
splitMapTreeN splt f s (Deep n pr m sf) = Deep n (splitMapDigit splt f prs pr) (splitMapTreeN splt (\eta1 eta2 -> splitMapNode splt f eta1 eta2) ms m) (splitMapDigit splt f sfs sf)
      where
        s' = splt (size pr) s
        prs = fst s'
        r = snd s'
        r' = splt (size m) r
        ms = fst r'
        sfs = snd r'
{-# COMPILE AGDA2HS splitMapTreeN #-}

splitMapTreeE : {s y : Set} -> (Int -> s -> (s × s)) -> (s -> Elem y -> b) -> s -> FingerTree (Elem y) -> FingerTree b
splitMapTreeE _  _ _ EmptyT = EmptyT
splitMapTreeE _  f s (Single xs) = Single $ f s xs
splitMapTreeE splt f s (Deep n pr m sf) = Deep n (splitMapDigit splt f prs pr) (splitMapTreeN splt (\eta1 eta2 -> splitMapNode splt f eta1 eta2) ms m) (splitMapDigit splt f sfs sf)
      where
        spr = size pr
        sm = n - spr - size sf
        s' = splt spr s
        prs = fst s'
        r = snd s'
        r' = splt sm r
        ms = fst r'
        sfs = snd r'
{-# COMPILE AGDA2HS splitMapTreeE #-}

splitMap : {a b s : Set} -> (Int -> s -> (s × s)) -> (s -> a -> b) -> s -> Seq a -> Seq b
splitMap splt' f0 s0 (Sequence xs0) = Sequence $ splitMapTreeE splt' (λ s' x -> case x of
                                                                            λ {
                                                                                (Element a) -> Element (f0 s' a)
                                                                            }) s0 xs0
{-# COMPILE AGDA2HS splitMap #-}


liftA2 : {a b c : Set} -> {f : Set -> Set} -> {{Applicative f}} -> (a -> b -> c) -> f a -> f b -> f c
liftA2 f x y = pure f <*> x <*> y
{-# COMPILE AGDA2HS liftA2 #-}

liftA3 : {a b c d : Set} -> {f : Set -> Set} -> {{Applicative f}} -> (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3 f x y z = pure f <*> x <*> y <*> z
{-# COMPILE AGDA2HS liftA3 #-}

{-# TERMINATING #-}
applicativeTree : {a : Set} -> {f : Set -> Set} -> {{Applicative f}} -> Nat -> Nat -> f a -> f (FingerTree a)
applicativeTree n mSize m = if n == 0 then pure EmptyT
                                      else (if n == 1 then fmap Single m
                                                      else (if n == 2 then deepA one emptyTree one
                                                                      else (if n == 3 then deepA two emptyTree one
                                                                                      else (if n == 4 then deepA two emptyTree two
                                                                                                      else (if n == 5 then deepA three emptyTree two 
                                                                                                                      else (if n == 6 then deepA three emptyTree three
                                      else (if rem == 0 then deepA three (applicativeTree (q -Nat 2) mSize' n3) three
                                                        else (if rem == 1 then deepA two (applicativeTree (q -Nat 1) mSize' n3) two
                                                                          else deepA three (applicativeTree (q -Nat 1) mSize' n3) two))))))))
  where
    mSize' = 3 * mSize
    n3 = liftA3 (Node3 (int64 (primWord64FromNat mSize'))) m m m
    one = fmap One m
    two = liftA2 Two m m
    three = liftA3 Three m m m
    deepA = liftA3 (Deep (int64 (primWord64FromNat (n * mSize))))
    emptyTree = pure EmptyT
    q = Agda.Builtin.Nat.div-helper 0 n 2 n
    rem = Agda.Builtin.Nat.mod-helper 0 n 2 n
{-# COMPILE AGDA2HS applicativeTree #-}


-- | 'replicateA' is an 'Applicative' version of 'replicate', and makes
-- \( O(\log n) \) calls to 'liftA2' and 'pure'.
replicateA : {a : Set} -> {{Applicative f}} -> Nat -> f a -> f (Seq a)
replicateA n x = Sequence <$> applicativeTree n 1 (Element <$> x)
{-# COMPILE AGDA2HS replicateA #-}

data Identity (a : Set) : Set where
  CIdentity : a -> Identity a
{-# COMPILE AGDA2HS Identity #-}

runIdentity : {a : Set} -> Identity a -> a
runIdentity (CIdentity a) = a
{-# COMPILE AGDA2HS runIdentity #-}

instance
  IdentityFunctor : Functor Identity
  IdentityFunctor .fmap f (CIdentity v) = CIdentity (f v)
{-# COMPILE AGDA2HS IdentityFunctor #-}

instance
  IdentityApplicative : Applicative Identity
  IdentityApplicative .pure = CIdentity
  IdentityApplicative ._<*>_ (CIdentity f) (CIdentity x) = CIdentity (f x)
{-# COMPILE AGDA2HS IdentityApplicative #-}

-- generates a sequence by replicating the given element
replicate : {a : Set} -> Nat -> a -> Seq a
replicate n x = runIdentity (replicateA n (CIdentity x))
{-# COMPILE AGDA2HS replicate #-}

-- needs to throw error for negative 
{-# TERMINATING #-}
cycleTaking : {a : Set} -> {{Sized a}} -> (n : Int) -> Seq a -> Seq a 
cycleTaking n xs = if n < (size xs) then xs >< (take n xs) else cycleTaking (n - size xs) (xs >< xs)
{-# COMPILE AGDA2HS cycleTaking #-}


reverseDigit : {a b : Set} -> (a -> b) -> Digit a -> Digit b
reverseDigit f (One a) = One (f a)
reverseDigit f (Two a b) = Two (f b) (f a)
reverseDigit f (Three a b c) = Three (f c) (f b) (f a)
reverseDigit f (Four a b c d) = Four (f d) (f c) (f b) (f a)
{-# COMPILE AGDA2HS reverseDigit #-}

reverseNode : {a b : Set} -> (a -> b) -> Node a -> Node b
reverseNode f (Node2 s a b) = Node2 s (f b) (f a)
reverseNode f (Node3 s a b c) = Node3 s (f c) (f b) (f a)
{-# COMPILE AGDA2HS reverseNode #-}

fmapReverseTree : {a b : Set} -> (a -> b) -> FingerTree a -> FingerTree b
fmapReverseTree _ EmptyT = EmptyT
fmapReverseTree f (Single x) = Single (f x)
fmapReverseTree f (Deep s pr m sf) =
    Deep s (reverseDigit f sf)
        (fmapReverseTree (reverseNode f) m)
        (reverseDigit f pr)
{-# COMPILE AGDA2HS fmapReverseTree #-}

-- Reverse a sequence while mapping over it.
fmapReverse : {a b : Set} -> (a -> b) -> Seq a -> Seq b
fmapReverse {a} {b} f (Sequence xs) = Sequence (fmapReverseTree (lift_elem f) xs)
  where
    lift_elem : {a b : Set} -> (a -> b) -> (Elem a -> Elem b)
    lift_elem g (Element a) = Element (g a)
{-# COMPILE AGDA2HS fmapReverse #-}

reverse : {a b : Set} -> Seq a -> Seq a
reverse (Sequence xs) = Sequence (fmapReverseTree id xs)
{-# COMPILE AGDA2HS reverse #-}


zipWithList' : {a b c : Set} -> (a -> b -> c) -> (xs : List a) -> (ys : List b) -> List c
zipWithList' f [] [] = []
zipWithList' f [] (y ∷ ys) = []
zipWithList' f (x ∷ xs) [] = []
zipWithList' f xs@(x ∷ xs') ys@(y ∷ ys') = f x y ∷ (zipWithList' f xs' ys')


-- | A version of zipWith that assumes the sequences have the same length.
zipWith' : {a b c : Set} -> (a -> b -> c) -> (xs : Seq a) -> (ys : Seq b) -> Seq c
zipWith' f xs ys = fromList (zipWithList' f (toList xs) (toList ys))


-- 'zipWith' generalizes 'zip' by zipping with the function given as the first argument, instead of a tupling function.
zipWith : {a b c : Set} -> (a -> b -> c) -> Seq a -> Seq b -> Seq c
zipWith f s1 s2 = zipWith' f s1' s2'
  where
    minLen = min (length s1) (length s2)
    s1' = take minLen s1
    s2' = take minLen s2
{-# COMPILE AGDA2HS zipWith #-}

-- 'zip' takes two sequences and returns a sequence of corresponding pairs.  If one input is short, excess elements are
-- discarded from the right end of the longer sequence.
zip : {a b : Set} -> Seq a -> Seq b -> Seq (a × b)
zip = zipWith (_,_)
{-# COMPILE AGDA2HS zip #-}


-- 'zipWith3' takes a function which combines three elements, as well as three sequences and returns a sequence of
-- their point-wise combinations, analogous to 'zipWith'.
zipWith3 : {a b c d : Set} -> (a -> b -> c -> d) -> Seq a -> Seq b -> Seq c -> Seq d
zipWith3 f s1 s2 s3 = zipWith' (_$_) (zipWith' f s1' s2') s3'
  where
    minLen = min (length s1) (min (length s2) (length s3))
    s1' = take minLen s1
    s2' = take minLen s2
    s3' = take minLen s3
{-# COMPILE AGDA2HS zipWith3 #-}

zipWith3' : {a b c d : Set} -> (a -> b -> c -> d) -> Seq a -> Seq b -> Seq c -> Seq d
zipWith3' f s1 s2 s3 = zipWith' (_$_) (zipWith' f s1 s2) s3
{-# COMPILE AGDA2HS zipWith3' #-}

-- 'zip3' takes three sequences and returns a sequence of triples, analogous to 'zip'.
zip3 : {a b c : Set} -> Seq a -> Seq b -> Seq c -> Seq (a × b × c)
zip3 = zipWith3 (_,_,_)
{-# COMPILE AGDA2HS zip3 #-}

pattern _,_,_,_ x y z w = x Tuple.∷ y Tuple.∷ z Tuple.∷ w Tuple.∷ []

_×_×_×_ : (a b c d : Set) -> Set
a × b × c × d = Tuple (a ∷ b ∷ c ∷ d ∷ [])

zipWith4 : {a b c d : Set} -> (a -> b -> c -> d -> e) -> Seq a -> Seq b -> Seq c -> Seq d -> Seq e
zipWith4 f s1 s2 s3 s4 = zipWith' (_$_) (zipWith3' f s1' s2' s3') s4'
  where
    minLen = min (length s1) (min (length s2) (min (length s3) (length s4)))
    s1' = take minLen s1
    s2' = take minLen s2
    s3' = take minLen s3
    s4' = take minLen s4
{-# COMPILE AGDA2HS zipWith4 #-}

zip4 : {a b c d : Set} -> Seq a -> Seq b -> Seq c -> Seq d -> Seq (_×_×_×_ a b c d)
zip4 = zipWith4 (_,_,_,_)
{-# COMPILE AGDA2HS zip4 #-}


record UnzipWith (f : Set -> Set) : Set₁ where
  field
    unzipWith' : {a b x : Set} -> (x -> (a × b)) -> f x -> (f a × f b)

open UnzipWith ⦃ ... ⦄ public
{-# COMPILE AGDA2HS UnzipWith #-}

instance
    NodeUnzipWith : UnzipWith Node
    NodeUnzipWith .unzipWith' f (Node2 s x y) = Node2 s (fst fx) (fst fy) , Node2 s (snd fx) (snd fy)
                                            where fx = f x
                                                  fy = f y
    NodeUnzipWith .unzipWith' f (Node3 s x y z) = Node3 s (fst fx) (fst fy) (fst fz) , Node3 s (snd fx) (snd fy) (snd fz)
                                            where fx = f x
                                                  fy = f y
                                                  fz = f z
{-# COMPILE AGDA2HS NodeUnzipWith #-}

instance
    DigitUnzipWith : UnzipWith Digit
    DigitUnzipWith .unzipWith' f (One x) = One (fst fx) , One (snd fx)
                                        where fx = f x
    DigitUnzipWith .unzipWith' f (Two x y) = Two (fst fx) (fst fy) , Two (snd fx) (snd fy)
                                        where fx = f x
                                              fy = f y
    DigitUnzipWith .unzipWith' f (Three x y z) = Three (fst fx) (fst fy) (fst fz) , Three (snd fx) (snd fy) (snd fz)
                                        where fx = f x
                                              fy = f y
                                              fz = f z 
    DigitUnzipWith .unzipWith' f (Four x y z w) = Four (fst fx) (fst fy) (fst fz) (fst fw) , Four (snd fx) (snd fy) (snd fz) (snd fw)
                                        where fx = f x
                                              fy = f y
                                              fz = f z
                                              fw = f w
{-# COMPILE AGDA2HS DigitUnzipWith #-}

instance
    FingerTreeUnzipWith : UnzipWith FingerTree
    FingerTreeUnzipWith .unzipWith' f EmptyT = EmptyT , EmptyT
    FingerTreeUnzipWith .unzipWith' f (Single x) = Single (fst fx) , Single (snd fx)
                                                where fx = f x
    FingerTreeUnzipWith .unzipWith' f (Deep v pr m sf) = (Deep v (fst prf) (fst mf) (fst sff)) , (Deep v (snd prf) (snd mf) (snd sff))
                                                    where prf = unzipWith' f pr
                                                          sff = unzipWith' f sf
                                                          mf = unzipWith' (unzipWith' f) m
{-# COMPILE AGDA2HS FingerTreeUnzipWith #-}


instance
    ElemUnzipWith : UnzipWith Elem
    ElemUnzipWith .unzipWith' f (Element x) = Element (fst fx) , Element (snd fx)
                                where fx = f x

unzipWithNodeElem : {x a b : Set} -> (x -> a × b) -> Node (Elem x) -> Node (Elem a) × Node (Elem b)
unzipWithNodeElem f (Node2 s (Element x) (Element y)) = Node2 s (Element (fst fx)) (Element (fst fy)) , Node2 s (Element (snd fx)) (Element (snd fy))
                                                    where fx = f x
                                                          fy = f y
unzipWithNodeElem f (Node3 s (Element x) (Element y) (Element z)) = Node3 s (Element (fst fx)) (Element (fst fy)) (Element (fst fz)) , Node3 s (Element (snd fx)) (Element (snd fy)) (Element (snd fz))
                                                                where fx = f x
                                                                      fy = f y
                                                                      fz = f z
{-# COMPILE AGDA2HS ElemUnzipWith #-}

instance
    SeqUnzipWith : UnzipWith Seq
    SeqUnzipWith .unzipWith' f (Sequence EmptyT) = (Sequence EmptyT) , (Sequence EmptyT)
    SeqUnzipWith .unzipWith' f (Sequence (Single (Element x))) = (Sequence (Single (Element (fst fx)))) , (Sequence (Single (Element (snd fx))))
                                                            where fx = f x
    SeqUnzipWith .unzipWith' f (Sequence (Deep v pr m sf)) = Sequence (Deep v (fst prf) (fst mf) (fst sff)) , Sequence (Deep v (snd prf) (snd mf) (snd sff))
                                                        where prf = unzipWith' (unzipWith' f) pr
                                                              sff = unzipWith' (unzipWith' f) sf
                                                              mf = unzipWith' (unzipWithNodeElem f) m
{-# COMPILE AGDA2HS SeqUnzipWith #-}

-- Unzip a sequence using a function to divide elements.
unzipWith : {a b c : Set} -> (a -> b × c) -> Seq a -> Seq b × Seq c
unzipWith = unzipWith'
{-# COMPILE AGDA2HS unzipWith #-}

unzip : {a b : Set} -> Seq (a × b) -> Seq a × Seq b
unzip xs = unzipWith id xs
{-# COMPILE AGDA2HS unzip #-}