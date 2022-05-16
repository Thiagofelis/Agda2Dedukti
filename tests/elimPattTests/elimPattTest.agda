open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Test (A B : Set) (a : A) : Set where
  c : (m n : Nat) -> A -> (n ≡ m -> Test A B a) -> Test A B a
  d : (f : Nat -> A -> Nat) -> (A -> Test A B a) -> Test A B a
  e : (f : (a' : A) -> a ≡ a' -> Test A B a) -> Test A B a


someIsZero : Nat -> Nat -> Nat -> Nat
someIsZero (suc x) y z = suc x
someIsZero zero (suc y) z = suc y
someIsZero zero zero (suc z) = suc z
someIsZero zero zero zero = zero


test : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> x ≡ x
test _ (c m _ _ _) _ _ _ _ _ = refl
test _ (d _ _) _ _ _ _ _ = refl
test _ (e _) _ _ _ _ _ = refl


test2 : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> x ≡ x
test2 _ (c m _ _ _) _ _ _ _ _ = refl
test2 _ _ _ x _ _ _ = refl


{-
test : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> Nat
test _ (c m _ _ _) _ _ _ _ _ = m
test _ _ _ x _ _ _ = x
-}

{-

Γ, args : ϕ, Δ{c args / x} ⊢ ? : A{c args / x}



-}
