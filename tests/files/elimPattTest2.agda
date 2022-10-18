open import Agda.Builtin.Equality
open import elimPattPrelude
open import Agda.Builtin.Unit

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat


data Test (A B : Set) (a : A) : Set where
  c : (m n : Nat) -> A -> (n ≡ m -> Test A B a) -> Test A B a
  d : (f : Nat -> A -> Nat) -> (A -> Test A B a) -> Test A B a
  e : (f : (a' : A) -> a ≡ a' -> Test A B a) -> Test A B a


data Test2 (A B : Set) (a : A) : Set where
  kc : (A -> Test2 A B a) -> (m n : Nat) -> A -> (n ≡ m -> Test2 A B a) -> Test2 A B a

test : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> x ≡ x
test _ (c m _ _ l) _ _ _ _ p = refl
test _ _ _ _ (c m _ _ l) _ p = refl
test _ _ _ _ _ _ _ = refl


someIsZero : Nat -> Nat -> Nat -> Nat
someIsZero (suc x) y z = suc x
someIsZero zero (suc y) z = suc y
someIsZero zero zero (suc z) = suc z
someIsZero zero zero zero = zero

jesper : Nat -> Nat
jesper zero = suc zero
jesper (suc zero) = zero
jesper (suc (suc _)) = suc zero


test2 : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> x ≡ x
test2 _ (c m _ _ _) _ _ _ _ _ = refl
test2 _ _ _ x _ _ _ = refl



_+_ : Nat -> Nat -> Nat
zero + y = y
(suc x) + y = suc (x + y)


cong : {A B : Set} -> {a a' : A} -> (f : A -> B) -> a ≡ a' -> f a ≡ f a'
cong _ refl = refl


+-assoc : (n m k : Nat) -> n + (m + k) ≡ (n + m) + k
+-assoc zero _ _ = refl
+-assoc (suc n) m k = cong suc (+-assoc n m k)
{-
data _×_ (A B : Set) : Set where
  mkProd : A -> B -> A × B

BellowNat : (P : Nat -> Set) -> Nat -> Set
BellowNat _ zero = ⊤
BellowNat P (suc n) = (BellowNat P n) × (P n)

π-1 : {A B : Set} -> A × B -> A
π-1 (mkProd a b) = a

π-2 : {A B : Set} -> A × B -> B
π-2 (mkProd a b) = b


data _<_ (n : Nat) : Nat -> Set where
  dir : n < suc n
  comp : (m : Nat) -> n < m -> n < suc m

π : {P : Nat -> Set} -> (y x : Nat) -> y < x -> BellowNat P x -> P y
π y .(suc y) dir b = π-2 b
π y .(suc m) (comp m p) b = π y m p (π-1 b)

bellowNat : (P : Nat -> Set) -> (p : (x : Nat) -> BellowNat P x -> P x) -> (x : Nat) -> BellowNat P x
bellowNat P p zero = record {}
bellowNat P p (suc x) = mkProd (bellowNat P p x) (p x (bellowNat P p x))

recNat : (P : Nat -> Set) -> (p : (x : Nat) -> BellowNat P x -> P x) -> (x : Nat) -> P x
recNat P p x = p x (bellowNat P p x)

-}
{-
test : ∀ {A B a} -> A -> (x : Test A B a) -> x ≡ x -> Nat -> (y : Test A B a) -> x ≡ y -> a ≡ a -> Nat
test _ (c m _ _ _) _ _ _ _ _ = m
test _ _ _ x _ _ _ = x
-}

{-

Γ, args : ϕ, Δ{c args / x} ⊢ ? : A{c args / x}



-}
