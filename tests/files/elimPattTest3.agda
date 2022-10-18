open import Agda.Builtin.Equality
open import elimPattPrelude
open import Agda.Builtin.Unit


data Test (A B : Set) (a : A) : Set where
  c : (m n : A) -> A -> (n ≡ m -> Test A B a) -> Test A B a
  d : (f : A -> A -> A) -> (A -> Test A B a) -> Test A B a
  e : (f : (a' : A) -> a ≡ a' -> Test A B a) -> Test A B a


data Test2 (A B : Set) (a : A) : Set where
  kc : (A -> Test2 A B a) -> (m n : A) -> A -> (n ≡ m -> Test2 A B a) -> Test2 A B a


data W (A : Set) (B : A -> Set) : Set where
  sup : (a : A) -> (f : B a -> W A B) -> W A B
