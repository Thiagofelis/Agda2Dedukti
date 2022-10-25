open import Agda.Builtin.Sigma

∧ : ∀ {a b} (A : Set a) (B : Set b) → Set (a Agda.Primitive.⊔ b)
∧ A B = Σ A (\_ -> B)

record UUnit (i : Agda.Primitive.Level) : Set i where
  constructor tt

ttt : (i : Agda.Primitive.Level) → UUnit i
ttt i = tt {i}
