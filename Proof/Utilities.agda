module Utilities where
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- repeat : {A : Set}
--   → ℕ
--   → (A → A)
--   → A
--   ---
--   → A
-- repeat zero f x = x
-- repeat (suc n) f x = f (repeat n f x)

-- thm-repeat : ∀ {A}
--   → (n m : ℕ)
--   → (f : A → A)
--   → (z : A)
--   ---
--   → repeat n f (repeat m f z) ≡ repeat (n + m) f z
-- thm-repeat zero m f z = refl
-- thm-repeat (suc n) m f z rewrite thm-repeat n m f z = refl

repeat : {A : Set}
  → ℕ
  → (A → A)
  → A
  ---
  → A
repeat zero f x = x
repeat (suc n) f x = repeat n f (f x)

lem-repeat : ∀ {A}
  → (n : ℕ)
  → (f : A → A)
  → (z : A)
  ---
  → repeat n f (f z) ≡ f (repeat n f z)
lem-repeat zero f z = refl
lem-repeat (suc n) f z = lem-repeat n f (f z)

thm-repeat : ∀ {A}
  → (n m : ℕ)
  → (f : A → A)
  → (z : A)
  ---
  → repeat n f (repeat m f z) ≡ repeat (n + m) f z
thm-repeat zero m f z = refl
thm-repeat (suc n) m f z
  rewrite lem-repeat n f (repeat m f z)
        | lem-repeat (n + m) f z
        | thm-repeat n m f z
  = refl
