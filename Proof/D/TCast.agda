module D.TCast
  (Label : Set)
  where

open import Types

data Cast : Type → Type → Set where
  cast : (l : Label)(T1 T2 : Type) → Cast T1 T2

open import Statics Label
open import D.Values Label Cast

open import Relation.Nullary using (Dec; yes; no)

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = cast l T1 T2

apply-cast' : Label → (T1 T2 : Type) → Val T1 → CastResult T2
apply-cast' l T1 T2 v with T1 ⌣? T2
apply-cast' l T1 T2 v | yes p with T1
apply-cast' l T1 _  v | yes ⋆⌣⋆ | ⋆ = succ v
apply-cast' l T1 _ (cast v (P⌣⋆ P₁) c) | yes (⋆⌣P P) | ⋆ = apply-cast' l (` P₁) (` P) v 
apply-cast' l T1 T2 v | yes p | ` P = succ (cast v p (cast l (` P) T2))
apply-cast' l T1 T2 v | no ¬p = fail l

apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
apply-cast (cast l T1 T2) v = apply-cast' l T1 T2 v

cast-dom : ∀ {T1 T2 T3 T4} → Cast (` T1 ⇒ T2) (` T3 ⇒ T4) → Cast T3 T1
cast-dom (cast l (` T1 ⇒ T2) (` T3 ⇒ T4)) = cast l T3 T1 

cast-cod : ∀ {T1 T2 T3 T4} → Cast (` T1 ⇒ T2) (` T3 ⇒ T4) → Cast T2 T4
cast-cod (cast l (` T1 ⇒ T2) (` T3 ⇒ T4)) = cast l T2 T4

cast-car : ∀ {T1 T2 T3 T4} → Cast (` T1 ⊗ T2) (` T3 ⊗ T4) → Cast T1 T3
cast-car (cast l (` T1 ⊗ T2) (` T3 ⊗ T4)) = cast l T1 T3

cast-cdr : ∀ {T1 T2 T3 T4} → Cast (` T1 ⊗ T2) (` T3 ⊗ T4) → Cast T2 T4
cast-cdr (cast l (` T1 ⊗ T2) (` T3 ⊗ T4)) = cast l T2 T4

cast-inl : ∀ {T1 T2 T3 T4} → Cast (` T1 ⊕ T2) (` T3 ⊕ T4) → Cast T1 T3
cast-inl (cast l (` T1 ⊕ T2) (` T3 ⊕ T4)) = cast l T1 T3

cast-inr : ∀ {T1 T2 T3 T4} → Cast (` T1 ⊕ T2) (` T3 ⊕ T4) → Cast T2 T4
cast-inr (cast l (` T1 ⊕ T2) (` T3 ⊕ T4)) = cast l T2 T4
