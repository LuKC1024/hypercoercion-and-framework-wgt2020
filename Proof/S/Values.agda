open import Types

module S.Values
  (Label : Set)
  (Cast : Type → Type → Set)
  where
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label
open import Variables

mutual
  
  data Val : Type → Set where
    inj : ∀ P → Val (` P) → Val ⋆
    fun : ∀ {Γ}
      → {T1 T2 T3 T4 : Type}
      → (env : Env Γ)
      → (c₁ : Cast T3 T1)
      → (b : (Γ , T1) ⊢ T2)
      → (c₂ : Cast T2 T4)
      -------------
      → Val (` T3 ⇒ T4)

    sole :
      --------
        Val (` U)

    cons : ∀ {T1 T2 T3 T4}
      → Val T1
      → (c₁ : Cast T1 T3)
      → Val T2
      → (c₂ : Cast T2 T4)
      ---------
      → Val (` T3 ⊗ T4)

    inl : ∀ {T T1 T2}
      → Val T
      → (c : Cast T T1)
      --------
      → Val (` T1 ⊕ T2)
      
    inr : ∀ {T T1 T2}
      → Val T
      → (c : Cast T T2)
      --------
      → Val (` T1 ⊕ T2)

  data Env : Context → Set where
    []  : Env ∅
    _∷_ : ∀ {Γ T}
      → (v : Val T)
      → Env Γ
      → Env (Γ , T)
   
_[_] : ∀ {Γ T} → Env Γ → Γ ∋ T → Val T
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

data CastResult (T : Type) : Set where
  succ : (v : Val T) → CastResult T
  fail : (l : Label) → CastResult T

_>>=_ : ∀ {T1 T2} → CastResult T1 → (Val T1 → CastResult T2) → CastResult T2
succ v >>= f = f v
fail l >>= f = fail l

>>=-succ : ∀ {T} → (R : CastResult T) → (R >>= succ) ≡ R
>>=-succ (succ v) = refl
>>=-succ (fail l) = refl
