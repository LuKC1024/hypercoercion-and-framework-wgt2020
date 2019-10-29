open import Types

module D.Values
  (Label : Set)
  (Cast : Type → Type → Set)
  where
  
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Terms Label
open import Variables

mutual
  
  data Val : Type → Set where
    cast : ∀ {P1 T1}
      → (v : Val (` P1))
      → (p : (` P1) ⌣ T1)
      → (c : Cast (` P1) T1)
      → Val T1
    
    fun : ∀ {Γ}
      → {T1 T2 : Type}
      → (env : Env Γ)
      → (b : (Γ , T1) ⊢ T2)
      -------------
      → Val (` T1 ⇒ T2)

    sole :
      --------
        Val (` U)

    cons : ∀ {T1 T2}
      → Val T1
      → Val T2
      ---------
      → Val (` T1 ⊗ T2)

    inl : ∀ {T1 T2}
      → Val T1
      --------
      → Val (` T1 ⊕ T2)
      
    inr : ∀ {T1 T2}
      → Val T2
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
