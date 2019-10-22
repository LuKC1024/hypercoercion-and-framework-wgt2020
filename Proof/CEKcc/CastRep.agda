module CEKcc.CastRep
  (Label : Set)
  where

open import Types
open import Variables
open import Terms Label
open import CEKcc.Values Label

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Relation.Nullary using (Dec; yes; no; ¬_)

record CastRep : Set₁ where
  field
    Cast : Type → Type → Set

    mk-cast : Label → (T1 T2 : Type) → Cast T1 T2
    mk-id : (T : Type) → Cast T T
    mk-seq : ∀ {T1 T2 T3}
      → Cast T1 T2
      → Cast T2 T3
      -----
      → Cast T1 T3
    apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val Cast T1 → CastResult Cast T2

-- only required for the bisim between D and S(C)
record CastIdIsId (CR : CastRep) : Set where
  open CastRep CR
  field
    lem-cast-id-is-id : ∀ l T →
      mk-cast l T T ≡ mk-id T

record Monoid (CR : CastRep) : Set where
  open CastRep CR
  field
    lem-id-l : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → mk-seq (mk-id T1) c ≡ c
    lem-id-r : ∀ {T1 T2}
      → (c : Cast T1 T2)
      ---
      → mk-seq c (mk-id T2) ≡ c
    lem-assoc : ∀ {T1 T2 T3 T4}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → (c3 : Cast T3 T4)
      ---
      → mk-seq (mk-seq c1 c2) c3 ≡ mk-seq c1 (mk-seq c2 c3)

record SurelyLazyD (CR : CastRep) : Set where
  open CastRep CR
  field
    lem-id : ∀ T
      → (v : Val Cast T)  
      -----------------------------
      → apply-cast (mk-id T) v ≡ succ v

    lem-seq : ∀ {T1 T2 T3}
      → (c1 : Cast T1 T2)
      → (c2 : Cast T2 T3)
      → (v : Val Cast T1)
      --------------------
      → apply-cast (mk-seq c1 c2) v ≡ (_>>=_ Cast (apply-cast c1 v) (λ u → apply-cast c2 u))
    lem-cast-¬⌣ : ∀ {T1 T2}
      → (l : Label)
      → ¬ (T1 ⌣ T2)
      → (v : Val Cast T1)
      ---
      → apply-cast (mk-cast l T1 T2) v ≡ fail l

    lem-cast-id⋆ : ∀ l
      → (v : Val Cast ⋆)
      → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v

    lem-cast-inj : ∀ {P}
      → (l : Label)
      → (v : Val Cast (` P))  
      → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
      
    lem-cast-proj : ∀ l P P₁ v
      → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v

    lem-cast-U : ∀ l
      → apply-cast (mk-cast l (` U) (` U)) sole ≡ succ sole

    lem-cast-⇒ : ∀ T11 T12 T21 T22
      → ∀ {S T}
      → (l : Label)
      → {Γ : Context}
      → (E : Env Cast Γ)
      → (c₁ : Cast T11 S)
      → (b : (Γ , S) ⊢ T)
      → (c₂ : Cast T T12)
      → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (fun E c₁ b c₂) ≡
        succ (fun E (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))

    lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
      → (l : Label)
      → (v₁ : Val Cast T01)
      → (v₂ : Val Cast T02)
      → (c₁ : Cast T01 T11)
      → (c₂ : Cast T02 T12)
      → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
        succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))

    lem-cast-⊕-l : ∀ T T11 T12 T21 T22
      → (l : Label)
      → (v : Val Cast T)
      → (c : Cast T T11)
      → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
        succ (inl v (mk-seq c (mk-cast l T11 T21)))

    lem-cast-⊕-r : ∀ T T11 T12 T21 T22
      → (l : Label)
      → (v : Val Cast T)
      → (c : Cast T T12)
      → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
        succ (inr v (mk-seq c (mk-cast l T12 T22)))

