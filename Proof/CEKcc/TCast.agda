module CEKcc.TCast
  (Label : Set)
  where

open import Types
open import CEKcc.CastRep Label

open import Relation.Nullary using (Dec; yes; no)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)

-- Type-based Cast

data Cast (T1 : Type) : Type → Set where
  id : Cast T1 T1
  cast : (l : Label)(T2 : Type) → Cast T1 T2
  seq : ∀ {T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3

open import Terms Label
open import CEKcc.Values Label Cast
open import Variables

mk-id : ∀ T → Cast T T
mk-id T = id

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = cast l T2

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 c2

do-cast : Label → (T1 T2 : Type) → Val T1 → CastResult T2
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆ = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P) = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P) = succ (inj P v)
do-cast l .(` U) .(` U) v | yes ⌣U = succ v
do-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) (fun env c₁ b c₂) | yes ⌣⇒ =
  succ (fun env (seq (mk-cast l T21 T11) c₁) b (seq c₂ (mk-cast l T12 T22)))
do-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) (cons v₁ c₁ v₂ c₂) | yes ⌣⊗ =
  succ (cons v₁ (seq c₁ (mk-cast l T11 T21)) v₂ ((seq c₂ (mk-cast l T12 T22))))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inl v c) | yes ⌣⊕ =
  succ (inl v (seq c (mk-cast l T11 T21)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inr v c) | yes ⌣⊕ =
  succ (inr v (seq c (mk-cast l T12 T22)))
do-cast l T1 T2 v | no ¬p = fail l

apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
apply-cast id v = succ v
apply-cast (cast l T2) v = do-cast l _ T2 v
apply-cast (seq c c₁) v =
  apply-cast c v >>= λ u →
  apply-cast c₁ u


open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

lem-id : ∀ T
  → (v : Val T)  
  -----------------------------
  → apply-cast (mk-id T) v ≡ succ v
lem-id T v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq c1 c2 v = refl

lem-cast-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Val T1)
  → apply-cast (mk-cast l T1 T2) v ≡ fail l
lem-cast-¬⌣ {T1} {T2} l p v with T1 ⌣? T2
lem-cast-¬⌣ {T1} {T2} l p v | yes p₁ = ⊥-elim (p p₁)
lem-cast-¬⌣ {T1} {T2} l p v | no ¬p = refl

lem-cast-id⋆ : ∀ l
  → (v : Val ⋆)
  → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
lem-cast-id⋆ l v = refl

lem-cast-inj : ∀ {P}
  → (l : Label)
  → (v : Val (` P))  
  → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
lem-cast-inj {P} l v = refl

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v = refl

lem-cast-U : ∀ l
  → apply-cast (mk-cast l (` U) (` U)) sole ≡ succ sole
lem-cast-U l = refl

lem-cast-⇒ : ∀ T11 T12 T21 T22
  → ∀ {S T}
  → (l : Label)
  → {Γ : Context}
  → (E : Env Γ)
  → (c₁ : Cast T11 S)
  → (b : (Γ , S) ⊢ T)
  → (c₂ : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22))) (fun E c₁ b c₂) ≡
    succ (fun E (mk-seq (mk-cast l T21 T11) c₁) b (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⇒ T11 T12 T21 T22 l E c₁ b c₂ = refl

lem-cast-⊗ : ∀ T01 T02 T11 T12 T21 T22
  → (l : Label)
  → (v₁ : Val T01)
  → (v₂ : Val T02)
  → (c₁ : Cast T01 T11)
  → (c₂ : Cast T02 T12)
  → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v₁ c₁ v₂ c₂) ≡
    succ (cons v₁ (mk-seq c₁ (mk-cast l T11 T21)) v₂ (mk-seq c₂ (mk-cast l T12 T22)))
lem-cast-⊗ T01 T02 T11 T12 T21 T22 l v₁ v₂ c₁ c₂ = refl
    
lem-cast-⊕-l : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v c) ≡
    succ (inl v (mk-seq c (mk-cast l T11 T21)))
lem-cast-⊕-l T T11 T12 T21 T22 l v c = refl

lem-cast-⊕-r : ∀ T T11 T12 T21 T22
  → (l : Label)
  → (v : Val T)
  → (c : Cast T T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v c) ≡
    succ (inr v (mk-seq c (mk-cast l T12 T22)))
lem-cast-⊕-r T T11 T12 T21 T22 l v c = refl

cast-rep : CastRep
cast-rep
  = record
    { Cast = Cast
    ; mk-cast = mk-cast
    ; mk-seq = mk-seq
    ; mk-id = mk-id
    ; apply-cast = apply-cast
    }
cast-rep-surely-lazyD : SurelyLazyD cast-rep
cast-rep-surely-lazyD
  = record
    { lem-id = lem-id
    ; lem-seq = lem-seq
    ; lem-cast-¬⌣ = lem-cast-¬⌣
    ; lem-cast-id⋆ = lem-cast-id⋆
    ; lem-cast-inj = lem-cast-inj
    ; lem-cast-proj = lem-cast-proj
    ; lem-cast-U = lem-cast-U
    ; lem-cast-⇒ = lem-cast-⇒
    ; lem-cast-⊗ = lem-cast-⊗
    ; lem-cast-⊕-l = lem-cast-⊕-l
    ; lem-cast-⊕-r = lem-cast-⊕-r
    }
