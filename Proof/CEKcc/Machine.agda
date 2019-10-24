open import Types
open import CEKcc.CastRep

module CEKcc.Machine
  (Label : Set)
  (cast-rep : CastRep Label)
  where

open CastRep cast-rep using (Cast; mk-cast; mk-id; mk-seq; apply-cast)

open import Variables
open import Terms Label
open import Observe Label
open import CEKcc.Values Label Cast


mutual
      
  data Cont (T1 T3 : Type) : Set where
    cont : ∀ {T2}
      → (fst : Cast T1 T2)
      → (snd : PreCont T2 T3)
      ---
      → Cont T1 T3

  data PreCont : Type → Type → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    mt : ∀ {Z}
      ----------
      → PreCont Z Z

    cons₁ : ∀ {Γ T1 T2 Z}
      → (E : Env Γ)
      → (e1 : Γ ⊢ T2)
      → (κ : Cont (` T1 ⊗ T2) Z)
      --------
      → PreCont T1 Z
      
    cons₂ : ∀ {T1 T2 Z}
      → (v1 : Val T1)
      → (κ : Cont (` T1 ⊗ T2) Z)
      --------
      → PreCont T2 Z

    inl :  ∀ {T1 T2 Z}
      → (κ : Cont (` T1 ⊕ T2) Z)
      --------
      → PreCont T1 Z

    inr :  ∀ {T1 T2 Z}
      → (κ : Cont (` T1 ⊕ T2) Z)
      --------
      → PreCont T2 Z
           
    app₁ : ∀ {Γ T1 T2 Z}
      → (E : Env Γ)
      → (e2 : Γ ⊢ T1)
      → (κ : Cont T2 Z)
      --------
      → PreCont (` T1 ⇒ T2) Z

    app₂ : ∀ {T1 T2 Z}
      → (v1 : Val (` T1 ⇒ T2))
      → (κ : Cont T2 Z)
      --------
      → PreCont T1 Z

    car : ∀ {T1 T2 Z}
      → (κ : Cont T1 Z)
      -----------
      → PreCont (` T1 ⊗ T2) Z
      
    cdr : ∀ {T1 T2 Z}
      → (κ : Cont T2 Z)
      -----------
      → PreCont (` T1 ⊗ T2) Z

    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → (E : Env Γ)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → (κ : Cont T3 Z)
      --------
      → PreCont (` T1 ⊕ T2) Z
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → (E : Env Γ)
      → (v1 : Val (` T1 ⊕ T2))
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → (κ : Cont T3 Z)
      --------
      → PreCont (` T1 ⇒ T3) Z
      
    case₃ : ∀ {T1 T2 T3 Z}
      → (v1 : Val (` T1 ⊕ T2))
      → (v2 : Val (` T1 ⇒ T3))
      → (κ : Cont T3 Z)
      ----------------
      → PreCont (` T2 ⇒ T3) Z

mk-cont : ∀ {T1 T2} → PreCont T1 T2 → Cont T1 T2
mk-cont κ = cont (mk-id _) κ

ext-cont : ∀ {T1 T2 T3} → Cast T1 T2 → Cont T2 T3 → Cont T1 T3
ext-cont c (cont fst snd) = cont (mk-seq c fst) snd

data State : Type → Set where 
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → (E : Env Γ)
    → (κ : Cont T1 T3)
    ------------
    → State T3
    
  return : ∀ {T1 T2}
    → (v : Val T1)
    → (κ : Cont T1 T2)
    ------------
    → State T2

  halt : ∀ {T}
    → Observe T
    → State T

load : ∀ {T} → ∅ ⊢ T → State T
load e = inspect e [] (mk-cont mt)

do-app : ∀ {T1 T2 Z}
  → Val (` T1 ⇒ T2)
  → Val T1
  → Cont T2 Z
  → State Z
do-app (fun env c₁ b c₂) rand κ with apply-cast c₁ rand
do-app (fun env c₁ b c₂) rand κ | succ v
  = inspect b (v ∷ env) (ext-cont c₂ κ)
do-app (fun env c₁ b c₂) rand κ | fail l
  = halt (blame l)

do-car : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T1 Z
  → State Z
do-car (cons v₁ c₁ v₂ c₂) κ = return v₁ (ext-cont c₁ κ)

do-cdr : ∀ {T1 T2 Z}
  → Val (` T1 ⊗ T2)
  → Cont T2 Z
  → State Z
do-cdr (cons v₁ c₁ v₂ c₂) κ = return v₂ (ext-cont c₂ κ)

do-case : ∀ {T1 T2 T3 Z}
  → Val (` T1 ⊕ T2)
  → Val (` T1 ⇒ T3)
  → Val (` T2 ⇒ T3)
  → Cont T3 Z
  → State Z
do-case (inl v1 c) (fun env c₁ b c₂) v3 k = return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))
do-case (inr v1 c) v2 (fun env c₁ b c₂) k = return v1 (mk-cont (app₂ (fun env (mk-seq c c₁) b c₂) k))

observe-val : ∀ {T} → Val T → Value T
observe-val (inj P v) = inj
observe-val (fun env c₁ b c₂) = fun
observe-val sole = sole
observe-val (cons v c₁ v₁ c₂) = cons
observe-val (inl v c) = inl
observe-val (inr v c) = inr

progress-return : ∀ {T Z}
  → Val T
  → PreCont T Z
  ---
  → State Z
progress-return v mt = halt (done (observe-val v))
progress-return v (cons₁ E e1 κ) = inspect e1 E (mk-cont (cons₂ v κ))
progress-return v (cons₂ {T1} {T2} v1 κ) = return (cons v1 (mk-id T1) v (mk-id T2)) κ
progress-return v (inl κ) = return (inl v (mk-id _)) κ
progress-return v (inr κ) = return (inr v (mk-id _)) κ
progress-return v (app₁ E e2 κ) = inspect e2 E (mk-cont (app₂ v κ))
progress-return v (app₂ v₁ κ) = do-app v₁ v κ
progress-return v (car κ) = do-car v κ
progress-return v (cdr κ) = do-cdr v κ
progress-return v (case₁ E e2 e3 κ) = inspect e2 E (mk-cont (case₂ E v e3 κ))
progress-return v (case₂ E v1 e3 κ) = inspect e3 E (mk-cont (case₃ v1 v κ))
progress-return v (case₃ v1 v2 κ) = do-case v1 v2 v κ

progress : {T : Type} → State T → State T
progress (inspect sole E κ) = return sole κ
progress (inspect (var X) E κ) = return (E [ X ]) κ
progress (inspect (lam T1 T2 e) E κ) = return (fun E (mk-id T1) e (mk-id T2)) κ
progress (inspect (cons e1 e2) E κ) = inspect e1 E (mk-cont (cons₁ E e2 κ))
progress (inspect (inl e) E κ) = inspect e E (mk-cont (inl κ))
progress (inspect (inr e) E κ) = inspect e E (mk-cont (inr κ))
progress (inspect (app e1 e2) E κ) = inspect e1 E (mk-cont (app₁ E e2 κ))
progress (inspect (car e) E κ) = inspect e E (mk-cont (car κ))
progress (inspect (cdr e) E κ) = inspect e E (mk-cont (cdr κ))
progress (inspect (case e1 e2 e3) E κ) = inspect e1 E (mk-cont (case₁ E e2 e3 κ))
progress (inspect (cast l T1 T2 e) E κ) = inspect e E (ext-cont (mk-cast l T1 T2) κ)
progress (inspect (blame l) E κ) = halt (blame l)
progress (return v (cont fst snd)) with apply-cast fst v
progress (return v (cont fst snd)) | succ u = progress-return u snd
progress (return v (cont fst snd)) | fail l = halt (blame l)
progress (halt obs) = halt obs

open import Utilities

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ-syntax)

record Evalo {T : Type} (e : ∅ ⊢ T) (o : Observe T) : Set where
  constructor evalo
  field
    n : ℕ
    prf : repeat n progress (load e) ≡ halt o
