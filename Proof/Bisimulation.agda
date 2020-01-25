open import S.CastADT

module Bisimulation
  (Label : Set)
  (LCR : CastADT Label)
  (LCM : Monoid Label LCR)
  (LCS : LazyD Label LCR)
  (Extras : CastIdIsId Label LCR)
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; suc; zero; _+_)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax; _,_)
open import Data.Sum using (_⊎_ ; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Types
open import Statics Label
open import Observables Label

import S.Machine
import S.Values
import D.Machine
import D.Values

-- instantiate CEKcc

module L where
  open CastADT LCR public
  open LazyD LCS public
  open Monoid LCM
    renaming (lem-id-l to monoid-id-l; lem-id-r to monoid-id-r; lem-assoc to monoid-assoc)
    public
  open CastIdIsId Extras public
  open S.Values Label Cast public
  open S.Machine Label LCR public

-- instantiate CEKc

module R where
  open import D.TCast Label public
  open import D.Values Label Cast public
  open import D.Machine Label public

mutual

  data EnvRelate : ∀ {Γ} → L.Env Γ → R.Env Γ → Set where
    []  : EnvRelate L.[] R.[]
    _∷_ : ∀ {Γ T}
      → {v : L.Val T}{u : R.Val T}
      → ValRelate v u
      → {E : L.Env Γ}{F : R.Env Γ}
      → EnvRelate E F
      → EnvRelate (L._∷_ v E) (R._∷_ u F)

  data ValRelate : ∀ {T} → L.Val T → R.Val T → Set where
    inj : ∀ {l}
      → (P : PreType)
      → {v : L.Val (` P)}
      → {u : R.Val (` P)}
      → ValRelate v u
      ----------------
      → ValRelate (L.inj _ v) (R.cast u (P⌣⋆ P) (R.mk-cast l (` P) ⋆))
      
    fun : ∀ {Γ T1 T2}
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      → (b : (Γ , T1) ⊢ T2)
      ----
      → ValRelate (L.fun lE (L.mk-id T1) b (L.mk-id T2)) (R.fun rE b)
      
    cast-fun : ∀ {Γ T1 T2}
      → ∀ l T3 T4 T5 T6
      → (E : L.Env Γ)
      → (c1 : L.Cast T3 T1)
      → (b  : (Γ , T1) ⊢ T2)
      → (c2 : L.Cast T2 T4)
      → {g : R.Val (` T3 ⇒ T4)}
      → ValRelate (L.fun E c1 b c2) g
      ---
      → ValRelate (L.fun E (L.mk-seq (L.mk-cast l T5 T3) c1) b (L.mk-seq c2 (L.mk-cast l T4 T6)))
                  (R.cast g ⌣⇒ (R.mk-cast l (` T3 ⇒ T4) (` T5 ⇒ T6)))      
    sole :
      --------
        ValRelate L.sole R.sole

    cast-sole : ∀ {l}
      → {rv : R.Val (` U)}
      -------
      → ValRelate L.sole (R.cast rv ⌣U (R.mk-cast l (` U) (` U)))

    cons : ∀ {T1 T2}
      → {v1 : L.Val T1}
      → {u1 : R.Val T1}
      → ValRelate v1 u1
      → {v2 : L.Val T2}
      → {u2 : R.Val T2}
      → ValRelate v2 u2
      ------------------
      → ValRelate (L.cons v1 (L.mk-id T1) v2 (L.mk-id T2)) (R.cons u1 u2)

    cast-cons : ∀ {T1 T2}
      → (l : Label)
      → ∀ T3 T4 T5 T6
      → (v1 : L.Val T1)
      → (c1 : L.Cast T1 T3)
      → (v2 : L.Val T2)
      → (c2 : L.Cast T2 T4)
      → {u : R.Val (` T3 ⊗ T4)}
      → ValRelate (L.cons v1 c1 v2 c2) u
      ------------------
      → ValRelate (L.cons v1 (L.mk-seq c1 (L.mk-cast l T3 T5))
                          v2 (L.mk-seq c2 (L.mk-cast l T4 T6)))
                  (R.cast u ⌣⊗ (R.mk-cast l (` T3 ⊗ T4) (` T5 ⊗ T6)))
      
    inl : ∀ {T1 T2}
      → {lv : L.Val T1}
      → {rv : R.Val T1}
      → ValRelate lv rv
      -----------------
      → ValRelate (L.inl {T2 = T2} lv (L.mk-id T1)) (R.inl rv)

    cast-inl : ∀ {T1 T3 T4 T5 T6}
      → (lv : L.Val T1)
      → (lc : L.Cast T1 T3)
      → {rv : R.Val (` T3 ⊕ T4)}
      → ValRelate (L.inl lv lc) rv
      → (l : Label)
      -----------------
      → ValRelate (L.inl lv (L.mk-seq lc (L.mk-cast l T3 T5)))
                  (R.cast rv ⌣⊕ (R.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
      
    inr : ∀ {T1 T2}
      → {lv : L.Val T2}
      → {rv : R.Val T2}
      → ValRelate lv rv
      -----------------
      → ValRelate (L.inr {T1 = T1} lv (L.mk-id T2)) (R.inr rv)

    cast-inr : ∀ {T2 T3 T4 T5 T6}
      → (lv : L.Val T2)
      → (lc : L.Cast T2 T4)
      → {rv : R.Val (` T3 ⊕ T4)}
      → ValRelate (L.inr lv lc) rv
      → (l : Label)
      -----------------
      → ValRelate (L.inr lv (L.mk-seq lc (L.mk-cast l T4 T6)))
                  (R.cast rv ⌣⊕ (R.mk-cast l (` T3 ⊕ T4) (` T5 ⊕ T6)))
      
                 
lenv : ∀ {T}
  → {v : L.Env T}
  → {u : R.Env T}
  → EnvRelate v u
  → L.Env T
lenv {v = v} vr = v

renv : ∀ {T}
  → {v : L.Env T}
  → {u : R.Env T}
  → EnvRelate v u
  → R.Env T
renv {u = u} vr = u

lval : ∀ {T}
  → {v : L.Val T}
  → {u : R.Val T}
  → ValRelate v u
  → L.Val T
lval {v = v} vr = v

rval : ∀ {T}
  → {v : L.Val T}
  → {u : R.Val T}
  → ValRelate v u
  → R.Val T
rval {u = u} vr = u

_[_] : ∀ {Γ T}
  → {lE : L.Env Γ}
  → {rE : R.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE L.[ x ]) (rE R.[ x ])
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]

data CastRelate : {T1 T2 : Type} → L.Cast T1 T2 → R.Cast T1 T2 → Set where
  cast : ∀ l T1 T2
    → CastRelate (L.mk-cast l T1 T2) (R.mk-cast l T1 T2)

data CastResultRelate {T : Type} : L.CastResult T → R.CastResult T → Set where
  succ :
      {v : L.Val T}{u : R.Val T}
    → ValRelate v u
    → CastResultRelate (L.succ v) (R.succ u)
  fail : (l : Label)
    → CastResultRelate (L.fail l) (R.fail l)

do-cast :
    (l : Label)
  → (T1 T2 : Type)
  → {lv : L.Val T1}
  → {rv : R.Val T1}
  → ValRelate lv rv
  → CastResultRelate (L.apply-cast (L.mk-cast l T1 T2) lv) (R.apply-cast (R.cast l T1 T2) rv)
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆
  rewrite L.lem-cast-id⋆ l (lval v)
  = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P)
  rewrite L.lem-cast-proj l P P₁ (lval v)
  = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P)
  rewrite L.lem-cast-inj l (lval v)
  = succ (inj P v)
do-cast l .(` U) .(` U) sole | yes ⌣U
  rewrite L.lem-cast-U l
  = succ cast-sole
do-cast l .(` U) .(` U) cast-sole | yes ⌣U
  rewrite L.lem-cast-U l
  = succ cast-sole
do-cast l (` T1 ⇒ T2) (` T3 ⇒ T4) (fun E b) | yes ⌣⇒
  rewrite L.lem-cast-⇒ T1 T2 T3 T4 l (lenv E) (L.mk-id _) b (L.mk-id _)
  = succ (cast-fun l T1 T2 T3 T4 _ _ _ _ (fun E b))
do-cast l (` T1 ⇒ T2) (` T3 ⇒ T4) (cast-fun l₁ T5 T6 _ _ lE c1 b c2 f) | yes ⌣⇒
  rewrite L.lem-cast-⇒ T1 T2 T3 T4 l lE
                       (L.mk-seq (L.mk-cast l₁ _ _) c1) b (L.mk-seq c2 (L.mk-cast l₁ _ _))
  = succ (cast-fun l T1 T2 T3 T4 lE _ b _ (cast-fun l₁ T5 T6 _ _ lE _ b _ f))
do-cast l (` (T1 ⊗ T2)) (` (T3 ⊗ T4)) v | yes ⌣⊗ with (lval v)
... | (L.cons v1 c1 v2 c2)
  rewrite L.lem-cast-⊗ _ _ T1 T2 T3 T4 l v1 v2 c1 c2
  = succ (cast-cons l _ _ _ _ _ _ _ _ v)
do-cast l (` (T1 ⊕ T2)) (` (T3 ⊕ T4)) v | yes ⌣⊕ with (lval v)
... | L.inl lv lc
  rewrite L.lem-cast-⊕-l _ T1 T2 T3 T4 l lv lc
  = succ (cast-inl _ _ v l)
... | L.inr lv lc
  rewrite L.lem-cast-⊕-r _ T1 T2 T3 T4 l lv lc
  = succ (cast-inr _ _ v l)
do-cast l T1 T2 v | no ¬p
  rewrite L.lem-cast-¬⌣ l ¬p (lval v)
   = fail l

-- Lemma 4.6 (applyCast Preserves Bisimulation)
apply-cast : ∀ {T1 T2}
  → {lv : L.Val T1}
  → {rv : R.Val T1}
  → ValRelate lv rv
  → {lc : L.Cast T1 T2}
  → {rc : R.Cast T1 T2}
  → CastRelate lc rc
  → CastResultRelate (L.apply-cast lc lv) (R.apply-cast rc rv)
apply-cast v (cast l T1 T2)
  with L.apply-cast (L.mk-cast l T1 T2) (lval v) | R.apply-cast' l T1 T2 (rval v) | do-cast l T1 T2 v
... | L.succ _ | R.succ _ | succ u = succ u
... | L.fail _ | R.fail _ | fail l₁ = fail l₁

mutual
  data ContRelate : {T1 T3 : Type} → L.Cont T1 T3 → R.Cont T1 T3 → Set where
    mk-cont : ∀ {T1 T2}
      → {lk : L.PreCont T1 T2}
      → {rk : R.Cont T1 T2}
      → (k : PreContRelate lk rk)
      ---
      → ContRelate (L.mk-cont lk) rk

    ext-cont : ∀ {T2}
      → (l : Label)
      → ∀ T0 T1
      → {lk : L.Cont T1 T2}
      → {rk : R.Cont T1 T2}
      → (k : ContRelate lk rk)
      ---
      → ContRelate (L.ext-cont (L.mk-cast l T0 T1) lk)
                   (R.cast (R.mk-cast l T0 T1) rk)
  
  data PreContRelate : {T1 T3 : Type} → L.PreCont T1 T3 → R.Cont T1 T3 → Set where
    mt : ∀ {Z}
      ----------
      → PreContRelate ( (L.mt {Z})) (R.mt {Z})
  
    cons₁ : ∀ {Γ T1 T2 Z}
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      → (e1 : Γ ⊢ T2)
      → {lκ : L.Cont (` T1 ⊗ T2) Z}
      → {rκ : R.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.cons₁ lE e1 lκ)) (R.cons₁ rE e1 rκ)
      
    cons₂ : ∀ {T1 T2 Z}
      → {lv1 : L.Val T1}
      → {rv1 : R.Val T1}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : L.Cont (` T1 ⊗ T2) Z}
      → {rκ : R.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.cons₂ lv1 lκ)) (R.cons₂ rv1 rκ)
                                                         
    inl :  ∀ {T1 T2 Z}
      → {lκ : L.Cont (` T1 ⊕ T2) Z}
      → {rκ : R.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.inl lκ)) (R.inl rκ)
                                             
    inr :  ∀ {T1 T2 Z}
      → {lκ : L.Cont (` T1 ⊕ T2) Z}
      → {rκ : R.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.inr lκ)) (R.inr rκ)
        
    app₁ : ∀ {Γ T1 T2 Z}
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ T1)
      → {lκ : L.Cont T2 Z}
      → {rκ : R.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.app₁ lE e2 lκ)) (R.app₁ rE e2 rκ)
                                                           
    app₂ : ∀ {T1 T2 Z}
      → {lv1 : L.Val (` T1 ⇒ T2)}
      → {rv1 : R.Val (` T1 ⇒ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : L.Cont T2 Z}
      → {rκ : R.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.app₂ lv1 lκ)) (R.app₂ rv1 rκ)
                                                       
    car : ∀ {T1 T2 Z}
      → {lκ : L.Cont T1 Z}
      → {rκ : R.Cont T1 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (L.car {T2 = T2} lκ)) (R.car {T2 = T2} rκ)
      
    cdr : ∀ {T1 T2 Z}
      → {lκ : L.Cont T2 Z}
      → {rκ : R.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate ( (L.cdr {T1 = T1} lκ)) (R.cdr {T1 = T1} rκ)
      
    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : L.Cont T3 Z}
      → {rκ : R.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.case₁ lE e2 e3 lκ)) (R.case₁ rE e2 e3 rκ)
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : L.Env Γ}
      → {rE : R.Env Γ}
      → (E : EnvRelate lE rE)
      → {lv1 : L.Val (` T1 ⊕ T2)}
      → {rv1 : R.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : L.Cont T3 Z}
      → {rκ : R.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate ( (L.case₂ lE lv1 e3 lκ)) (R.case₂ rE rv1 e3 rκ)
      
    case₃ : ∀ {T1 T2 T3 Z}
      → {lv1 : L.Val (` T1 ⊕ T2)}
      → {rv1 : R.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lv2 : L.Val (` T1 ⇒ T3)}
      → {rv2 : R.Val (` T1 ⇒ T3)}
      → (v2 : ValRelate lv2 rv2)
      → {lκ : L.Cont T3 Z}
      → {rκ : R.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      ----------------
      → PreContRelate ( (L.case₃ lv1 lv2 lκ)) (R.case₃ rv1 rv2 rκ)
  
data NonhaltingRelate : {T : Type}
  → L.Nonhalting T
  → R.Nonhalting T
  → Set
  where
  
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : L.Env Γ}
    → {rE : R.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : L.Cont T1 T3}
    → {rκ : R.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.inspect e lE lκ) (R.inspect e rE rκ)
    
  return : ∀ {T1 T2}
    → {lv1 : L.Val T1}
    → {rv1 : R.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : L.Cont T1 T2}
    → {rκ : R.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → NonhaltingRelate (L.return lv1 lκ) (R.return rv1 rκ)

data StateRelate : {T : Type} → L.State T → R.State T → Set where

  `_ : ∀ {T}
    → {ls : L.Nonhalting T}
    → {rs : R.Nonhalting T}
    → (s : NonhaltingRelate ls rs)
    → StateRelate (L.` ls) (R.` rs)

  halt : ∀ {T}
    → (o : Observable T)
    → StateRelate (L.halt o) (R.halt o)

lcont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → L.Cont T1 T2
lcont {lk = lk} kk = lk

rcont : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (kk : ContRelate lk rk)
  ---
  → R.Cont T1 T2
rcont {rk = rk} kk = rk

lstate : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → (ss : StateRelate ls rs)
  ---
  → L.State T
lstate {ls = ls} ss = ls

rstate : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → (ss : StateRelate ls rs)
  ---
  → R.State T
rstate {rs = rs} ss = rs

data StateRelate* {T : Type} : L.State T → R.State T → Set where
  it : {ls ls' : L.State T}{rs rs' : R.State T}
    → (ss : StateRelate ls' rs')
    → (xs : ls L.−→* ls')
    → (ys : rs R.−→* rs')
    → StateRelate* ls rs

StateRelate*-done : ∀ {T}
  → {lS : L.State T}
  → {rS : R.State T}
  → (ss : StateRelate lS rS)
  → StateRelate* lS rS
StateRelate*-done ss = it ss L.[] R.[]

StateRelate*-step : ∀ {T}
  → {ls : L.State T}
  → {rs1 rs2 : R.State T}
  → (y  : rs1 R.−→ rs2)
  → (ss : StateRelate* ls rs2)
  → StateRelate* ls rs1
StateRelate*-step y (it ss xs ys) = it ss xs (y R.∷ ys)

ext-cont-id : ∀ {T1 T2}
  → {lk : L.Cont T1 T2}
  → {rk : R.Cont T1 T2}
  → (k : ContRelate lk rk)
  ---
  → ContRelate (L.ext-cont (L.mk-id T1) lk) rk
ext-cont-id {lk = L.cont fst snd} k rewrite L.monoid-id-l fst
  = k

ext-cont-seq : ∀ {T1 T2 T3 T4}
  → (c1 : L.Cast T1 T2)
  → (c2 : L.Cast T2 T3)
  → (k : L.Cont T3 T4)
  ---
  → L.ext-cont (L.mk-seq c1 c2) k ≡ L.ext-cont c1 (L.ext-cont c2 k)
ext-cont-seq c1 c2 (L.cont fst snd)
  rewrite L.monoid-assoc c1 c2 fst
  = refl

lem-do-app : ∀ {Γ T1 T2 T3 T4 T5 T6}
  → (E : L.Env Γ)
  → (c₁ : L.Cast T3 T1)
  → (b : (Γ , T1) ⊢ T2)
  → (c₂ : L.Cast T2 T4)
  → (c₃ : L.Cast T4 T5)
  → (rand : L.Val T3)
  → (k : L.Cont T5 T6)
  → L.do-app (L.fun E c₁ b (L.mk-seq c₂ c₃)) rand k
    ≡
    L.do-app (L.fun E c₁ b c₂) rand (L.ext-cont c₃ k)
lem-do-app E c₁ b c₂ c₃ rand k with L.apply-cast c₁ rand
lem-do-app E c₁ b c₂ c₃ rand k | L.succ v rewrite ext-cont-seq c₂ c₃ k = refl
lem-do-app E c₁ b c₂ c₃ rand k | L.fail l = refl

do-app : ∀ {T1 T2 Z}
  → {lv1 : L.Val (` T1 ⇒ T2)}
  → {rv1 : R.Val (` T1 ⇒ T2)}
  → ValRelate lv1 rv1
  → {lv2 : L.Val T1}
  → {rv2 : R.Val T1}
  → ValRelate lv2 rv2
  → {lk : L.Cont T2 Z}
  → {rk : R.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate* (L.do-app lv1 lv2 lk)
                 (R.do-app rv1 rv2 rk)
do-app (fun E b) rand k
  rewrite L.lem-id _ (lval rand)
  = StateRelate*-done (` inspect b (rand ∷ E) (ext-cont-id k))
do-app (cast-fun l T3 T4 T5 T6 E c1 b c2 {g = g} rator) rand k
  rewrite lem-do-app E (L.mk-seq (L.mk-cast l T5 T3) c1) b c2 (L.mk-cast l T4 T6) (lval rand) (lcont k)
  = StateRelate*-step R.it helper
  where
    helper : StateRelate* (L.do-app (L.fun E (L.mk-seq (L.mk-cast l T5 T3) c1) b c2)
                                    (lval rand)
                                    (L.ext-cont (L.mk-cast l T4 T6) (lcont k)))
                          (R.progress
                            (R.return (rval rand)
                              (R.cast (R.cast l T5 T3)
                              (R.app₂ g (R.cast (R.cast l T4 T6) (rcont k))))))
    helper
      rewrite L.lem-seq (L.mk-cast l T5 T3) c1 (lval rand)
      with L.apply-cast (L.mk-cast l T5 T3) (lval rand) | R.apply-cast (R.mk-cast l T5 T3) (rval rand) | (apply-cast rand (cast l T5 T3))
    ... | L.succ _ | R.succ _ | succ rand₁ = StateRelate*-step R.it (do-app rator rand₁ (ext-cont l T4 T6 k))
    ... | L.fail _ | R.fail _ | fail l₁ = StateRelate*-done (halt (blame l₁))

lem-do-car : ∀ {T1 T2 T3 T4 T5 T6 Z}
  → (l : Label)
  → (v1   : L.Val T1)
  → (c1   : L.Cast T1 T3)
  → (v2   : L.Val T2)
  → (c2   : L.Cast T2 T4)
  → (lk   : L.Cont T5 Z)
  → (L.do-car
       (L.cons v1 (L.mk-seq c1 (L.mk-cast l T3 T5))
                v2 (L.mk-seq c2 (L.mk-cast l T4 T6)))
       lk)
    ≡
    (L.do-car
       (L.cons v1 c1
                v2 c2)
       (L.ext-cont (L.mk-cast l T3 T5) lk))
lem-do-car l v1 c1 v2 c2 (L.cont fst snd)
  rewrite L.monoid-assoc c1 (L.mk-cast l _ _) fst
  = refl

do-car : ∀ {T1 T2 Z}
  → {lv : L.Val (` T1 ⊗ T2)}
  → {rv : R.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : L.Cont T1 Z}
  → {rk : R.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (L.do-car lv lk) (R.do-car rv rk)
do-car (cons v v₁) k = StateRelate*-done (` return v (ext-cont-id k))
do-car (cast-cons l T3 T4 T5 T6 v1 c1 v2 c2 v) k
  rewrite lem-do-car {T6 = T6} l v1 c1 v2 c2 (lcont k)
  = StateRelate*-step R.it (do-car v (ext-cont l T3 T5 k))

lem-do-cdr : ∀ {T1 T2 T3 T4 T5 T6 Z}
  → (l : Label)
  → (v1   : L.Val T1)
  → (c1   : L.Cast T1 T3)
  → (v2   : L.Val T2)
  → (c2   : L.Cast T2 T4)
  → (lk   : L.Cont T6 Z)
  → (L.do-cdr
       (L.cons v1 (L.mk-seq c1 (L.mk-cast l T3 T5))
                v2 (L.mk-seq c2 (L.mk-cast l T4 T6)))
       lk)
    ≡
    (L.do-cdr
       (L.cons v1 c1
                v2 c2)
       (L.ext-cont (L.mk-cast l T4 T6) lk))
lem-do-cdr l v1 c1 v2 c2 (L.cont fst snd)
  rewrite L.monoid-assoc c2 (L.mk-cast l _ _) fst
  = refl

do-cdr : ∀ {T1 T2 Z}
  → {lv : L.Val (` T1 ⊗ T2)}
  → {rv : R.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : L.Cont T2 Z}
  → {rk : R.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate* (L.do-cdr lv lk) (R.do-cdr rv rk)
do-cdr (cons v1 v2) k = StateRelate*-done (` return v2 (ext-cont-id k))
do-cdr (cast-cons l T3 T4 T5 T6 v1 c1 v2 c2 v) k
  rewrite lem-do-cdr {T5 = T5} l v1 c1 v2 c2 (lcont k)
  = StateRelate*-step R.it (do-cdr v (ext-cont l T4 T6 k))

lem-ext-cont : ∀ {T1 T2 T3 T4 Z}
  → (c1 : L.Cast T1 T2)
  → (c2 : L.Cast T2 T3)
  → (c3 : L.Cast T3 T4)
  → (k : L.Cont T4 Z)
  → L.ext-cont (L.mk-seq c1 c2) (L.ext-cont c3 k)
    ≡
    L.ext-cont c1 (L.ext-cont (L.mk-seq c2 c3) k)
lem-ext-cont c1 c2 c3 (L.cont c4 k)
  rewrite L.monoid-assoc c1 c2 (L.mk-seq c3 c4)
        | L.monoid-assoc c2 c3 c4
  = refl

cap-fun : ∀ {Γ T1 T2 T3 T4}
  → {env : L.Env Γ}
  → {c1 : L.Cast T3 T1}
  → {e : (Γ , T1) ⊢ T2}
  → {c2 : L.Cast T2 T4}
  → {rv : R.Val (` T3 ⇒ T4)}
  → (v : ValRelate (L.fun env c1 e c2) rv)
  → (l : Label)
  → ∀ T5
  ---
  → ValRelate (L.fun env
                      (L.mk-seq (L.mk-cast l T5 T3) c1)
                      e
                      c2)
              (R.cast rv ⌣⇒ (R.cast l (` T3 ⇒ T4) (` T5 ⇒ T4)))
cap-fun {T4 = T4} {c2 = c2} v l T5 with cast-fun l _ _ T5 T4 _ _ _ _ v
... | r
  rewrite L.lem-cast-id-is-id l T4
        | L.monoid-id-r c2
  = r              
  
do-case : ∀ {T1 T2 T3 Z}
  → {lv1 : L.Val (` T1 ⊕ T2)}
  → {rv1 : R.Val (` T1 ⊕ T2)}
  → ValRelate lv1 rv1
  → {lv2 : L.Val (` T1 ⇒ T3)}
  → {rv2 : R.Val (` T1 ⇒ T3)}
  → ValRelate lv2 rv2
  → {lv3 : L.Val (` T2 ⇒ T3)}
  → {rv3 : R.Val (` T2 ⇒ T3)}
  → ValRelate lv3 rv3
  → {lk : L.Cont T3 Z}
  → {rk : R.Cont T3 Z}
  → ContRelate lk rk
  → StateRelate* (L.do-case lv1 lv2 lv3 lk)
                 (R.do-case rv1 rv2 rv3 rk)
do-case (inl v1) {lv2 = L.fun env c1 b c2} v2 v3 k rewrite L.monoid-id-l c1 = StateRelate*-done (` return v1 (mk-cont (app₂ v2 k)))
do-case (inr v1) v2 {lv3 = L.fun env c1 b c2} v3 k rewrite L.monoid-id-l c1 = StateRelate*-done (` return v1 (mk-cont (app₂ v3 k)))
do-case (cast-inl lv lc v1 l) {lv2 = L.fun _ c _ _} v2 {lv3 = L.fun _ _ _ _} v3 k with do-case v1 (cap-fun v2 l _) (cap-fun v3 l _) k
... | tmp rewrite L.monoid-assoc lc (L.mk-cast l _ _) c = StateRelate*-step R.it tmp
do-case (cast-inr lv lc v1 l) {lv2 = L.fun _ _ _ _} v2 {lv3 = L.fun _ c _ _} v3 k with do-case v1 (cap-fun v2 l _) (cap-fun v3 l _) k
... | tmp rewrite L.monoid-assoc lc (L.mk-cast l _ _) c = StateRelate*-step R.it tmp

observe-val : ∀ {T}
  → {lv : L.Val T}
  → {rv : R.Val T}
  → ValRelate lv rv
  → L.observe-val lv ≡ R.observe-val rv
observe-val (inj P v) = refl
observe-val (fun E b) = refl
observe-val (cast-fun l T3 T4 T5 T6 lE c1 b c2 v) = refl
observe-val sole = refl
observe-val cast-sole = refl
observe-val (cons v v₁) = refl
observe-val (cast-cons l T3 T4 T5 T6 v1 c1 v2 c2 v) = refl
observe-val (inl x) = refl
observe-val (cast-inl lv lc v l) with R.observe-val (rval v) | observe-val v
... | inl | refl = refl
observe-val (inr x) = refl
observe-val (cast-inr lv lc v l) with R.observe-val (rval v) | observe-val v
... | inr | refl = refl
  
progress*-return : ∀ {T Z}
  → {lv : L.Val T}
  → {rv : R.Val T}
  → ValRelate lv rv
  → {lk : L.PreCont T Z}
  → {rk : R.Cont T Z}
  → PreContRelate lk rk
  ---
  → StateRelate* (L.progress-return lv lk) (R.progress (R.return rv rk))
progress*-return v mt with L.observe-val (lval v) | R.observe-val (rval v) | observe-val v
... | _ | _ | refl = StateRelate*-done (halt (done _))
progress*-return v (cons₁ E e1 κ) = StateRelate*-done (` inspect e1 E (mk-cont (cons₂ v κ)))
progress*-return v (cons₂ v1 κ) = StateRelate*-done (` return (cons v1 v) κ)
progress*-return v (inl κ) = StateRelate*-done (` return (inl v) κ)
progress*-return v (inr κ) = StateRelate*-done (` return (inr v) κ)
progress*-return v (app₁ E e2 κ) = StateRelate*-done (` inspect e2 E (mk-cont (app₂ v κ)))
progress*-return v (app₂ v1 κ) = do-app v1 v κ
progress*-return v (car κ) = do-car v κ
progress*-return v (cdr κ) = do-cdr v κ
progress*-return v (case₁ E e2 e3 κ)
  = StateRelate*-done (` inspect e2 E (mk-cont (case₂ E v e3 κ)))
progress*-return v (case₂ E v1 e3 κ)
  = StateRelate*-done (` inspect e3 E (mk-cont (case₃ v1 v κ)))
progress*-return v (case₃ v1 v2 κ) = do-case v1 v2 v κ

progress-ret : ∀ {T1 Z}
  → {lv : L.Val T1}
  → {rv : R.Val T1}
  → ValRelate lv rv
  → {lk : L.Cont T1 Z}
  → {rk : R.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate* (L.progress (L.return lv lk))
                 (R.progress (R.return rv rk))
progress-ret v (mk-cont k)
  rewrite L.lem-id _ (lval v)
  = progress*-return v k
progress-ret v (ext-cont l T1 T2 {lk = (L.cont c k)} k')
  rewrite L.lem-seq (L.mk-cast l T1 T2) c (lval v)
  with (L.apply-cast (L.mk-cast l T1 T2) (lval v)) | (R.apply-cast' l T1 T2 (rval v)) | (do-cast l T1 T2 v)
... | L.succ _ | R.succ _ | succ v₁ = StateRelate*-step R.it (progress-ret v₁ k')
... | L.fail _ | R.fail _ | fail l₁ = StateRelate*-done (halt (blame l₁))

progress* : ∀ {T}
  → {lS : L.Nonhalting T}
  → {rS : R.Nonhalting T}
  → NonhaltingRelate lS rS
  → StateRelate* (L.progress lS) (R.progress rS)
progress* (inspect (var x) E κ) = StateRelate*-done (` return (E [ x ]) κ)
progress* (inspect sole E κ) = StateRelate*-done (` return sole κ)
progress* (inspect (lam T1 T2 e) E κ) = StateRelate*-done (` return (fun E e) κ)
progress* (inspect (cons e e₁) E κ) = StateRelate*-done (` inspect e E (mk-cont (cons₁ E e₁ κ)))
progress* (inspect (inl e) E κ) = StateRelate*-done (` inspect e E (mk-cont (inl κ)))
progress* (inspect (inr e) E κ) = StateRelate*-done (` inspect e E (mk-cont (inr κ)))
progress* (inspect (app e e₁) E κ) = StateRelate*-done (` inspect e E (mk-cont (app₁ E e₁ κ)))
progress* (inspect (car e) E κ) = StateRelate*-done (` inspect e E (mk-cont (car κ)))
progress* (inspect (cdr e) E κ) = StateRelate*-done (` inspect e E (mk-cont (cdr κ)))
progress* (inspect (case e e₁ e₂) E κ) = StateRelate*-done (` inspect e E (mk-cont (case₁ E e₁ e₂ κ)))
progress* (inspect (cast l T1 T2 e) E κ) = StateRelate*-done (` inspect e E (ext-cont l _ _ κ))
progress* (inspect (blame l) E κ) = StateRelate*-done (halt (blame l))
progress* (return v k) = progress-ret v k

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (L.load e) (R.load e)
load e = ` inspect e [] (mk-cont mt)

-- Lemma 4.8 Weak Bisimulation between S(C) and D
lem-weak-bisimulation-SC-D : ∀ {T}
  → {ls : L.State T}
  → {rs : R.State T}
  → (ss : StateRelate ls rs)
  → (L.Final ls × R.Final rs)
    ⊎
    ∃[ ls' ]
    ∃[ rs' ](
       (StateRelate ls' rs') ×
       (ls L.−→+ ls') ×
       (rs R.−→+ rs'))
lem-weak-bisimulation-SC-D (` ss) with progress* ss
lem-weak-bisimulation-SC-D (` ss) | it ss' xs ys
  = inj₂ (_ , _ , ss' , (_ , L.it , xs) , (_ , R.it , ys))
lem-weak-bisimulation-SC-D (halt o) = inj₁ ((o , refl) , (o , refl))

module Foo {T : Type} where
  import Bisim
  module CorrectnessTheorems =
    Bisim.Theorems (L.system {T = T}) R.system StateRelate lem-weak-bisimulation-SC-D
  open CorrectnessTheorems using (thm-final-LR; thm-final-RL) public

-- Corollary 4.9 (Correctness of S(C))

correctness-l : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → L.Evalo e o
  ---
  → R.Evalo e o
correctness-l {e = e} (o , xs) with Foo.thm-final-LR (load e) xs (o , refl)
correctness-l {e = e} (o , xs) | (R.halt o) , ys , (o , refl) , halt o = o , ys

correctness-r : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observable T}
  → R.Evalo e o
  ---
  → L.Evalo e o
correctness-r {e = e} (o , xs) with Foo.thm-final-RL (load e) xs (o , refl)
correctness-r {e = e} (o , xs) | (L.halt o) , ys , (o , refl) , halt o = o , ys
