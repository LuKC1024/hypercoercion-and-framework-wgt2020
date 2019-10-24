open import CEKcc.CastRep

module CEKcc.BiSimulation
  (Label : Set)
  (LCR : CastRep Label)
  (LCS : SurelyLazyD Label LCR)
  (RCR : CastRep Label)
  (RCS : SurelyLazyD Label RCR)
  where

open import Utilities using (repeat)
open import Variables
open import Types
open import Terms Label
open import Observe Label
import CEKcc.Machine
import CEKcc.Values

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Nat using (ℕ; suc; zero)
open import Data.Product using ( _×_ ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩)

module Values = CEKcc.Values Label

-- an abstract machine specialized for an representation

module L where
  open CastRep LCR public
  open SurelyLazyD LCS public

module LV = CEKcc.Values Label L.Cast
module LM = CEKcc.Machine Label LCR

-- an abstract machine specialized for another representation

module R where
  open CastRep RCR public
  open SurelyLazyD RCS public

module RV = CEKcc.Values Label R.Cast
module RM = CEKcc.Machine Label RCR

data CastRelate : ∀ {T1 T2} → L.Cast T1 T2 → R.Cast T1 T2 → Set where
  id : ∀ {T}
     --------------------------------------------------
     → CastRelate (L.mk-id T) (R.mk-id T)
  cast : ∀ l T1 T2
    ---------------------------------------------------------
    → CastRelate (L.mk-cast l T1 T2) (R.mk-cast l T1 T2)
  seq : ∀ {T1 T2 T3}
    → {c₁ : L.Cast T1 T2}
    → {ç₁ : R.Cast T1 T2}
    → CastRelate c₁ ç₁
    → {c₂ : L.Cast T2 T3}
    → {ç₂ : R.Cast T2 T3}
    → CastRelate c₂ ç₂
    ---------------------------------------------------------
    → CastRelate (L.mk-seq c₁ c₂) (R.mk-seq ç₁ ç₂)
    
mutual

  data EnvRelate : ∀ {Γ} → LV.Env Γ → RV.Env Γ → Set where
    []  : EnvRelate LV.[] RV.[]
    _∷_ : ∀ {Γ T}
      → {v : LV.Val T}{u : RV.Val T}
      → ValRelate v u
      → {E : LV.Env Γ}{F : RV.Env Γ}
      → EnvRelate E F
      → EnvRelate (LV._∷_ v E) (RV._∷_ u F)

  data ValRelate : ∀ {T} → LV.Val T → RV.Val T → Set where
    inj : ∀ P
      → {v : LV.Val (` P)}
      → {u : RV.Val (` P)}
      → ValRelate v u
      ----------------
      → ValRelate (LV.inj _ v) (RV.inj _ u)
      
    fun : ∀ {Γ T1 T2 T3 T4}
      → {E : LV.Env Γ}{F : RV.Env Γ}
      → EnvRelate E F
      → {c1 : L.Cast T3 T1}{ç1 : R.Cast T3 T1}
      → CastRelate c1 ç1
      → (b : Γ , T1 ⊢ T2)
      → {c2 : L.Cast T2 T4}{ç2 : R.Cast T2 T4}
      → CastRelate c2 ç2
      -------------
      → ValRelate (LV.fun E c1 b c2) (RV.fun F ç1 b ç2)

    sole :
      --------
        ValRelate LV.sole RV.sole

    cons : ∀ {T1 T2 T3 T4}
      → {v1 : LV.Val T1}
      → {u1 : RV.Val T1}
      → ValRelate v1 u1
      → {c1 : L.Cast T1 T3}
      → {ç1 : R.Cast T1 T3}
      → CastRelate c1 ç1
      → {v2 : LV.Val T2}
      → {u2 : RV.Val T2}
      → ValRelate v2 u2
      → {c2 : L.Cast T2 T4}
      → {ç2 : R.Cast T2 T4}
      → CastRelate c2 ç2
      ------------------
      → ValRelate (LV.cons v1 c1 v2 c2) (RV.cons u1 ç1 u2 ç2)

    inl : ∀ {T1 T2 T3}
      → {v : LV.Val T1}
      → {u : RV.Val T1}
      → ValRelate v u
      → {c : L.Cast T1 T3}
      → {ç : R.Cast T1 T3}
      → CastRelate c ç
      -----------------
      → ValRelate (LV.inl {T2 = T2} v c) (RV.inl u ç)
      
    inr : ∀ {T1 T2 T4}
      → {v : LV.Val T2}
      → {u : RV.Val T2}
      → ValRelate v u
      → {c : L.Cast T2 T4}
      → {ç : R.Cast T2 T4}
      → CastRelate c ç
      -----------------
      → ValRelate (LV.inr {T1 = T1} v c) (RV.inr u ç)

_[_] : ∀ {Γ T}
  → {lE : LV.Env Γ}
  → {rE : RV.Env Γ}
  → (E : EnvRelate lE rE)
  → (x : Γ ∋ T)
  → ValRelate (lE LV.[ x ]) (rE RV.[ x ])
(c ∷ E) [ Z ] = c
(c ∷ E) [ S x ] = E [ x ]


data CastResultRelate {T : Type} : LV.CastResult T → RV.CastResult T → Set where
  succ :
      {v : LV.Val T}{u : RV.Val T}
    → ValRelate v u
    → CastResultRelate (LV.succ v) (RV.succ u)
  fail : (l : Label)
    → CastResultRelate (LV.fail l) (RV.fail l)

mutual
  -- cast from T1 to T2
  data ContRelate : {T1 T3 : Type} (lκ : LM.Cont T1 T3) (rκ : RM.Cont T1 T3) → Set where
    cont : ∀ {T1 T3 mid}
      → {lfst : L.Cast T1 mid}
      → {rfst : R.Cast T1 mid}
      → (fst : CastRelate lfst rfst)
      → {lsnd : LM.PreCont mid T3}
      → {rsnd : RM.PreCont mid T3}
      → (snd : PreContRelate lsnd rsnd)
      → ContRelate (LM.cont lfst lsnd) (RM.cont rfst rsnd)

  data PreContRelate : {T1 T3 : Type} → LM.PreCont T1 T3 → RM.PreCont T1 T3 → Set where
  
    -- Every expression of arity n has n pre-continuations, except cast

    mt : ∀ {Z}
      ----------
      → PreContRelate (LM.mt {Z}) (RM.mt {Z})

    cons₁ : ∀ {Γ T1 T2 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e1 : Γ ⊢ T2)
      → {lκ : LM.Cont (` T1 ⊗ T2) Z}
      → {rκ : RM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.cons₁ lE e1 lκ) (RM.cons₁ rE e1 rκ)
      
    cons₂ : ∀ {T1 T2 Z}
      → {lv1 : LV.Val T1}
      → {rv1 : RV.Val T1}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : LM.Cont (` T1 ⊗ T2) Z}
      → {rκ : RM.Cont (` T1 ⊗ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.cons₂ lv1 lκ) (RM.cons₂ rv1 rκ)

    inl :  ∀ {T1 T2 Z}
      → {lκ : LM.Cont (` T1 ⊕ T2) Z}
      → {rκ : RM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.inl lκ) (RM.inl rκ)

    inr :  ∀ {T1 T2 Z}
      → {lκ : LM.Cont (` T1 ⊕ T2) Z}
      → {rκ : RM.Cont (` T1 ⊕ T2) Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.inr lκ) (RM.inr rκ)
           
    app₁ : ∀ {Γ T1 T2 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ T1)
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.app₁ lE e2 lκ) (RM.app₁ rE e2 rκ)

    app₂ : ∀ {T1 T2 Z}
      → {lv1 : LV.Val (` T1 ⇒ T2)}
      → {rv1 : RV.Val (` T1 ⇒ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.app₂ lv1 lκ) (RM.app₂ rv1 rκ)

    car : ∀ {T1 T2 Z}
      → {lκ : LM.Cont T1 Z}
      → {rκ : RM.Cont T1 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate (LM.car {T2 = T2} lκ) (RM.car {T2 = T2} rκ)
      
    cdr : ∀ {T1 T2 Z}
      → {lκ : LM.Cont T2 Z}
      → {rκ : RM.Cont T2 Z}
      → (κ : ContRelate lκ rκ)
      -----------
      → PreContRelate (LM.cdr {T1 = T1} lκ) (RM.cdr {T1 = T1} rκ)
      
    case₁ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → (e2 : Γ ⊢ ` T1 ⇒ T3)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.case₁ lE e2 e3 lκ) (RM.case₁ rE e2 e3 rκ)
      
    case₂ :  ∀ {Γ T1 T2 T3 Z}
      → {lE : LV.Env Γ}
      → {rE : RV.Env Γ}
      → (E : EnvRelate lE rE)
      → {lv1 : LV.Val (` T1 ⊕ T2)}
      → {rv1 : RV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → (e3 : Γ ⊢ ` T2 ⇒ T3)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      --------
      → PreContRelate (LM.case₂ lE lv1 e3 lκ) (RM.case₂ rE rv1 e3 rκ)
      
    case₃ : ∀ {T1 T2 T3 Z}
      → {lv1 : LV.Val (` T1 ⊕ T2)}
      → {rv1 : RV.Val (` T1 ⊕ T2)}
      → (v1 : ValRelate lv1 rv1)
      → {lv2 : LV.Val (` T1 ⇒ T3)}
      → {rv2 : RV.Val (` T1 ⇒ T3)}
      → (v2 : ValRelate lv2 rv2)
      → {lκ : LM.Cont T3 Z}
      → {rκ : RM.Cont T3 Z}
      → (κ : ContRelate lκ rκ)
      ----------------
      → PreContRelate (LM.case₃ lv1 lv2 lκ) (RM.case₃ rv1 rv2 rκ)

mk-cont : ∀ {T1 T2}
  → {lκ : LM.PreCont T1 T2}
  → {rκ : RM.PreCont T1 T2}
  → (κ : PreContRelate lκ rκ)
  → ContRelate (LM.mk-cont lκ) (RM.mk-cont rκ)
mk-cont κ = cont id κ

ext-cont : ∀ {T1 T2 T3}
  → {lc : L.Cast T1 T2}
  → {rc : R.Cast T1 T2}
  → (c : CastRelate lc rc)
  → {lκ : LM.Cont T2 T3}
  → {rκ : RM.Cont T2 T3}
  → (κ : ContRelate lκ rκ)
  → ContRelate (LM.ext-cont lc lκ) (RM.ext-cont rc rκ)
ext-cont c (cont fst snd) = cont (seq c fst) snd

data StateRelate : {T : Type} → LM.State T → RM.State T → Set where
  inspect : ∀ {Γ T1 T3}
    → (e : Γ ⊢ T1)
    → {lE : LV.Env Γ}
    → {rE : RV.Env Γ}
    → (E : EnvRelate lE rE)
    → {lκ : LM.Cont T1 T3}
    → {rκ : RM.Cont T1 T3}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (LM.inspect e lE lκ) (RM.inspect e rE rκ)
    
  return : ∀ {T1 T2}
    → {lv1 : LV.Val T1}
    → {rv1 : RV.Val T1}
    → (v1 : ValRelate lv1 rv1)
    → {lκ : LM.Cont T1 T2}
    → {rκ : RM.Cont T1 T2}
    → (κ : ContRelate lκ rκ)
    ------------
    → StateRelate (LM.return lv1 lκ) (RM.return rv1 rκ)

  halt : ∀ {T}
    → (o : Observe T)
    → StateRelate (LM.halt o) (RM.halt o)


  -- halt : ∀ {T}
  --   → {lo : Observe T}
  --   → {ro : Observe T}
  --   → lo ≡ ro
  --   → StateRelate (LM.halt lo) (RM.halt ro)

lval : ∀ {T}
  → {v : LV.Val T}
  → {u : RV.Val T}
  → ValRelate v u
  → LV.Val T
lval {v = v} vr = v

rval : ∀ {T}
  → {v : LV.Val T}
  → {u : RV.Val T}
  → ValRelate v u
  → RV.Val T
rval {u = u} vr = u

lenv : ∀ {Γ}
  → {E : LV.Env Γ}
  → {F : RV.Env Γ}
  → EnvRelate E F
  → LV.Env Γ
lenv {E = E} vr = E

renv : ∀ {Γ}
  → {E : LV.Env Γ}
  → {F : RV.Env Γ}
  → EnvRelate E F
  → RV.Env Γ
renv {F = F} vr = F

rcast : ∀ {T1 T2}
  → {c : L.Cast T1 T2}
  → {d : R.Cast T1 T2}
  → CastRelate c d
  → R.Cast T1 T2
rcast {d = d} cd = d

lcast : ∀ {T1 T2}
  → {c : L.Cast T1 T2}
  → {d : R.Cast T1 T2}
  → CastRelate c d
  → L.Cast T1 T2
lcast {c = c} cd = c

_>>=_ : ∀ {T1 T2}
  → {R : LV.CastResult T1}
  → {S : RV.CastResult T1}
  → CastResultRelate R S
  → {f : LV.Val T1 → (LV.CastResult T2)}
  → {g : RV.Val T1 → (RV.CastResult T2)}
  → ({v : LV.Val T1} → {u : RV.Val T1} → ValRelate v u → CastResultRelate (f v) (g u))
  → CastResultRelate (R LV.>>= f) (S RV.>>= g)
succ v >>= f = f v
fail l >>= f = fail l

do-cast :
    (l : Label)
  → (T1 T2 : Type)
  → {v : LV.Val T1}
  → {u : RV.Val T1}
  → ValRelate v u
  → CastResultRelate (L.apply-cast (L.mk-cast l T1 T2) v)
                     (R.apply-cast (R.mk-cast l T1 T2) u)
do-cast l T1 T2 v with T1 ⌣? T2
do-cast l .⋆ .⋆ v | yes ⋆⌣⋆
  rewrite L.lem-cast-id⋆ l (lval v) | R.lem-cast-id⋆ l (rval v)
  = succ v
do-cast l .⋆ .(` P) (inj P₁ v) | yes (⋆⌣P P)
  rewrite L.lem-cast-proj l P P₁ (lval v) | R.lem-cast-proj l P P₁ (rval v)
  = do-cast l (` P₁) (` P) v
do-cast l .(` P) .⋆ v | yes (P⌣⋆ P)
  rewrite L.lem-cast-inj l (lval v) | R.lem-cast-inj l (rval v)
  = succ (inj P v)
do-cast l .(` U) .(` U) sole | yes ⌣U
  rewrite L.lem-cast-U l | R.lem-cast-U l
  = succ sole
do-cast l (` (T11 ⇒ T12)) (` (T21 ⇒ T22)) (fun E c₁ b c₂) | yes ⌣⇒
  rewrite L.lem-cast-⇒ T11 T12 T21 T22 l (lenv E) (lcast c₁) b (lcast c₂)
    | R.lem-cast-⇒ T11 T12 T21 T22 l (renv E) (rcast c₁) b (rcast c₂)
  = succ (fun E (seq (cast l T21 T11) c₁) b (seq c₂ (cast l T12 T22)))
do-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22)) (cons v c v₁ c₁) | yes ⌣⊗
  rewrite L.lem-cast-⊗ _ _ T11 T12 T21 T22 l (lval v) (lval v₁) (lcast c) (lcast c₁)
    | R.lem-cast-⊗ _ _ T11 T12 T21 T22 l (rval v) (rval v₁) (rcast c) (rcast c₁)
  = succ (cons v (seq c (cast l T11 T21)) v₁ (seq c₁ (cast l T12 T22)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inl v c) | yes ⌣⊕
  rewrite L.lem-cast-⊕-l _ T11 T12 T21 T22 l (lval v) (lcast c)
    | R.lem-cast-⊕-l _ T11 T12 T21 T22 l (rval v) (rcast c)
  = succ (inl v (seq c (cast l T11 T21)))
do-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22)) (inr v c) | yes ⌣⊕
  rewrite L.lem-cast-⊕-r _ T11 T12 T21 T22 l (lval v) (lcast c)
    | R.lem-cast-⊕-r _ T11 T12 T21 T22 l (rval v) (rcast c)
  = succ (inr v (seq c (cast l T12 T22)))
do-cast l T1 T2 v | no ¬p
  rewrite L.lem-cast-¬⌣ l ¬p (lval v)
    | R.lem-cast-¬⌣ l ¬p (rval v)
  = fail l

apply-cast : ∀ {T1 T2}
  → {c : L.Cast T1 T2}{ç : R.Cast T1 T2}
  → CastRelate c ç
  → {v : LV.Val T1}{u : RV.Val T1}
  → ValRelate v u
  ----------------------
  → CastResultRelate (L.apply-cast c v) (R.apply-cast ç u)
apply-cast (id {T}) vr
  rewrite L.lem-id T (lval vr) | R.lem-id T (rval vr) =
  succ vr
apply-cast (cast l T1 T2) vr = do-cast l T1 T2 vr
apply-cast (seq {c₁ = c₁}{ç₁ = ç₁} cç1 {c₂ = c₂}{ç₂ = ç₂} cç2) {v = v}{u = u} vr
  rewrite L.lem-seq c₁ c₂ v | R.lem-seq ç₁ ç₂ u
  = apply-cast cç1 vr >>= λ ur →
    apply-cast cç2 ur

do-app : ∀ {T1 T2 Z}
  → {lv1 : LV.Val (` T1 ⇒ T2)}
  → {rv1 : RV.Val (` T1 ⇒ T2)}
  → ValRelate lv1 rv1
  → {lv2 : LV.Val T1}
  → {rv2 : RV.Val T1}
  → ValRelate lv2 rv2
  → {lk : LM.Cont T2 Z}
  → {rk : RM.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate (LM.do-app lv1 lv2 lk) (RM.do-app rv1 rv2 rk)
do-app (fun env c₁ b c₂) rand κ with L.apply-cast (lcast c₁) (lval rand) | R.apply-cast (rcast c₁) (rval rand) | apply-cast c₁ rand
do-app (fun env c₁ b c₂) rand κ | CEKcc.Values.succ _ | CEKcc.Values.succ _ | succ v = inspect b (v ∷ env) (ext-cont c₂ κ)
do-app (fun env c₁ b c₂) rand κ | CEKcc.Values.fail _ | CEKcc.Values.fail _ | fail l = halt (blame l)

do-car : ∀ {T1 T2 Z}
  → {lv : LV.Val (` T1 ⊗ T2)}
  → {rv : RV.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : LM.Cont T1 Z}
  → {rk : RM.Cont T1 Z}
  → ContRelate lk rk
  → StateRelate (LM.do-car lv lk) (RM.do-car rv rk)
do-car (cons v1 c1 v2 c2) k = return v1 (ext-cont c1 k)

do-cdr : ∀ {T1 T2 Z}
  → {lv : LV.Val (` T1 ⊗ T2)}
  → {rv : RV.Val (` T1 ⊗ T2)}
  → ValRelate lv rv
  → {lk : LM.Cont T2 Z}
  → {rk : RM.Cont T2 Z}
  → ContRelate lk rk
  → StateRelate (LM.do-cdr lv lk) (RM.do-cdr rv rk)
do-cdr (cons v1 c1 v2 c2) k = return v2 (ext-cont c2 k)

do-case : ∀ {T1 T2 T3 Z}
  → {lv1 : LV.Val (` T1 ⊕ T2)}
  → {rv1 : RV.Val (` T1 ⊕ T2)}
  → ValRelate lv1 rv1
  → {lv2 : LV.Val (` T1 ⇒ T3)}
  → {rv2 : RV.Val (` T1 ⇒ T3)}
  → ValRelate lv2 rv2
  → {lv3 : LV.Val (` T2 ⇒ T3)}
  → {rv3 : RV.Val (` T2 ⇒ T3)}
  → ValRelate lv3 rv3
  → {lk : LM.Cont T3 Z}
  → {rk : RM.Cont T3 Z}
  → ContRelate lk rk
  → StateRelate (LM.do-case lv1 lv2 lv3 lk)
                (RM.do-case rv1 rv2 rv3 rk)
do-case (inl v1 c) (fun env c₁ b c₂) v3 k = return v1 (mk-cont (app₂ (fun env (seq c c₁) b c₂) k))
do-case (inr v1 c) v2 (fun env c₁ b c₂) k = return v1 (mk-cont (app₂ (fun env (seq c c₁) b c₂) k))

observe-val : ∀ {T}
  → {lv : LV.Val T}
  → {rv : RV.Val T}
  → ValRelate lv rv
  → LM.observe-val lv ≡ RM.observe-val rv
observe-val (inj P v) = refl
observe-val (fun env c₁ b c₂) = refl
observe-val sole = refl
observe-val (cons v c₁ v₁ c₂) = refl
observe-val (inl v c) = refl
observe-val (inr v c) = refl

progress-return : ∀ {T Z}
  → {lv : LV.Val T}
  → {rv : RV.Val T}
  → ValRelate lv rv
  → {lk : LM.PreCont T Z}
  → {rk : RM.PreCont T Z}
  → PreContRelate lk rk
  ---
  → StateRelate (LM.progress-return lv lk) (RM.progress-return rv rk) 
progress-return v mt with LM.observe-val (lval v) | RM.observe-val (rval v) | observe-val v
... | lo | ro | refl = halt (done lo)
progress-return v (cons₁ E e1 κ) = inspect e1 E (mk-cont (cons₂ v κ))
progress-return v (cons₂ {T1} {T2} v1 κ) = return (cons v1 id v id) κ
progress-return v (inl κ) = return (inl v id) κ
progress-return v (inr κ) = return (inr v id) κ
progress-return v (app₁ E e2 κ) = inspect e2 E (mk-cont (app₂ v κ))
progress-return v (app₂ v₁ κ) = do-app v₁ v κ
progress-return v (car κ) = do-car v κ
progress-return v (cdr κ) = do-cdr v κ
progress-return v (case₁ E e2 e3 κ) = inspect e2 E (mk-cont (case₂ E v e3 κ))
progress-return v (case₂ E v1 e3 κ) = inspect e3 E (mk-cont (case₃ v1 v κ))
progress-return v (case₃ v1 v2 κ) = do-case v1 v2 v κ

progress : ∀ {T}
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate lS rS
  → StateRelate (LM.progress lS) (RM.progress rS)
progress (inspect sole E κ) = return sole κ
progress (inspect (var X) E κ) = return (E [ X ]) κ
progress (inspect (lam T1 T2 e) E κ) = return (fun E id e id) κ
progress (inspect (cons e1 e2) E κ) = inspect e1 E (mk-cont (cons₁ E e2 κ))
progress (inspect (inl e) E κ) = inspect e E (mk-cont (inl κ))
progress (inspect (inr e) E κ) = inspect e E (mk-cont (inr κ))
progress (inspect (app e1 e2) E κ) = inspect e1 E (mk-cont (app₁ E e2 κ))
progress (inspect (car e) E κ) = inspect e E (mk-cont (car κ))
progress (inspect (cdr e) E κ) = inspect e E (mk-cont (cdr κ))
progress (inspect (case e1 e2 e3) E κ) = inspect e1 E (mk-cont (case₁ E e2 e3 κ))
progress (inspect (cast l T1 T2 e) E κ) = inspect e E (ext-cont (cast l T1 T2) κ)
progress (inspect (blame l) E κ) = halt (blame l)
progress (return {lv1 = lv1} {rv1 = rv1} v {(LM.cont lfst lsnd)} {(RM.cont rfst rsnd)} (cont fst₂ snd₂))
  with (L.apply-cast lfst lv1) | (R.apply-cast rfst rv1) | apply-cast fst₂ v
... | Values.succ _ | (RV.succ _) | succ u = progress-return u snd₂
... | Values.fail _ | (RV.fail _) | fail l = halt (blame l)
progress (halt o) = halt o

load : ∀ {T} → (e : ∅ ⊢ T) → StateRelate (LM.load e) (RM.load e)
load e = inspect e [] (cont id mt)

progress* : ∀ {T}
  → (n : ℕ)
  → {lS : LM.State T}
  → {rS : RM.State T}
  → StateRelate lS rS
  → StateRelate (repeat n LM.progress lS) (repeat n RM.progress rS)
progress* zero SS = SS
progress* (suc n) SS = progress* n (progress SS)

lem-evalo-l : ∀ {T}
  → (n : ℕ)
  → {ls : LM.State T}
  → {rs : RM.State T}
  → (ss : StateRelate ls rs)
  → (o : Observe T)
  → repeat n LM.progress ls ≡ LM.halt o
  ---
  → repeat n RM.progress rs ≡ RM.halt o
lem-evalo-l zero (halt _) o refl = refl
lem-evalo-l (suc n) ss o p = lem-evalo-l n (progress ss) o p

thm-evalo : ∀ {T}
  → {e : ∅ ⊢ T}
  → {o : Observe T}
  → LM.Evalo e o
  ---
  → RM.Evalo e o
thm-evalo {e = e} {o} (LM.evalo n prf) = RM.evalo n (lem-evalo-l n (load e) o prf)
