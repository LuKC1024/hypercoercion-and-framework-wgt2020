module Bisim
  where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_ ; inj₁; inj₂)
open import Data.Product using (Σ; _×_ ; Σ-syntax; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

-- This is a parameterized bisimulation proof between any two systems.

-- A *system* is a deterministic transition system, which includes
--   - a set of states
--   - a transition relation
--   - a theorem saying that final state cannot transition
--   - a theorem saying that the transition relation is deterministic

-- The parameterized bisimulation proof claims that
-- given a bisimulation relation _≈_
-- If s₁ ≈ s₂ implies that either
--   - s₁ final and s₂ final, or
--   - there exist s₃ and s₄ such that s₁ −→+ s₃ and s₂ −→+ s₄ and s₃ ≈ s₄
-- then for all s₁ ≈ s₂
--   - s₁ −→* s₃ and s₃ final implies s₂ −→* s₄ and s₄ final and s₃ ≈ s₄ for some s₄
--   - s₂ −→* s₄ and s₄ final implies s₁ −→* s₃ and s₃ final and s₃ ≈ s₄ for some s₃

record System (State : Set) : Set₁ where
  field
    _−→_ : State → State → Set
    Final : State → Set
    final-nontransitional : ∀ {s t}
      → Final s
      → (s −→ t)
      → ⊥
    deterministic : ∀ {s t1 t2}
      → s −→ t1
      → s −→ t2
      → t1 ≡ t2
      
  data _−→*_ : State → State → Set where
    [] : {s : State}
      → s −→* s

    _∷_ : ∀ {s1 s2 s3}
      → (x  : s1 −→ s2)
      → (xs : s2 −→* s3)
      → s1 −→* s3

  _−→+_ : State → State → Set
  s1 −→+ s2 = ∃[ s ] (s1 −→ s × s −→* s2)

  data Prefix : {s1 s2 s3 : State} → s1 −→* s2 → s1 −→* s3 → Set where
    zero : ∀ {s1 s3}
      → {xs : s1 −→* s3}
      → Prefix [] xs

    suc : ∀ {s0 s1 s2 s3}
      → {x : s0 −→ s1}
      → {y : s0 −→ s1}
      → {xs : s1 −→* s2}
      → {ys : s1 −→* s3}
      → Prefix xs ys
      → Prefix (x ∷ xs) (y ∷ ys)

  _++_ : ∀ {s1 s2 s3} → s1 −→* s2 → s2 −→* s3 → s1 −→* s3
  [] ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

module Lemmas
  {lState rState : Set}
  (lSystem : System lState)
  (rSystem : System rState)
  (_~_ : lState → rState → Set)
  (preserve : {ls : lState}{rs : rState}
    → ls ~ rs
    → (System.Final lSystem ls × System.Final rSystem rs)
      ⊎
      ∃[ ls' ]
      ∃[ rs' ](
        (ls' ~ rs') ×
        System._−→+_ lSystem ls ls' ×
        System._−→+_ rSystem rs rs'))
  where

  open System using ([]; _∷_; zero; suc)

  module L where
    open System lSystem public
    
  module R where
    open System rSystem public

  prefix : ∀ {ls}
    → ∀ {ls'}
    → (xs : ls L.−→* ls')
    → L.Final ls'
    → ∀ {ls*}
    → (ys : ls L.−→* ls*)
    → L.Prefix ys xs
  prefix xs halt [] = zero
  prefix [] halt (y ∷ ys) = ⊥-elim (L.final-nontransitional halt y)
  prefix (x ∷ xs) halt (y ∷ ys) with L.deterministic x y
  ... | refl = suc (prefix xs halt ys)

  mutual
    -- the job of this helper is cutting prefix
    lem-final-helper : ∀ {ls1 ls2 rs}
      → (ss : ls2 ~ rs)
      → ∀ {ls'}
      → (xs : ls1 L.−→* ls2)
      → (ys : ls1 L.−→* ls')
      → L.Prefix xs ys
      → L.Final ls'
      → ∃[ rs' ](
           rs R.−→* rs' ×
           R.Final rs' ×
           ls' ~ rs'
        )
    lem-final-helper ss [] ys zero ht = lem-final ss ys ht
    lem-final-helper ss (x ∷ xs) (y ∷ ys) (suc n) ht = lem-final-helper ss xs ys n ht

    lem-final : ∀ {ls rs}
      → (ss : ls ~ rs)
      → ∀ {ls'}
      → ls L.−→* ls'
      → L.Final ls'
      → ∃[ rs' ](
           rs R.−→* rs' ×
           R.Final rs' ×
           ls' ~ rs'
        )
    lem-final ss [] ls-halt with preserve ss
    lem-final ss [] ls-halt | inj₁ (ls-halt' , rs-halt)
      = _ , [] , rs-halt , ss
    lem-final ss [] ls-halt | inj₂ (ls' , rs' , ss' , (_ , lx , lxs) , (_ , rx , rxs))
      = ⊥-elim (L.final-nontransitional ls-halt lx)
    lem-final ss (lx ∷ lxs) ls'-halt with preserve ss
    lem-final ss (lx ∷ lxs) ls'-halt | inj₁ (ls-halt , rs-halt)
      = ⊥-elim (L.final-nontransitional ls-halt lx)
    lem-final ss (lx ∷ lxs) ls'-halt | inj₂ (ls' , rs' , ss' , (_ , lx' , lxs') , (_ , rx' , rxs'))
      with L.deterministic lx lx'
    ... | refl with lem-final-helper ss' lxs' lxs (prefix lxs ls'-halt lxs') ls'-halt
    ... | rs'' , rxs , rhalt , bis = rs'' , (rx' ∷ (rxs' R.++ rxs)) , rhalt , bis


module Theorems
  {lState rState : Set}
  (lSystem : System lState)
  (rSystem : System rState)
  (_~_ : lState → rState → Set)
  (preserve : {ls : lState}{rs : rState}
    → ls ~ rs
    → (System.Final lSystem ls × System.Final rSystem rs)
      ⊎
      ∃[ ls' ]
      ∃[ rs' ](
        (ls' ~ rs') ×
        System._−→+_ lSystem ls ls' ×
        System._−→+_ rSystem rs rs'))
  where
  
  module L where
    open System lSystem public
    
  module R where
    open System rSystem public
    
  thm-final-LR : ∀ {ls rs}
    → (ss : ls ~ rs)
    → ∀ {ls'}
    → ls L.−→* ls'
    → L.Final ls'
    → ∃[ rs' ](
      rs R.−→* rs' ×
      R.Final rs' ×
      ls' ~ rs'
    )
  thm-final-LR = Lemmas.lem-final lSystem rSystem _~_ preserve

  preserve' : {rs : rState}{ls : lState}
    → ls ~ rs
    → (System.Final rSystem rs × System.Final lSystem ls)
      ⊎
      ∃[ rs' ]
      ∃[ ls' ](
        (ls' ~ rs') ×
        System._−→+_ rSystem rs rs' ×
        System._−→+_ lSystem ls ls')
  preserve' ss with preserve ss
  preserve' ss | inj₁ (lh , rh) = inj₁ (rh , lh)
  preserve' ss | inj₂ (ls' , rs' , ss' , lxs , rxs)
    = inj₂ (rs' , ls' , ss' , rxs , lxs)

  thm-final-RL : ∀ {ls rs}
    → (ss : ls ~ rs)
    → ∀ {rs'}
    → rs R.−→* rs'
    → R.Final rs'
    → ∃[ ls' ](
      ls L.−→* ls' ×
      L.Final ls' ×
      ls' ~ rs'
    )
  thm-final-RL
    = Lemmas.lem-final rSystem lSystem (λ r l → l ~ r) preserve'

open Theorems public
