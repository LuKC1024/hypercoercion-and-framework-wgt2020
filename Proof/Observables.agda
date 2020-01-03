module Observables
  (Label : Set)
  where

open import Types

data Value : Type → Set where
  inj : Value ⋆
  
  fun : ∀ {T1 T2}
    ---
    → Value (` T1 ⇒ T2)
                  
  sole :
    --------
      Value (` U)
             
  cons : ∀ {T1 T2}
    ---------
    → Value (` T1 ⊗ T2)
                  
  inl : ∀ {T1 T2}
    --------
    → Value (` T1 ⊕ T2)
    
  inr : ∀ {T1 T2}
    --------
    → Value (` T1 ⊕ T2)
    
data Observable : Type → Set where
  blame : ∀ {T}
    → Label
    ---
    → Observable T
  done : ∀ {T}
    → Value T
    ---
    → Observable T
