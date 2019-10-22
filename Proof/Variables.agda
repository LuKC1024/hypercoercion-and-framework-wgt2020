module Variables where

open import Types

data Context : Set where
  ∅   : Context
  _,_ : Context → Type → Context


infix  4 _∋_
infix  9 S_

data _∋_ : Context → Type → Set where

  Z : ∀ {Γ A}
      ----------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

extL :  Type → Context → Context
extL t ∅ = ∅ , t
extL t (C , x) = (extL t C) , x
