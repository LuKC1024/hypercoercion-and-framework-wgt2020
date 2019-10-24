open import Types

module Terms
  (Label : Set)
  where

open import Variables

infix  4 _⊢_

data _⊢_ : Context → Type → Set where
                                
  -- kind of a constructor
               
  var : ∀ {Γ T}
    → Γ ∋ T
    --------
    → Γ ⊢ T
          
  -- constructors
     
  sole : ∀ {Γ}
    --------
    → Γ ⊢ ` U
            
  lam : ∀ {Γ}
    → ∀ T1 T2
    → Γ , T1 ⊢ T2
    -------------
    → Γ ⊢ ` T1 ⇒ T2
                 
  cons : ∀ {Γ T1 T2}
    → Γ ⊢ T1
    → Γ ⊢ T2
    ---------
    → Γ ⊢ ` T1 ⊗ T2
                 
  inl : ∀ {Γ T1 T2}
    → Γ ⊢ T1
    --------
    → Γ ⊢ ` T1 ⊕ T2
    
  inr : ∀ {Γ T1 T2}
    → Γ ⊢ T2
    --------
    → Γ ⊢ ` T1 ⊕ T2
                 
  -- eliminators
  
  app : ∀ {Γ T1 T2}
    → Γ ⊢ ` T1 ⇒ T2
    → Γ ⊢ T1
    --------
    → Γ ⊢ T2
          
  car : ∀ {Γ T1 T2}
    → Γ ⊢ ` T1 ⊗ T2
    ---------------
    → Γ ⊢ T1
    
  cdr : ∀ {Γ T1 T2}
    → Γ ⊢ ` T1 ⊗ T2
    ---------------
    → Γ ⊢ T2
          
  case : ∀ {Γ T1 T2 T3}
    → Γ ⊢ ` T1 ⊕ T2
    → Γ ⊢ ` T1 ⇒ T3
    → Γ ⊢ ` T2 ⇒ T3
    ----------------
    → Γ ⊢ T3
    
  -- kind of an eliminator
  
  cast : ∀ {Γ}
    → (l : Label)
    → (T1 T2 : Type)
    → Γ ⊢ T1
    --------
    → Γ ⊢ T2

  blame : ∀ {Γ T}
    → (l : Label)
    ---
    → Γ ⊢ T
