module CEKcc.HCast (Label : Set) where
open import Types
open import Variables
open import Terms Label
open import CEKcc.CastRep Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)

data Head : PreType → Type → Set where
  ⁇ : ∀ {P} → (l : Label) → Head P ⋆
  ε : ∀ {P} → Head P (` P)

data Last (P : PreType) : Type → Set where
  ‼ : Last P ⋆
  ε : Last P (` P)

data Tail (P : PreType) : Type → Set where
  fail : ∀ {T}
    → (l : Label)
    → Tail P T
  last : ∀ {T}
    → (t : Last P T)
    → Tail P T

mutual
  data Cast : Type → Type → Set where
    id⋆ : Cast ⋆ ⋆
    ↷ : ∀ {A P B}
      → (h : Head P A)
      → (r : Rest P B)
      → Cast A B

  data Rest : PreType → Type → Set where
    rest : ∀ {P Q B}
      → (b : Body P Q)
      → (t : Tail Q B)
      → Rest P B
    
  data Body : PreType → PreType → Set where
    U : Body U U
    _⇒_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S2 S1) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⇒ T1) (S2 ⇒ T2)
    _⊗_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⊗ T1) (S2 ⊗ T2)
    _⊕_ : ∀ {S1 S2 T1 T2} →
      (c₁ : Cast S1 S2) →
      (c₂ : Cast T1 T2) →
      Body (S1 ⊕ T1) (S2 ⊕ T2)

GapP : PreType → PreType → Set
GapP P1 P2 = P1 ≡ P2 ⊎ Label

GapT : Type → Type → Set
GapT T1 T2 = T1 ≡ T2 ⊎ Label

ℓ-dom : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T3 T1
ℓ-dom (inj₁ refl) = inj₁ refl
ℓ-dom (inj₂ l) = inj₂ l

ℓ-cod : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⇒ T2) (T3 ⇒ T4)
  → GapT T2 T4
ℓ-cod (inj₁ refl) = inj₁ refl
ℓ-cod (inj₂ l) = inj₂ l

ℓ-car : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T1 T3
ℓ-car (inj₁ refl) = inj₁ refl
ℓ-car (inj₂ l) = inj₂ l

ℓ-cdr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊗ T2) (T3 ⊗ T4)
  → GapT T2 T4
ℓ-cdr (inj₁ refl) = inj₁ refl
ℓ-cdr (inj₂ l) = inj₂ l

ℓ-inl : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊕ T2) (T3 ⊕ T4)
  → GapT T1 T3
ℓ-inl (inj₁ refl) = inj₁ refl
ℓ-inl (inj₂ l) = inj₂ l

ℓ-inr : ∀ {T1 T2 T3 T4}
  → GapP (T1 ⊕ T2) (T3 ⊕ T4)
  → GapT T2 T4
ℓ-inr (inj₁ refl) = inj₁ refl
ℓ-inr (inj₂ l) = inj₂ l

mutual
  seq : ∀ {T1 T2 T3 T4}
    → Cast T1 T2
    → T2 ≡ T3 ⊎ Label
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq id⋆ ℓ id⋆ = id⋆
  seq id⋆ ℓ (↷ (⁇ l) r) = ↷ (⁇ l) r
  seq id⋆ ℓ (↷ ε r) with ℓ
  seq id⋆ ℓ (↷ ε r) | inj₁ ()
  seq id⋆ ℓ (↷ ε r) | inj₂ l = ↷ (⁇ l) r
  seq (↷ h (rest b (fail l))) ℓ c2 = ↷ h (rest b (fail l))
  seq (↷ h (rest b (last t))) ℓ id⋆ = ↷ h (rest b (last ‼))
  seq (↷ h1 (rest b1 (last t1))) ℓ (↷ h2 r2) = ↷ h1 (seq-rest b1 t1 ℓ h2 r2)

  seq-rest : ∀ {P1 P2 P3 T1 T2 T3}
    → (b1 : Body P1 P2)
    → (t1 : Last P2 T1)
    → (ℓ : GapT T1 T2)
    → (h2 : Head P3 T2)
    → (r2 : Rest P3 T3)
    → Rest P1 T3
  seq-rest {P2 = P1} b1 t1 ℓ h2 (rest {P = P2} b2 t2) with (` P1) ⌣? (` P2)
  seq-rest {P2 = P1} b1 t1 ℓ h2 (rest {_} b2 t2) | yes p = rest (seq-m (link h2 ℓ t1) p b1 b2) t2
  seq-rest {P2 = P1} b1 t1 ℓ h2 (rest {_} b2 t2) | no ¬p with (link h2 ℓ t1)
  seq-rest b1 t1 ℓ h2 (rest b2 t2) | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-rest b1 t1 ℓ h2 (rest b2 t2) | no ¬p | inj₂ l = rest b1 (fail l)

  seq-m : ∀ {P1 P2 P3 P4}
    → P2 ≡ P3 ⊎ Label
    → (` P2) ⌣ (` P3)
    → Body P1 P2
    → Body P3 P4
    ---
    → Body P1 P4
  seq-m ℓ ⌣U U U = U
  seq-m ℓ ⌣⇒ (c₁ ⇒ c₂) (c₃ ⇒ c₄) = seq c₃ (ℓ-dom ℓ) c₁ ⇒ seq c₂ (ℓ-cod ℓ) c₄
  seq-m ℓ ⌣⊗ (c₁ ⊗ c₂) (c₃ ⊗ c₄) = seq c₁ (ℓ-car ℓ) c₃ ⊗ seq c₂ (ℓ-cdr ℓ) c₄
  seq-m ℓ ⌣⊕ (c₁ ⊕ c₂) (c₃ ⊕ c₄) = seq c₁ (ℓ-inl ℓ) c₃ ⊕ seq c₂ (ℓ-inr ℓ) c₄
  
  link : ∀ {Q P T1 T2}
    → (h : Head P T2)
    → (ℓ : T1 ≡ T2 ⊎ Label)
    → (t : Last Q T1)
    -----------------
    → Q ≡ P ⊎ Label
  link (⁇ l) ℓ t = inj₂ l
  link ε (inj₁ refl) ε = inj₁ refl
  link ε (inj₂ y) t = inj₂ y

mutual
  mk-id : ∀ T → Cast T T
  mk-id ⋆
    = id⋆
  mk-id (` P)
    = ↷ ε (rest (mk-id-body P) (last ε))

  mk-id-body : ∀ P → Body P P
  mk-id-body U
    = U
  mk-id-body (T₁ ⇒ T₂)
    = mk-id T₁ ⇒ mk-id T₂
  mk-id-body (T₁ ⊗ T₂)
    = mk-id T₁ ⊗ mk-id T₂
  mk-id-body (T₁ ⊕ T₂)
    = mk-id T₁ ⊕ mk-id T₂

mk-cast : Label → ∀ T1 T2 → Cast T1 T2
mk-cast l T1 T2 = seq (mk-id T1) (inj₂ l) (mk-id T2)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq c1 (inj₁ refl) c2

mutual
  seq-id-l : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq (mk-id T1) c ≡ c
  seq-id-l id⋆ = refl
  seq-id-l (↷ (⁇ l) r) = refl
  seq-id-l (↷ ε (rest U t)) = refl
  seq-id-l (↷ ε (rest (c₁ ⇒ c₂) t)) rewrite seq-id-r c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (rest (c₁ ⊗ c₂) t)) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  seq-id-l (↷ ε (rest (c₁ ⊕ c₂) t)) rewrite seq-id-l c₁ | seq-id-l c₂ = refl
  
  seq-id-r : ∀ {T1 T2} → (c : Cast T1 T2) → mk-seq c (mk-id T2) ≡ c
  seq-id-r id⋆ = refl
  seq-id-r (↷ h (rest b (fail l))) = refl
  seq-id-r (↷ h (rest b (last ‼))) = refl
  seq-id-r (↷ h (rest U (last ε))) = refl
  seq-id-r (↷ h (rest (c₁ ⇒ c₂) (last ε))) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (rest (c₁ ⊗ c₂) (last ε))) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  seq-id-r (↷ h (rest (c₁ ⊕ c₂) (last ε))) rewrite seq-id-r c₁ | seq-id-r c₂ = refl

seq-id⋆-l : ∀ {T}
  → (ℓ : ⋆ ≡ ⋆ ⊎ Label)
  → (c : Cast ⋆ T) → seq id⋆ ℓ c ≡ c
seq-id⋆-l (inj₁ refl) id⋆ = refl
seq-id⋆-l (inj₁ refl) (↷ (⁇ l) r) = refl
seq-id⋆-l (inj₂ y) id⋆ = refl
seq-id⋆-l (inj₂ y) (↷ (⁇ l) r) = refl


seq-id⋆-id⋆ : ∀ ℓ
  → seq id⋆ ℓ id⋆ ≡ id⋆
seq-id⋆-id⋆ (inj₁ refl) = refl
seq-id⋆-id⋆ (inj₂ y) = refl

mutual
  seq-m-assoc : ∀ {P1 P2 P3 P4 P5 P6}
    → (b1 : Body P1 P2)
    → (ℓ1 : GapP P2 P3)
    → (p1 : (` P2) ⌣ (` P3))
    → (b2 : Body P3 P4)
    → (ℓ2 : GapP P4 P5)
    → (p2 : (` P4) ⌣ (` P5))
    → (b3 : Body P5 P6)
    ---
    → seq-m ℓ2 p2 (seq-m ℓ1 p1 b1 b2) b3
      ≡
      seq-m ℓ1 p1 b1 (seq-m ℓ2 p2 b2 b3)
  seq-m-assoc U ℓ1 ⌣U U ℓ2 ⌣U U = refl
  seq-m-assoc (c₁ ⇒ c₂) ℓ1 ⌣⇒ (c₃ ⇒ c₄) ℓ2 ⌣⇒ (c₅ ⇒ c₆) = cong₂ (λ x y → x ⇒ y) (sym (seq-assoc c₅ (ℓ-dom ℓ2) c₃ (ℓ-dom ℓ1) c₁)) (seq-assoc c₂ (ℓ-cod ℓ1) c₄ (ℓ-cod ℓ2) c₆)
  seq-m-assoc (c₁ ⊗ c₂) ℓ1 ⌣⊗ (c₃ ⊗ c₄) ℓ2 ⌣⊗ (c₅ ⊗ c₆) = cong₂ (λ x y → x ⊗ y) (seq-assoc c₁ (ℓ-car ℓ1) c₃ (ℓ-car ℓ2) c₅) (seq-assoc c₂ (ℓ-cdr ℓ1) c₄ (ℓ-cdr ℓ2) c₆)
  seq-m-assoc (c₁ ⊕ c₂) ℓ1 ⌣⊕ (c₃ ⊕ c₄) ℓ2 ⌣⊕ (c₅ ⊕ c₆) = cong₂ (λ x y → x ⊕ y) (seq-assoc c₁ (ℓ-inl ℓ1) c₃ (ℓ-inl ℓ2) c₅) (seq-assoc c₂ (ℓ-inr ℓ1) c₄ (ℓ-inr ℓ2) c₆)
  
  seq-assoc : ∀ {T1 T2 T3 T4 T5 T6}
    → (c1 : Cast T1 T2)
    → (ℓ1 : T2 ≡ T3 ⊎ Label)
    → (c2 : Cast T3 T4)
    → (ℓ2 : T4 ≡ T5 ⊎ Label)
    → (c3 : Cast T5 T6)
    → seq (seq c1 ℓ1 c2) ℓ2 c3 ≡ seq c1 ℓ1 (seq c2 ℓ2 c3)
  seq-assoc id⋆ ℓ1 id⋆ ℓ2 id⋆ = refl
  seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ (⁇ l) r) = refl
  seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) with ℓ2
  seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) | inj₁ ()
  seq-assoc id⋆ ℓ1 id⋆ ℓ2 (↷ ε r) | inj₂ y = refl
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest b (fail l₁))) ℓ2 c3 = refl
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest b (last t))) ℓ2 id⋆ = refl
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {P = P2} b₁ t₁)) with (` P1) ⌣? (` P2)
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | yes p = refl
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p with link h ℓ2 t
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = _} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-assoc id⋆ ℓ1 (↷ (⁇ l) (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | no ¬p | inj₂ y = refl
  seq-assoc id⋆ ℓ1 (↷ ε (rest b t)) ℓ2 c3 with ℓ1
  seq-assoc id⋆ ℓ1 (↷ ε (rest b t)) ℓ2 c3 | inj₁ ()
  seq-assoc id⋆ ℓ1 (↷ ε (rest b (fail l))) ℓ2 c3 | inj₂ y = refl
  seq-assoc id⋆ ℓ1 (↷ ε (rest b (last t))) ℓ2 id⋆ | inj₂ y = refl
  seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {P = P2} b₁ t₁)) | inj₂ y with (` P1) ⌣? (` P2)
  seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | yes p = refl
  seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p with link h ℓ2 t
  seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = _} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-assoc id⋆ ℓ1 (↷ ε (rest {Q = P1} b (last t))) ℓ2 (↷ h (rest {_} b₁ t₁)) | inj₂ y | no ¬p | inj₂ y₁ = refl
  seq-assoc (↷ h (rest b (fail l))) ℓ1 c2 ℓ2 c3 = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 id⋆ = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {P = P2} b₁ t₁)) with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {_} b₁ t₁)) | yes p = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ (⁇ l) (rest {_} b₁ t₁)) | no ¬p = refl
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) with ℓ2
  seq-assoc (↷ h (rest b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₁ ()
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest {P = P2} b₁ t₁)) | inj₂ y with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₂ y | yes p = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 id⋆ ℓ2 (↷ ε (rest b₁ t₁)) | inj₂ y | no ¬p = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P = P2} b₁ (fail l))) ℓ2 c3 with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | yes p = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p with link h₁ ℓ1 t
  seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (fail l))) ℓ2 c3 | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P = P2} b₁ (last t₁))) ℓ2 id⋆ with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | yes p = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p with link h₁ ℓ1 t
  seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p | inj₁ refl =  ⊥-elim (¬p (⌣refl (` _)))
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} b₁ (last t₁))) ℓ2 id⋆ | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {Q = P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P = P4} b₂ t₂)) with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | yes p with (` P3) ⌣? (` P4)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | yes p₁ with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | yes p | yes p₁ | yes p₂
    rewrite ⌣unique p p₂ = cong (λ b → ↷ h (rest b t₂)) (seq-m-assoc b (link h₁ ℓ1 t) p₂ b₁ (link h₂ ℓ2 t₁) p₁ b₂)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | yes p₁ | no ¬p = ⊥-elim (¬p p)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | no ¬p with link h₂ ℓ2 t₁
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {_} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes p | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl (` _)))
  seq-assoc (↷ h (rest {Q = .U} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣U | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = .(_ ⇒ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⇒ | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊗ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⊗ | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = .(_ ⊕ _)} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | yes ⌣⊕ | no ¬p | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {P4} b₂ t₂)) | no ¬p with (` P3) ⌣? (` P4)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | yes p₁ = ⊥-elim (¬p p₁)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ with link h₁ ℓ1 t
  seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ | inj₁ refl = ⊥-elim (¬p₁ (⌣refl (` _)))
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | yes p | no ¬p₁ | inj₂ y = refl
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ with link h₂ ℓ2 t₁
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {_} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₁ refl = ⊥-elim (¬p₁ (⌣refl (` _)))
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {P2} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y with (` P1) ⌣? (` P2)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | yes p = ⊥-elim (¬p p)
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ with link h₁ ℓ1 t
  seq-assoc (↷ h (rest {Q = _} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ | inj₁ refl = ⊥-elim (¬p₂ (⌣refl (` _)))
  seq-assoc (↷ h (rest {Q = P1} b (last t))) ℓ1 (↷ h₁ (rest {_} {P3} b₁ (last t₁))) ℓ2 (↷ h₂ (rest {_} b₂ t₂)) | no ¬p | no ¬p₁ | inj₂ y | no ¬p₂ | inj₂ y₁ = refl 

open import CEKcc.Values Label Cast
  
module AlternativeApplyCast where
 
  apply-body : ∀ {P1 P2 P3}
    → P1 ≡ P2 ⊎ Label
    → Body P2 P3
    → Val (` P1)
    → CastResult (` P3)
  apply-body {P1} {P2} ℓ b v with (` P1) ⌣? (` P2)
  apply-body {.U} {.U} ℓ U sole | yes ⌣U = succ sole
  apply-body {.(_ ⇒ _)} {.(_ ⇒ _)} ℓ (c₃ ⇒ c₄) (fun env c₁ b₁ c₂) | yes ⌣⇒ = succ (fun env (seq c₃ (ℓ-dom ℓ) c₁) b₁ (seq c₂ (ℓ-cod ℓ) c₄))
  apply-body {.(_ ⊗ _)} {.(_ ⊗ _)} ℓ (c₃ ⊗ c₄) (cons v₁ c₁ v₂ c₂) | yes ⌣⊗ = succ (cons v₁ (seq c₁ (ℓ-car ℓ) c₃) v₂ (seq c₂ (ℓ-cdr ℓ) c₄))
  apply-body {.(_ ⊕ _)} {.(_ ⊕ _)} ℓ (c₃ ⊕ c₄) (inl v c) | yes ⌣⊕ = succ (inl v (seq c (ℓ-inl ℓ) c₃))
  apply-body {.(_ ⊕ _)} {.(_ ⊕ _)} ℓ (c₃ ⊕ c₄) (inr v c) | yes ⌣⊕ = succ (inr v (seq c (ℓ-inr ℓ) c₄))
  apply-body {P1} {.P1} (inj₁ refl) b v | no ¬p = ⊥-elim (¬p (⌣refl (` P1)))
  apply-body {P1} {P2} (inj₂ l) b v | no ¬p = fail l
  
  apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
  apply-tail (fail l) v = fail l
  apply-tail (last ‼) v = succ (inj _ v)
  apply-tail (last ε) v = succ v

  apply-rest : ∀ {P1 P2 T}
    → GapP P1 P2
    → Rest P2 T
    → Val (` P1)
    ---
    → CastResult T
  apply-rest ℓ (rest b t) v = apply-body ℓ b v >>= apply-tail t

  apply-cast : ∀ {T1 T2}
    → Cast T1 T2
    → Val T1
    ---
    → CastResult T2
  apply-cast id⋆ v = succ v
  apply-cast (↷ (⁇ l) r) (inj _ v) = apply-rest (inj₂ l) r v
  apply-cast (↷ ε r) v = apply-rest (inj₁ refl) r v

open AlternativeApplyCast public

mutual
  lem-id-body : ∀ P
    → (v : Val (` P))  
    -----------------------------
    → apply-body (inj₁ refl) (mk-id-body P) v ≡ succ v
  lem-id-body U sole = refl
  lem-id-body (T₁ ⇒ T₂) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊗ T₂) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  lem-id-body (T₁ ⊕ T₂) (inl v c) rewrite seq-id-r c = refl
  lem-id-body (T₁ ⊕ T₂) (inr v c) rewrite seq-id-r c = refl

  lem-id : ∀ T
    → (v : Val T)  
    -----------------------------
    → apply-cast (mk-id T) v ≡ succ v
  lem-id ⋆ v = refl
  lem-id (` U) sole = refl
  lem-id (` (T₁ ⇒ T₂)) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
  lem-id (` (T₁ ⊗ T₂)) (cons v c₁ v₁ c₂) rewrite seq-id-r c₁ | seq-id-r c₂ = refl
  lem-id (` (T₁ ⊕ T₂)) (inl v c) rewrite seq-id-r c = refl
  lem-id (` (T₁ ⊕ T₂)) (inr v c) rewrite seq-id-r c = refl

lem-seq-fail : ∀ {P1 P2 P3 T1 T2}
  → (v : Val (` P1))
  → (ℓ : GapP P1 P2)
  → (b : Body P2 P3)
  → (l : Label)
  → (f : Val T1 → CastResult T2)
  ---
  → (apply-body ℓ b v >>= (λ v → fail l)) ≡
    ((apply-body ℓ b v >>= (λ v → fail l)) >>= f)
lem-seq-fail v ℓ b l f with apply-body ℓ b v
lem-seq-fail v ℓ b l f | succ v₁ = refl
lem-seq-fail v ℓ b l f | fail l₁ = refl

lem-apply-body-refl : ∀ {P1 P2}
  → (v : Val (` P1))
  → (b : Body P1 P2)
  → ∃[ u ](apply-body (inj₁ refl) b v ≡ succ u)
lem-apply-body-refl {P1} v b with (` P1) ⌣? (` P1)
lem-apply-body-refl {.U} sole U | yes ⌣U = sole , refl
lem-apply-body-refl {.(_ ⇒ _)} (fun env c₁ b₁ c₂) (c₃ ⇒ c₄) | yes ⌣⇒
  = (fun env (seq c₃ (inj₁ refl) c₁) b₁ (seq c₂ (inj₁ refl) c₄)) , refl
lem-apply-body-refl {.(_ ⊗ _)} (cons v c₁ v₁ c₂) (c₃ ⊗ c₄) | yes ⌣⊗
  = cons v (seq c₁ (inj₁ refl) c₃) v₁ (seq c₂ (inj₁ refl) c₄) , refl
lem-apply-body-refl {.(_ ⊕ _)} (inl v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inl v (seq c (inj₁ refl) c₁) , refl
lem-apply-body-refl {.(_ ⊕ _)} (inr v c) (c₁ ⊕ c₂) | yes ⌣⊕ = inr v (seq c (inj₁ refl) c₂) , refl
lem-apply-body-refl {P1} v b | no ¬p = ⊥-elim (¬p (⌣refl _))

lem-apply-body-⌣ : ∀ {P0 P1 P2}
  → (v : Val (` P0))
  → (ℓ : GapP P0 P1)
  → (p : (` P0) ⌣ (` P1))
  → (b : Body P1 P2)
  → ∃[ u ](apply-body ℓ b v ≡ succ u)
lem-apply-body-⌣ {.U} {.U} sole ℓ ⌣U U = sole , refl
lem-apply-body-⌣ {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b₁ c₂) ℓ ⌣⇒ (c₃ ⇒ c₄) = (fun env (seq c₃ _ c₁) b₁ (seq c₂ _ c₄)) , refl
lem-apply-body-⌣ {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ ⌣⊗ (c₃ ⊗ c₄) = cons v (seq c₁ _ c₃) v₁ (seq c₂ _ c₄) , refl
lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inl v (seq c _ c₁) , refl
lem-apply-body-⌣ {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ ⌣⊕ (c₁ ⊕ c₂) = inr v (seq c _ c₂) , refl

lem-seq' : ∀ {P1 P2 P3 P4 P5 T1 T2}
  → (v : Val (` P1))
  → (ℓ : GapP P1 P2)
  → (b1 : Body P2 P3)
  → (t1 : Last P3 T1)
  → (h2 : Head P4 T1)
  → (b2 : Body P4 P5)
  → (t2 : Tail P5 T2)
  → apply-rest ℓ
      (seq-rest b1 t1 (inj₁ refl) h2 (rest b2 t2))
      v
    ≡
    ((apply-body ℓ b1 v >>= apply-tail (last t1)) >>=
      apply-cast (↷ h2 (rest b2 t2)))
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 with (` P3) ⌣? (` P4)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p with t1 | h2
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l with (` P1) ⌣? (` P2)
lem-seq' {.U} {.U} {.U} {.U} sole ℓ U t1 h2 U t2 | yes ⌣U | ‼ | ⁇ l | yes ⌣U = refl
lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ‼ | ⁇ l | yes ⌣⇒
  rewrite seq-assoc c₅ (inj₂ l) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₂ l) c₆
  = refl
lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ‼ | ⁇ l | yes ⌣⊗
  rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₂ l) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₂ l) c₆
  = refl
lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
  rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₂ l) c₃
  = refl
lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ‼ | ⁇ l | yes ⌣⊕
  rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₂ l) c₄
  = refl
lem-seq' {P1} {.P1} {P3} {P4} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
lem-seq' {P1} {P2} {P3} {P4} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ‼ | ⁇ l | no ¬p = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | yes p | ε | ε with (` P1) ⌣? (` P2)
lem-seq' {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} {.(_ ⇒ _)} (fun env c₁ b c₂) ℓ (c₃ ⇒ c₄) t1 h2 (c₅ ⇒ c₆) t2 | yes ⌣⇒ | ε | ε | yes ⌣⇒
  rewrite seq-assoc c₅ (inj₁ refl) c₃ (ℓ-dom ℓ) c₁ | seq-assoc c₂ (ℓ-cod ℓ) c₄ (inj₁ refl) c₆
  = refl
lem-seq' {.U} {.U} {.U} {.U} sole ℓ U t1 h2 U t2 | yes ⌣U | ε | ε | yes ⌣U = refl
lem-seq' {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} {.(_ ⊗ _)} (cons v c₁ v₁ c₂) ℓ (c₃ ⊗ c₄) t1 h2 (c₅ ⊗ c₆) t2 | yes ⌣⊗ | ε | ε | yes ⌣⊗
  rewrite seq-assoc c₁ (ℓ-car ℓ) c₃ (inj₁ refl) c₅ | seq-assoc c₂ (ℓ-cdr ℓ) c₄ (inj₁ refl) c₆
  = refl
lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inl v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
  rewrite seq-assoc c (ℓ-inl ℓ) c₁ (inj₁ refl) c₃
  = refl
lem-seq' {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} {.(_ ⊕ _)} (inr v c) ℓ (c₁ ⊕ c₂) t1 h2 (c₃ ⊕ c₄) t2 | yes ⌣⊕ | ε | ε | yes ⌣⊕
  rewrite seq-assoc c (ℓ-inr ℓ) c₂ (inj₁ refl) c₄
  = refl
lem-seq' {P1} {.P1} {P3} {P3} v (inj₁ refl) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = (⊥-elim (¬p (⌣refl (` P1))))
lem-seq' {P1} {P2} {P3} {P3} v (inj₂ y) b1 t1 h2 b2 t2 | yes p | ε | ε | no ¬p = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p with t1 | h2
... | ε | ε = (⊥-elim (¬p (⌣refl (` P3))))
... | ‼ | ⁇ l with apply-body ℓ b1 v
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ with (` P3) ⌣? (` P4)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ | yes p = ⊥-elim (¬p p)
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | succ v₁ | no ¬p₁ = refl
lem-seq' {P1} {P2} {P3} {P4} v ℓ b1 t1 h2 b2 t2 | no ¬p | ‼ | ⁇ l | fail l₁ = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id⋆ id⋆ v = refl
lem-seq id⋆ (↷ (⁇ l) r) v = refl
lem-seq (↷ h (rest b (last ‼))) id⋆ v = sym (>>=-succ _)
lem-seq (↷ (⁇ l₁) (rest b (fail l))) c2 (inj P v) = lem-seq-fail v (inj₂ l₁) b l _
lem-seq (↷ ε (rest b (fail l))) c2 v = lem-seq-fail v _ b l _
lem-seq (↷ (⁇ l) (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) (inj P v) = lem-seq' v (inj₂ l) b t h₁ b₁ t₁
lem-seq (↷ ε (rest {Q = P1} b (last t))) (↷ h₁ (rest {_} b₁ t₁)) v = lem-seq' v (inj₁ refl) b t h₁ b₁ t₁

lem-cast-¬⌣ : ∀ {T1 T2}
  → (l : Label)
  → ¬ (T1 ⌣ T2)
  → (v : Val T1)
  → apply-cast (mk-cast l T1 T2) v ≡ fail l
lem-cast-¬⌣ {⋆} {⋆} l ¬p v = ⊥-elim (¬p ⋆⌣⋆)
lem-cast-¬⌣ {⋆} {` P} l ¬p v = ⊥-elim (¬p (⋆⌣P P))
lem-cast-¬⌣ {` P} {⋆} l ¬p v = ⊥-elim (¬p (P⌣⋆ P))
lem-cast-¬⌣ {` P} {` P₁} l ¬p v with (` P) ⌣? (` P₁)
lem-cast-¬⌣ {` P} {` P₁} l ¬p v | yes p = ⊥-elim (¬p p)
lem-cast-¬⌣ {` P} {` P₁} l ¬p v | no ¬p₁
  rewrite sym (>>=-succ (apply-body (inj₁ refl) (mk-id-body P) v))
        | lem-id (` P) v
  = refl

lem-cast-id⋆ : ∀ l
  → (v : Val ⋆)
  → apply-cast (mk-cast l ⋆ ⋆) v ≡ succ v
lem-cast-id⋆ l v = refl

lem-cast-inj : ∀ {P}
  → (l : Label)
  → (v : Val (` P))  
  → apply-cast (mk-cast l (` P) ⋆) v ≡ succ (inj P v)
lem-cast-inj {P} l v
  rewrite sym (>>=-succ (apply-body (inj₁ refl) (mk-id-body P) v))
        | lem-id (` P) v
  = refl

lem-seq2-id : ∀ {T1 T2 T3 T4}
  → (c1 : Cast T1 T2)
  → (ℓ : GapT T2 T3)
  → (c2 : Cast T3 T4)
  → seq c1 (inj₁ refl) (seq (mk-id T2) ℓ c2)
    ≡ seq c1 ℓ c2
lem-seq2-id c1 ℓ c2
  rewrite sym (seq-assoc c1 (inj₁ refl) (mk-id _) ℓ c2) | seq-id-r c1
  = refl

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v with (` P₁) ⌣? (` P)
lem-cast-proj l .U .U sole | yes ⌣U = refl
lem-cast-proj l (T1 ⇒ T2) (T3 ⇒ T4) (fun env c₁ b c₂) | yes ⌣⇒
  rewrite seq-id-l (seq (mk-id T1) (inj₂ l) c₁)
        | seq-assoc (mk-id T1) (inj₂ l) (mk-id T3) (inj₁ refl) c₁
        | seq-id-l c₁
        | seq-id-r (seq c₂ (inj₂ l) (mk-id T2))
        | sym (seq-assoc c₂ (inj₁ refl) (mk-id T4) (inj₂ l) (mk-id T2))
        | seq-id-r c₂
  = refl
lem-cast-proj l (T1 ⊗ T2) (T3 ⊗ T4) (cons v c₁ v₁ c₂) | yes ⌣⊗
  rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1) | lem-seq2-id c₂ (inj₂ l) (mk-id T2)
  = refl
lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inl v c₁) | yes ⌣⊕
  rewrite lem-seq2-id c₁ (inj₂ l) (mk-id T1)
  = refl
lem-cast-proj l (T1 ⊕ T2) (T3 ⊕ T4) (inr v c₂) | yes ⌣⊕
  rewrite lem-seq2-id c₂ (inj₂ l) (mk-id T2)
  = refl
lem-cast-proj l P P₁ v | no ¬p rewrite lem-id-body P₁ v = refl

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
cast-rep-monoid : Monoid cast-rep
cast-rep-monoid
  = record
    { lem-id-l = seq-id-l
    ; lem-id-r = seq-id-r
    ; lem-assoc = λ c1 c2 c3 → seq-assoc c1 _ c2 _ c3
    }

lem-cast-id-is-id : ∀ l T →
  mk-cast l T T ≡ mk-id T
lem-cast-id-is-id l ⋆ = refl
lem-cast-id-is-id l (` U) = refl
lem-cast-id-is-id l (` (T₁ ⇒ T₂))
  rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
lem-cast-id-is-id l (` (T₁ ⊗ T₂))
  rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl
lem-cast-id-is-id l (` (T₁ ⊕ T₂))
  rewrite lem-cast-id-is-id l T₁ | lem-cast-id-is-id l T₂ = refl

cast-rep-cast-id-is-id : CastIdIsId cast-rep
cast-rep-cast-id-is-id
  = record { lem-cast-id-is-id = lem-cast-id-is-id }
