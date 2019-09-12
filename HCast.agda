module HCast (Label : Set) where
open import Types
open import Variables
open import Terms Label

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

data Head (P : PreType) : Type → Set where
  ⁇ : (l : Label) → Head P ⋆
  ε : Head P (` P)

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

mutual
  seq : ∀ {T1 T2 T3 T4}
    → T2 ≡ T3 ⊎ Label
    → Cast T1 T2
    → Cast T3 T4
  ----------------
    → Cast T1 T4
  seq ℓ id⋆ id⋆
    = id⋆
  seq ℓ id⋆ (↷ ε r) with ℓ
  seq ℓ id⋆ (↷ ε r) | inj₁ ()
  seq ℓ id⋆ (↷ ε r) | inj₂ l
    = ↷ (⁇ l) r
  seq ℓ id⋆ (↷ (⁇ l) r)
    = ↷ (⁇ l) r
  seq ℓ (↷ h r) c2 = ↷ h (seq' ℓ r c2)

  seq' : ∀ {P T2 T3 T4}
    → T2 ≡ T3 ⊎ Label
    → Rest P T2
    → Cast T3 T4
  ----------------
    → Rest P T4
  seq' ℓ (rest b (fail l)) c2
    = rest b (fail l)
  seq' ℓ (rest b (last t)) id⋆
    = rest b (last ‼)
  seq' ℓ (rest b (last t)) (↷ (⁇ l) r)
    = ext-rest (inj₂ l) b r
  seq' ℓ (rest b (last t)) (↷ ε r) with ℓ
  seq' ℓ (rest b (last ε)) (↷ ε r) | inj₁ refl
    = ext-rest (inj₁ refl) b r
  seq' ℓ (rest b (last t)) (↷ ε r) | inj₂ l
    = ext-rest (inj₂ l) b r

  ext-rest : ∀ {P1 P2 P3 T1}
    → P2 ≡ P3 ⊎ Label
    → Body P1 P2
    → Rest P3 T1
  ----------------
    → Rest P1 T1
  ext-rest {P2 = P2} {P3 = P3} ℓ b (rest b₁ t) with (` P2) ⌣? (` P3)
  ext-rest ℓ U (rest U t) | yes ⌣U
    = rest U t
  ext-rest ℓ (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒ with ℓ
  ext-rest ℓ (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒ | inj₁ refl
    = rest ((seq (inj₁ refl) c₃ c₁) ⇒ (seq (inj₁ refl) c₂ c₄)) t
  ext-rest ℓ (c₁ ⇒ c₂) (rest (c₃ ⇒ c₄) t) | yes ⌣⇒ | inj₂ l
    = rest ((seq (inj₂ l) c₃ c₁) ⇒ (seq (inj₂ l) c₂ c₄)) t
  ext-rest ℓ (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗ with ℓ
  ext-rest ℓ (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗ | inj₁ refl
    = rest ((seq (inj₁ refl) c₁ c₃) ⊗ (seq (inj₁ refl) c₂ c₄)) t
  ext-rest ℓ (c₁ ⊗ c₂) (rest (c₃ ⊗ c₄) t) | yes ⌣⊗ | inj₂ l
    = rest ((seq (inj₂ l) c₁ c₃) ⊗ (seq (inj₂ l) c₂ c₄)) t
  ext-rest ℓ (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕ with ℓ
  ext-rest ℓ (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕ | inj₁ refl
    = rest ((seq (inj₁ refl) c₁ c₃) ⊕ (seq (inj₁ refl) c₂ c₄)) t
  ext-rest ℓ (c₁ ⊕ c₂) (rest (c₃ ⊕ c₄) t) | yes ⌣⊕ | inj₂ l
    = rest ((seq (inj₂ l) c₁ c₃) ⊕ (seq (inj₂ l) c₂ c₄)) t
  ext-rest ℓ b (rest b₁ t) | no ¬p with ℓ
  ext-rest {P2 = _} {_} ℓ b (rest b₁ t) | no ¬p | inj₁ refl = ⊥-elim (¬p (⌣refl _))
  ext-rest {P2 = _} {_} ℓ b (rest b₁ t) | no ¬p | inj₂ l = rest b (fail l)

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
mk-cast l T1 T2 = seq (inj₂ l) (mk-id T1) (mk-id T2)

mk-seq : ∀ {T1 T2 T3} → Cast T1 T2 → Cast T2 T3 → Cast T1 T3
mk-seq c1 c2 = seq (inj₁ refl) c1 c2




open import Vals Label Cast

apply-tail : ∀ {P T} → Tail P T → Val (` P) → CastResult T
apply-tail (fail l) v = fail l
apply-tail (last ‼) v = succ (inj _ v)
apply-tail (last ε) v = succ v

mutual
  apply-body : ∀ {P Q} → Body P Q → Val (` P) → CastResult (` Q)
  apply-body U sole
    = succ sole
  apply-body (c₁ ⇒ c₂) (fun E c₃ b c₄)
    = succ (fun E (mk-seq c₁ c₃) b (mk-seq c₄ c₂))
  apply-body (c₁ ⊗ c₂) (cons v₁ v₂)
    = apply-cast c₁ v₁ >>= λ u₁ →
      apply-cast c₂ v₂ >>= λ u₂ →
      succ (cons u₁ u₂)
  apply-body (c₁ ⊕ c₂) (inl v)
    = apply-cast c₁ v >>= λ u →
      succ (inl u)
  apply-body (c₁ ⊕ c₂) (inr v)
    = apply-cast c₂ v >>= λ u →
      succ (inr u)
      
  apply-rest : ∀ {P T} → Rest P T → Val (` P) → CastResult T
  apply-rest (rest b t) v
    = apply-body b v >>= λ u →
      apply-tail t u
  
  apply-cast : ∀ {T1 T2} → Cast T1 T2 → Val T1 → CastResult T2
  apply-cast id⋆ v
    = succ v
  apply-cast (↷ (⁇ l) r) (inj P v)
    = apply-rest (ext-rest (inj₂ l) (mk-id-body P) r) v
  apply-cast (↷ ε r) v
    = apply-rest r v

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

lem-id : ∀ T
  → (v : Val T)  
  -----------------------------
  → apply-cast (mk-id T) v ≡ succ v
lem-id ⋆ v = refl
lem-id (` U) sole = refl
lem-id (` (T₁ ⇒ T₂)) (fun env c₁ b c₂) rewrite seq-id-l c₁ | seq-id-r c₂ = refl
lem-id (` (T₁ ⊗ T₂)) (cons v₁ v₂) rewrite lem-id T₁ v₁ | lem-id T₂ v₂ = refl
lem-id (` (T₁ ⊕ T₂)) (inl v) rewrite lem-id T₁ v = refl
lem-id (` (T₁ ⊕ T₂)) (inr v) rewrite lem-id T₂ v = refl

lem-seq : ∀ {T1 T2 T3}
  → (c1 : Cast T1 T2)
  → (c2 : Cast T2 T3)
  → (v : Val T1)
  --------------------
  → apply-cast (mk-seq c1 c2) v ≡ apply-cast c1 v >>= λ u → apply-cast c2 u
lem-seq id⋆ id⋆ v = refl
lem-seq id⋆ (↷ (⁇ l) r) v = refl
lem-seq (↷ (⁇ l) (rest b t)) c2 (inj _ v) = {!!}
lem-seq (↷ ε (rest b (fail l))) c2 v with apply-body b v
lem-seq (↷ ε (rest b (fail l))) c2 v | succ v₁ = refl
lem-seq (↷ ε (rest b (fail l))) c2 v | fail l₁ = refl
lem-seq (↷ ε (rest b (last ‼))) id⋆ v = sym (>>=-succ _)
lem-seq (↷ ε (rest b (last ‼))) (↷ (⁇ l) (rest b₁ t)) v = {!!}
lem-seq (↷ ε (rest b (last ε))) (↷ ε (rest {P = P} b₁ t)) v with (` P) ⌣? (` P)
lem-seq (↷ ε (rest U (last ε))) (↷ ε (rest {_} U t)) sole | yes ⌣U = refl
lem-seq (↷ ε (rest (c₁ ⇒ c₂) (last ε))) (↷ ε (rest {_} (c₃ ⇒ c₄) t)) (fun env c₅ b c₆) | yes ⌣⇒ = {!!}
lem-seq (↷ ε (rest (c₁ ⊗ c₂) (last ε))) (↷ ε (rest {_} (c₃ ⊗ c₄) t)) (cons v v₁) | yes ⌣⊗
  rewrite lem-seq c₁ c₃ v
        | lem-seq c₂ c₄ v₁
        | >>=-succ (apply-cast c₁ v >>= (λ u₁ → apply-cast c₂ v₁ >>= (λ u₂ → succ (cons u₁ u₂))))
  = {!!}
lem-seq (↷ ε (rest b (last ε))) (↷ ε (rest {_} b₁ t)) v | yes ⌣⊕ = {!!}
lem-seq (↷ ε (rest b (last ε))) (↷ ε (rest {_} b₁ t)) v | no ¬p = ⊥-elim (¬p (⌣refl _))

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
  rewrite sym (>>=-succ (apply-body (mk-id-body P) v))
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
  rewrite sym (>>=-succ (apply-body (mk-id-body P) v))
        | lem-id (` P) v
  = refl

lem-cast-proj : ∀ l P P₁ v
  → apply-cast (mk-cast l ⋆ (` P)) (inj P₁ v) ≡ apply-cast (mk-cast l (` P₁) (` P)) v
lem-cast-proj l P P₁ v with (` P₁) ⌣? (` P)
lem-cast-proj l .U .U v | yes ⌣U = refl
lem-cast-proj l .(_ ⇒ _) .(_ ⇒ _) v | yes ⌣⇒ = refl
lem-cast-proj l .(_ ⊗ _) .(_ ⊗ _) v | yes ⌣⊗ = refl
lem-cast-proj l .(_ ⊕ _) .(_ ⊕ _) v | yes ⌣⊕ = refl
lem-cast-proj l P P₁ v | no ¬p = refl

lem-cast-U : 
    (l : Label)
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

lem-cast-⊗ : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T11)
  → (v₁ : Val T12)
  → apply-cast (mk-cast l (` (T11 ⊗ T12)) (` (T21 ⊗ T22))) (cons v v₁) ≡
    apply-cast (mk-cast l T11 T21) v >>= λ u →
    apply-cast (mk-cast l T12 T22) v₁ >>= λ u₁ →
    succ (cons u u₁)
lem-cast-⊗ T11 T12 T21 T22 l v v₁
  = >>=-succ _
    
lem-cast-⊕-l : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T11)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inl v) ≡
    apply-cast (mk-cast l T11 T21) v >>= λ u →
    succ (inl u)
lem-cast-⊕-l T11 T12 T21 T22 l v
  = >>=-succ _

lem-cast-⊕-r : ∀ T11 T12 T21 T22
  → (l : Label)
  → (v : Val T12)
  → apply-cast (mk-cast l (` (T11 ⊕ T12)) (` (T21 ⊕ T22))) (inr v) ≡
    apply-cast (mk-cast l T12 T22) v >>= λ u →
    succ (inr u)
lem-cast-⊕-r T11 T12 T21 T22 l v
  = >>=-succ _
