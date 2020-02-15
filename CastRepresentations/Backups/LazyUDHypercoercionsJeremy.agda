module CastRepresentations.LazyUDHypercoercionsJeremy (Label : Set) where

  open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
  open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
      renaming (_,_ to ⟨_,_⟩)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Binary.PropositionalEquality
     using (_≡_;_≢_; refl; trans; sym; cong; cong₂; cong-app)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Negation using (contradiction)
     
  open import Types
  open import Variables

  data Inj : Type → Set
  data Proj : Type → Set
  data Middle : Type → Set
  data Cast : Type → Set

  data Cast where
    id★ : Cast (` * ⇒ *)
    _↷_,_ : ∀{A B C D} → Proj (` A ⇒ B) → Middle (` B ⇒ C) → Inj (` C ⇒ D)
          → Cast (` A ⇒ D)

  data Proj where
    𝜖 : ∀{A} → Proj (` A ⇒ A)
    ?? : Label → {H : PreType} {g : Ground H} → Proj (` * ⇒ (` H))

  data Middle where
    -- id : (ι : Base) → Middle ((` ι) ⇒ (` ι))
    B'  : Middle (` (` B) ⇒ (` B))
    _↣_ : ∀ {A B A' B'}
        → (c : Cast (` B ⇒ A)) → (d : Cast (` A' ⇒ B'))
          -----------------------------------------
        → Middle (` (` A ⇒ A') ⇒ (` B ⇒ B'))
    _×'_ : ∀ {A B A' B'}
      → (c : Cast (` A ⇒ B)) → (d : Cast (` A' ⇒ B'))
        -----------------------------------------
      → Middle (` (` A ⊗ A') ⇒ (` B ⊗ B'))

  data Inj where
    𝜖 : ∀{A} → Inj (` A ⇒ A)
    !! : ∀ {G} {g : Ground G} → Inj (` (` G) ⇒ *)
    cfail : ∀{A B} → Label → Inj (` A ⇒ B)

  _⨟_ : ∀{A B C} → (c : Cast (` A ⇒ B)) → (d : Cast (` B ⇒ C))
      → Cast (` A ⇒ C)

  _`⨟_ : ∀{A B C} → (c : Middle (` A ⇒ B)) → (d : Middle (` B ⇒ C))
       → Middle (` A ⇒ C)
  ((c ↣ d) `⨟ (c' ↣ d')) = (c' ⨟ c) ↣ (d ⨟ d')
  ((c ×' d) `⨟ (c' ×' d')) = (c ⨟ c') ×' (d ⨟ d')
  B' `⨟ B' = B'

  _⌣'_ : ∀{A B C D} → Middle (` A ⇒ B) → Middle (` C ⇒ D)
       → Dec (B ⌣ C)
  B' ⌣' B' = yes ⌣B
  B' ⌣' (c ↣ d) = no (λ ())
  B' ⌣' (c ×' d) = no (λ ())
  (c ↣ d) ⌣' B' = no (λ ())
  (c ↣ d) ⌣' (c₁ ↣ d₁) = yes ⌣⇒
  (c ↣ d) ⌣' (c₁ ×' d₁) = no (λ ())
  (c ×' d) ⌣' B' = no (λ ())
  (c ×' d) ⌣' (c₁ ↣ d₁) = no (λ ())
  (c ×' d) ⌣' (c₁ ×' d₁) = yes ⌣⊗

  c ⨟ id★ = c
  id★ ⨟ (p₂ ↷ m₂ , i₂) = (p₂ ↷ m₂ , i₂)
  (p₁ ↷ m₁ , 𝜖) ⨟ (𝜖 ↷ m₂ , i₂) = p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , (!! {G = C}{g = gC})) ⨟ ((?? ℓ) {H = D}{g = gD} ↷ m₂ , i₂)
      with _≟_ (` C) (` D) -- {gC}{gD}
  ... | no C≢D = p₁ ↷ m₁ , cfail ℓ
  ... | yes C≡D rewrite C≡D = p₁ ↷ (m₁ `⨟ m₂) , i₂
  (p₁ ↷ m₁ , cfail ℓ) ⨟ (p₂ ↷ m₂ , i₂) = p₁ ↷ m₁ , cfail ℓ

  open import X.BlameStrategies Label using (BlameStrategy; LazyDBS)
  open BlameStrategy LazyDBS using (Injectable)

  open import S.Values Label Injectable (λ A B → Cast (` A ⇒ B))

  open import Error
  
  CastResult : Type → Set
  CastResult T = Error Label (Value T)

  ⟦_⟧ : ∀ {A B} → Cast (` A ⇒ B) → Value A → CastResult B
  ⟦ id★ ⟧       v = return v
  ⟦ h ↷ m , t ⟧ v = {!!}
--   applyCast M id★ {A-id★} =
--       M
--   applyCast M (p ↷ m , cfail ℓ) = raise ℓ
--   applyCast M c = ? -- eta× M c C-pair
--   applyCast M c = ? -- eta⊎ M c C-sum
--   applyCast M (𝜖 ↷ id , 𝜖) = ? -- M
--   applyCast M v ((?? ℓ) {g = g} ↷ m , i) {A-proj}
--       with canonical* M v
--   ... | ⟨ A' , ⟨ M' , ⟨ c , ⟨ i' , ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ ⟩ =
--         M' ⟨ c ⨟ ((?? ℓ) {g = g} ↷ m , i) ⟩

-- --   funCast : ∀ {Γ A A' B'} → (M : Γ ⊢ A) → SimpleValue M
-- --           → (c : Cast (A ⇒ (A' ⇒ B'))) → ∀ {i : Inert c} → Γ ⊢ A' → Γ ⊢ B'
-- --   funCast M v (𝜖 ↷ (c ↣ d) , 𝜖) {I-mid I-cfun} N = (M · N ⟨ c ⟩) ⟨ d ⟩
  

--   open import CastStructure

--   ecs : EfficientCastStruct
--   ecs = record
--              { precast = pcs
--              ; applyCast = applyCast
--              ; compose = _⨟_
--              }
             
--   import EfficientParamCasts
--   open EfficientParamCasts ecs public


--   data PreType : Type → Set where
--     P-Base : ∀{ι} → PreType (` ι)
--     P-Fun : ∀{A B} → PreType (A ⇒ B)
--     P-Pair : ∀{A B} → PreType (A ⊗ B)
--     P-Sum : ∀{A B} → PreType (A `⊎ B)

--   pre? : (A : Type) → Dec (PreType A)
--   pre? * = no (λ ())
--   pre? (` ι) = yes P-Base
--   pre? (A ⇒ B) = yes P-Fun
--   pre? (A ⊗ B) = yes P-Pair
--   pre? (A `⊎ B) = yes P-Sum

--   not-pre-unk : ∀{A} {np : ¬ PreType A} → A ≡ *
--   not-pre-unk {*} {np} = refl
--   not-pre-unk {` ι} {np} = ⊥-elim (contradiction P-Base np)
--   not-pre-unk {A ⇒ B} {np} = ⊥-elim (contradiction P-Fun np)
--   not-pre-unk {A ⊗ B} {np} = ⊥-elim (contradiction P-Pair np)
--   not-pre-unk {A `⊎ B} {np} = ⊥-elim (contradiction P-Sum np)
  
  make-id : (A : Type) → Cast (` A ⇒ A)
  
  make-id-p : (P : PreType) → Middle (` (` P) ⇒ (` P))
  make-id-p (B)  = B'
  make-id-p (T1 ⇒ T2) = make-id T1 ↣  make-id T2
  make-id-p (T1 ⊗ T2) = make-id T1 ×' make-id T2
  -- make-id-p (A `⊎ B) {P-Sum} = make-id A +' make-id B

  make-id * = id★
  make-id (` P) = 𝜖 ↷ make-id-p P , 𝜖

  coerce-to-gnd : (A : PreType) → (B : PreType) → {g : Ground B}
    → Label → Middle (` (` A) ⇒ (` B))
  coerce-from-gnd : (A : PreType) → (B : PreType) → {g : Ground A}
    → Label → Middle (` (` A) ⇒ (` B))
  coerce : (A : Type) → (B : Type) → Label → Cast (` A ⇒ B)

  -- coerce-to* : (A : Type) → Label → Cast (A ⇒ *)
  -- coerce-to* A ℓ with eq-unk A
  -- ... | yes eq rewrite eq = id★ 
  -- ... | no neq with ground? A
  -- ...     | yes g =  𝜖 ↷ (coerce-to-gnd A A {g}{Refl~}{neq} ℓ) , !! {A} {g}
  -- ...     | no ng with ground A {neq}
  -- ...          | ⟨ G , ⟨ g , c ⟩ ⟩ =
  --                𝜖 ↷ (coerce-to-gnd A G {g}{c}{neq} ℓ) , !! {G} {g}

  -- coerce-from* : (B : Type) → Label → Cast (* ⇒ B)
  -- coerce-from* B ℓ with eq-unk B
  -- ... | yes eq rewrite eq = id★
  -- ... | no neq with ground? B
  -- ...     | yes g = (?? ℓ) {B}{g} ↷ (coerce-from-gnd B B {g}{Refl~}{neq} ℓ) , 𝜖
  -- ...     | no ng with ground B {neq}
  -- ...        | ⟨ G , ⟨ g , c ⟩ ⟩ =
  --              (?? ℓ) {G}{g} ↷ (coerce-from-gnd G B {g}{Sym~ c}{neq} ℓ) , 𝜖

  -- coerce-to-gnd .* B {g} {unk~L} {neq} ℓ = ⊥-elim (neq refl)
  -- coerce-to-gnd (` ι) (` ι) {g} {base~} {neq} ℓ = id ι
  -- coerce-to-gnd (A ⇒ B) (* ⇒ *) {G-Fun} {fun~ c d} {neq} ℓ =
  --    (coerce-from* A ℓ) ↣ (coerce-to* B ℓ)
  -- coerce-to-gnd (A `× B) (* `× *) {G-Pair} {pair~ c d} {neq} ℓ =
  --    (coerce-to* A ℓ) ×' (coerce-to* B ℓ)
  -- coerce-to-gnd (A `⊎ B) (* `⊎ *) {G-Sum} {sum~ c d} {neq} ℓ =
  --    (coerce-to* A ℓ) +' (coerce-to* B ℓ)

  -- coerce-from-gnd A .* {g} {unk~R} {neq} ℓ = ⊥-elim (neq refl)
  -- coerce-from-gnd (` ι) (` ι) {g} {base~} {neq} ℓ = id ι
  -- coerce-from-gnd (* ⇒ *) (A ⇒ B) {G-Fun} {fun~ c d} {neq} ℓ =
  --    (coerce-to* A ℓ) ↣ (coerce-from* B ℓ)
  -- coerce-from-gnd (* `× *) (A `× B) {G-Pair} {pair~ c d} {neq} ℓ =
  --    (coerce-from* A ℓ) ×' (coerce-from* B ℓ)
  -- coerce-from-gnd (* `⊎ *) (A `⊎ B) {G-Sum} {sum~ c d} {neq} ℓ =
  --    (coerce-from* A ℓ) +' (coerce-from* B ℓ)

  -- coerce .* B {unk~L} ℓ = coerce-from* B ℓ
  -- coerce A .* {unk~R} ℓ = coerce-to* A ℓ
  -- coerce (` ι) (` ι) {base~} ℓ = 𝜖 ↷ id ι , 𝜖
  -- coerce (A ⇒ B) (C ⇒ D) {fun~ c d} ℓ =
  --    𝜖 ↷ (coerce C A {c} ℓ ↣ coerce B D {d} ℓ) , 𝜖
  -- coerce (A `× B) (C `× D) {pair~ c d} ℓ =
  --    𝜖 ↷ (coerce A C {c} ℓ ×' coerce B D {d} ℓ) , 𝜖
  -- coerce (A `⊎ B) (C `⊎ D) {sum~ c d} ℓ =
  --    𝜖 ↷ (coerce A C {c} ℓ +' coerce B D {d} ℓ) , 𝜖

--       with pre? A
--   ... | yes p = 𝜖 ↷ make-id-p A {p} , 𝜖
--   ... | no np rewrite not-pre-unk {A}{np} = id★

  -- right-id : ∀{A B : Type}(c : Cast (` A ⇒ B))
  --          → c ⨟ make-id B ≡ c
  -- left-id : ∀{A B : Type}(c : Cast (` A ⇒ B))
  --          → make-id A ⨟ c ≡ c
           
  -- right-id-m-p : ∀{A B : PreType}(m : Middle (` (` A) ⇒ (` B)))
  --          → m `⨟ make-id-p B ≡ m
  -- -- right-id-m-p {.(` ι)} {` ι} {id .ι} {P-Base} = refl
  -- right-id-m-p (c ↣ d)
  --     rewrite left-id c | right-id d = refl
  -- right-id-m-p (c ×' d)
  --     rewrite right-id c | right-id d = refl
  -- -- right-id-m-p {A `⊎ A'} {B `⊎ C} {c +' d} {P-Sum} 
  --     -- rewrite right-id {A}{B} {c} | right-id {A'}{C}{d} = refl
      
  -- right-id-p : ∀{A B : PreType}{c : Cast (` (` A) ⇒ (` B))}
  --          → c ⨟ (𝜖 ↷ make-id-p B , 𝜖) ≡ c
  -- right-id-p (_↷_,_ p₁ m₁ 𝜖) {P-Base}
  --     rewrite right-id-m-p {m₁} = refl
  -- right-id-p {A} {` ι} {p₁ ↷ m₁ , cfail ℓ} {P-Base} = refl
  -- right-id-p {A} {B ⇒ C} {_↷_,_ {B = B₁ ⇒ B₂} p₁ (c ↣ d) 𝜖} {P-Fun}
  --     rewrite left-id {B}{B₁}{c} | right-id {B₂}{C}{d} = refl
  -- right-id-p {A} {B ⇒ C} {p₁ ↷ m , cfail ℓ} {P-Fun} = refl
  -- right-id-p {A} {B ⊗ C} {_↷_,_ {B = B₁ ⊗ B₂} p₁ (c ×' d) 𝜖} {P-Pair}
  --     rewrite right-id {B₁}{B}{c} | right-id {B₂}{C}{d} = refl
  -- right-id-p {A} {B ⊗ C} {p₁ ↷ m₁ , cfail ℓ} {P-Pair} = refl
  -- -- right-id-p {A} {B `⊎ C} {_↷_,_ {B = B₁ `⊎ B₂} p₁ (c +' d) 𝜖} {P-Sum} 
  -- --     rewrite right-id {B₁}{B}{c} | right-id {B₂}{C}{d} = refl
  -- -- right-id-p {A} {B `⊎ C} {p₁ ↷ m₁ , cfail ℓ} {P-Sum} = refl

  -- right-id {A} {*} {c} = refl
  -- right-id {A} {` ι} {c} = right-id-p
  -- right-id {A} {B ⇒ C} {c} = right-id-p
  -- right-id {A} {B ⊗ C} {c} = right-id-p
  -- right-id {A} {B `⊎ C} {c} = right-id-p
-- {-
--       with pre? B
--   ... | yes p = right-id-p {A}{B}{c}{p}
--   ... | no np =
--         let x = not-pre-unk {B}{np}  in
--         {!!}
-- -}

--   left-id-m-p : ∀{A B : Type}{m : Middle (A ⇒ B)} {p : PreType A}
--            → make-id-p A {p} `⨟ m ≡ m
--   left-id-m-p {.(` ι)} {` ι} {id .ι} {P-Base} = refl
--   left-id-m-p {A ⇒ A'} {B ⇒ C} {c ↣ d} {P-Fun}
--       rewrite right-id {B}{A} {c} | left-id {A'}{C}{d} = refl
--   left-id-m-p {A ⊗ A'} {B ⊗ C} {c ×' d} {P-Pair}
--       rewrite left-id {A}{B} {c} | left-id {A'}{C}{d} = refl
--   left-id-m-p {A `⊎ A'} {B `⊎ C} {c +' d} {P-Sum} 
--       rewrite left-id {A}{B} {c} | left-id {A'}{C}{d} = refl

--   left-id-p : ∀{A B : Type}{c : Cast (A ⇒ B)} {p : PreType A}
--            → (𝜖 ↷ make-id-p A {p} , 𝜖) ⨟ c ≡ c
--   left-id-p {` ι} {B} {_↷_,_ {C = C} 𝜖 m₁ i₁} {P-Base}
--      rewrite left-id-m-p {` ι}{C}{m₁}{P-Base} = refl
--   left-id-p {A ⇒ C} {B} {_↷_,_ {C = D ⇒ E} 𝜖 (c ↣ d) i₁} {P-Fun}
--      rewrite right-id {D}{A}{c} | left-id {C}{E}{d} = refl
--   left-id-p {A ⊗ C} {B} {_↷_,_ {C = D ⊗ E} 𝜖 (c ×' d) i₁} {P-Pair} 
--      rewrite left-id {A}{D}{c} | left-id {C}{E}{d} = refl
--   left-id-p {A `⊎ C} {B} {_↷_,_ {C = D `⊎ E} 𝜖 (c +' d) i₁} {P-Sum}
--      rewrite left-id {A}{D}{c} | left-id {C}{E}{d} = refl

--   left-id {*} {.*} {id★}
--       with pre? *
--   ... | yes p = refl
--   ... | no np = refl
--   left-id {*} {B} {x ↷ x₁ , x₂} = refl
--   left-id {` ι} {B} {c} = left-id-p
--   left-id {A ⇒ C} {B} {c} = left-id-p
--   left-id {A ⊗ C} {B} {c} = left-id-p
--   left-id {A `⊎ C} {B} {c} = left-id-p

--   left-id★ : ∀{B} (c : Cast (* ⇒ B))
--            → id★ ⨟ c ≡ c
--   left-id★ {B} c = left-id {*}{B}{c}

-- {-
--   todo: update me to match new definition using ground equality -Jeremy
--   assoc : ∀{A B C D} (c₁ : Cast (A ⇒ B)) → (c₂ : Cast (B ⇒ C))
--         → (c₃ : Cast (C ⇒ D))
--         → (c₁ ⨟ c₂) ⨟ c₃ ≡ c₁ ⨟ (c₂ ⨟ c₃)
--   `assoc : ∀{A B C D} (m₁ : Middle (A ⇒ B)) → (m₂ : Middle (B ⇒ C))
--          → (m₃ : Middle (C ⇒ D))
--          → (m₁ `⨟ m₂) `⨟ m₃ ≡ m₁ `⨟ (m₂ `⨟ m₃)
--   `assoc (id .ι) (id ι) (id .ι) = refl
--   `assoc (c₁ ↣ d₁) (c ↣ d) (c₂ ↣ d₂)
--       rewrite assoc c₂ c c₁ | assoc d₁ d d₂ = refl
--   `assoc (c₁ ×' d₁) (c ×' d) (c₂ ×' d₂)
--       rewrite assoc c₁ c c₂ | assoc d₁ d d₂ = refl
--   `assoc (c₁ +' d₁) (c +' d) (c₂ +' d₂)
--       rewrite assoc c₁ c c₂ | assoc d₁ d d₂ = refl
--   assoc c₁ id★ c₃ rewrite left-id★ c₃ = refl
--   assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
--       rewrite `assoc m₁ m₂ m₃ = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃) = refl
--   assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!) id★ = refl
--   assoc {A} {B} {.*} {D} (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!{G = G}{g = g1}) ((?? ℓ){H = H}{g = g2} ↷ m₃ , i₃)
--       with (m₁ `⨟ m₂) ⌣' m₃
--   ... | no m123
--       with gnd-eq? G H {g1}{g2}
--   ... | no G≢H = refl
--   ... | yes refl = ⊥-elim (contradiction refl m123)
--   assoc {A} {B} {.*} {D} (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , !!{g = g1}) ((?? ℓ){g = g2} ↷ m₃ , i₃)
--       | yes m123
--       with consis-ground-eq m123 g1 g2
--   ... | refl
--       with m₂ ⌣' m₃
--   ... | no m23 = ⊥-elim (contradiction m123 m23)
--   ... | yes m23
--       with consis-ground-eq m23 g1 g2
--   ... | refl rewrite `assoc m₁ m₂ m₃ = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , !!) id★ = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ) (𝜖 ↷ m₂ , (!!{g = g1})) ((?? ℓ'){g = g2} ↷ m₃ , i₃)
--       with m₂ ⌣' m₃
--   ... | no m23 = refl
--   ... | yes m23
--       with consis-ground-eq m23 g1 g2
--   ... | refl = refl
--   assoc c₁ (𝜖 ↷ m₂ , cfail ℓ) id★ = refl
--   assoc (p₁ ↷ m₁ , 𝜖) (𝜖 ↷ m₂ , cfail ℓ) (p₃ ↷ m₃ , i₃) = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ') (𝜖 ↷ m₂ , cfail ℓ) (p₃ ↷ m₃ , i₃) = refl
--   assoc {.*} {.*} {C} {D} id★ ((?? ℓ){g = g} ↷ m₂ , i₂) c₃
--       rewrite left-id★ (((?? ℓ){g = g} ↷ m₂ , i₂) ⨟ c₃) = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , i₂) id★ = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
--       with m₁ ⌣' m₂
--   ... | no m12
--          with m₁ ⌣' (m₂ `⨟ m₃)
--   ...    | no m123 = refl
--   ...    | yes m123
--          with consis-ground-eq m123 g1 g2
--   ...    | refl = ⊥-elim (contradiction m123 m12)
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃)
--       | yes m12
--       with consis-ground-eq m12 g1 g2
--   ... | refl
--        with m₁ ⌣' (m₂ `⨟ m₃)
--   ...    | no m123 = ⊥-elim (contradiction m12 m123)
--   ...    | yes m123
--          with consis-ground-eq m123 g1 g2
--   ...    | refl rewrite `assoc m₁ m₂ m₃ = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , cfail ℓ') (𝜖 ↷ m₃ , i₃)
--       with m₁ ⌣' m₂
--   ... | no m12 = refl
--   ... | yes m12
--       with consis-ground-eq m12 g1 g2
--   ... | refl = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1})
--         (?? ℓ {g = g2} ↷ m₂ , !! {g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
--       with m₁ ⌣' m₂
--   ... | no m12
--          with m₂ ⌣' m₃
--   ...    | no m23
--            with m₁ ⌣' m₂ {- need to repeat the with, weird! -}
--   ...      | no m12' = refl
--   ...      | yes m12'
--            with consis-ground-eq m12' g1 g2
--   ...      | refl = ⊥-elim (contradiction m12' m12)
  
--   assoc (p₁ ↷ m₁ , !! {g = g1})
--         (?? ℓ {g = g2} ↷ m₂ , !! {g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
--       | no m12 | yes m23
--             with consis-ground-eq m23 g3 g4
--   ...       | refl
--                with m₁ ⌣' (m₂ `⨟ m₃)
--   ...          | no m123 = refl
--   ...          | yes m123
--                   with consis-ground-eq m123 g1 g2
--   ...             | refl = ⊥-elim (contradiction m123 m12)
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
--       | yes m12
--       with consis-ground-eq m12 g1 g2
--   ... | refl
--       with (m₁ `⨟ m₂) ⌣' m₃
--   ... | no m123
--       with m₂ ⌣' m₃
--   ... | no m23 
--       with m₁ ⌣' m₂ {- weird repetition needed -}
--   ... | no m12' = ⊥-elim (contradiction m12 m12')
--   ... | yes m12'
--       with consis-ground-eq m12' g1 g2
--   ... | refl = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
--       | yes m12 | refl | no m123 | yes m23
--       with consis-ground-eq m23 g3 g4
--   ... | refl
--       with m₁ ⌣' (m₂ `⨟ m₃)
--   ... | no m123' = ⊥-elim (contradiction m23 m123)
--   ... | yes m123'
--       with consis-ground-eq m123' g1 g2
--   ... | refl = ⊥-elim (contradiction m23 m123)
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , !!{g = g3}) ((?? ℓ'){g = g4} ↷ m₃ , i₃)
--       | yes m12 | refl | yes m123
--       with consis-ground-eq m123 g3 g4
--   ... | refl
--       with m₂ ⌣' m₃
--   ... | no m23 = ⊥-elim (contradiction m123 m23)
--   ... | yes m23
--       with consis-ground-eq m23 g3 g4
--   ... | refl
--       with m₁ ⌣' (m₂ `⨟ m₃)
--   ... | no m123' = ⊥-elim (contradiction m12 m123')
--   ... | yes m123'
--       with consis-ground-eq m123' g1 g2
--   ... | refl rewrite `assoc m₁ m₂ m₃ = refl
--   assoc (p₁ ↷ m₁ , !! {g = g1}) (?? ℓ {g = g2} ↷ m₂ , cfail ℓ'') (?? ℓ' ↷ m₃ , i₃)
--       with m₁ ⌣' m₂
--   ... | no m12 = refl
--   ... | yes m12
--       with consis-ground-eq m12 g1 g2
--   ... | refl = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , i₂) id★ = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , 𝜖) (𝜖 ↷ m₃ , i₃) = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , cfail x) (𝜖 ↷ m₃ , i₃) = refl
--   assoc (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , !!{g = g2}) ((?? ℓ''){g = g3} ↷ m₃ , i₃)
--       with m₂ ⌣' m₃
--   ... | no m23 = refl
--   ... | yes m23
--       with consis-ground-eq m23 g2 g3
--   ... | refl = refl
--   assoc {A} {.*} {.*} {D} (p₁ ↷ m₁ , cfail ℓ') (?? ℓ ↷ m₂ , cfail ℓ''') (?? ℓ'' ↷ m₃ , i₃) = refl
-- -}

--   cast-id : ∀ (A : Type) → (l : Label)  → (c : A ~ A)
--           → coerce A A {c} l ≡ make-id A
--   cast-id * l unk~L = refl
--   cast-id * l unk~R = refl
--   cast-id (` ι) l base~ = refl
--   cast-id (A ⇒ B) l (fun~ c d)
--       rewrite (cast-id A l c) | cast-id B l d = refl
--   cast-id (A ⊗ B) l (pair~ c d)
--       rewrite (cast-id A l c) | cast-id B l d = refl
--   cast-id (A `⊎ B) l (sum~ c d)
--       rewrite (cast-id A l c) | cast-id B l d = refl
