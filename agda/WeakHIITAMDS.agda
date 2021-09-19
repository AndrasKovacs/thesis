
{-# OPTIONS --without-K --postfix-projections --rewriting #-}

open import Lib

{-
Definition of (parts of the) the AMDS model of the syntax of weak HIIT
signatures. For simplicitly, we don't formally use two-level type theory
here. Instead we work in intensional Agda, and define the model based on a
"wild" cwf, where all equalities are intensional. What we have to manually check
is that every conversion equation in the syntax can be proven as "refl" in the
model, i.e. that it is a strict model.

We omit most of the weak preservation equations up to ID.
-}

module WeakHIITAMDS (ℓ : Level) where

infixl 5 _▶_
infixl 7 _[_]T
infixl 5 _,ₛ_
infixr 6 _∘_
infixl 8 _[_]

the : ∀ {i}(A : Set i) → A → A
the A x = x


-- Base cwf (category with families), i.e. the explicit substitution calculus
--------------------------------------------------------------------------------

record Con : Set₂ where
  constructor con
  field
    ᴬ : Set₁
    ᴹ : ᴬ → ᴬ → Set
    ᴰ : ᴬ → Set₁
    ˢ : (γ : ᴬ) → ᴰ γ → Set
open Con public

record Ty (Γ : Con) : Set₂ where
  constructor ty
  field
    ᴬ : Γ .ᴬ → Set₁
    ᴹ : ∀ γ₀ γ₁ → ᴬ γ₀ → ᴬ γ₁ → Γ .ᴹ γ₀ γ₁ → Set
    ᴰ : ∀ γ → ᴬ γ → Γ .ᴰ γ → Set₁
    ˢ : ∀ γ γᴰ → (α : ᴬ γ) → ᴰ γ α γᴰ → Γ .ˢ γ γᴰ → Set
open Ty public

record Tm Γ (A : Ty Γ) : Set₁ where
  constructor tm
  field
    ᴬ : ∀ γ → A .ᴬ γ
    ᴹ : ∀ γ₀ γ₁ (γᴹ : Γ .ᴹ γ₀ γ₁) → A .ᴹ γ₀ γ₁ (ᴬ γ₀) (ᴬ γ₁) γᴹ
    ᴰ : ∀ γ (γᴰ : Γ .ᴰ γ) → A .ᴰ γ (ᴬ γ) γᴰ
    ˢ : ∀ γ γᴰ (γˢ : Γ .ˢ γ γᴰ) → A .ˢ γ γᴰ (ᴬ γ) (ᴰ γ γᴰ) γˢ
open Tm public

record Sub (Γ Δ : Con) : Set₁ where
  constructor sub
  field
    ᴬ : Γ .ᴬ → Δ .ᴬ
    ᴹ : ∀ γ₀ γ₁ → Γ .ᴹ γ₀ γ₁ → Δ .ᴹ (ᴬ γ₀) (ᴬ γ₁)
    ᴰ : ∀ γ → Γ .ᴰ γ → Δ .ᴰ (ᴬ γ)
    ˢ : ∀ γ γᴰ → Γ .ˢ γ γᴰ → Δ .ˢ (ᴬ γ) (ᴰ γ γᴰ)
open Sub public

∙ : Con
∙ .ᴬ     = Lift ⊤
∙ .ᴹ _ _ = Lift ⊤
∙ .ᴰ _   = Lift ⊤
∙ .ˢ _ _ = Lift ⊤

ε : ∀{Γ} → Sub Γ ∙
ε {Γ} = _

_▶_ : (Γ : Con) → Ty Γ → Con
(Γ ▶ A) .ᴬ                    = Σ (Γ .ᴬ) (A .ᴬ)
(Γ ▶ A) .ᴹ (γ₀ , α₀)(γ₁ , α₁) = Σ (Γ .ᴹ γ₀ γ₁) (A .ᴹ _ _ α₀ α₁)
(Γ ▶ A) .ᴰ (γ , α)            = Σ (Γ .ᴰ γ) (A .ᴰ γ α)
(Γ ▶ A) .ˢ (γ , α)(γᴰ , αᴰ)   = Σ (Γ .ˢ γ γᴰ) (A .ˢ _ _ α αᴰ)

_[_]T : ∀{Γ Δ} → Ty Δ → Sub Γ Δ → Ty Γ
(A [ σ ]T) .ᴬ γ              = A .ᴬ (σ .ᴬ γ)
(A [ σ ]T) .ᴹ γ₀ γ₁ α₀ α₁ γᴹ = A .ᴹ _ _ α₀ α₁ (σ .ᴹ _ _ γᴹ)
(A [ σ ]T) .ᴰ γ α         γᴰ = A .ᴰ _ α (σ .ᴰ _ γᴰ)
(A [ σ ]T) .ˢ γ γᴰ α αᴰ γˢ   = A .ˢ _ _ α αᴰ (σ .ˢ _ _ γˢ)

id : ∀{Γ} → Sub Γ Γ
id {Γ} .ᴬ γ      = γ
id {Γ} .ᴹ _ _ γᴹ = γᴹ
id {Γ} .ᴰ _ γᴰ   = γᴰ
id {Γ} .ˢ _ _ γˢ = γˢ

_∘_ : ∀{Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
(σ ∘ δ) .ᴬ γ      = σ .ᴬ (δ .ᴬ γ)
(σ ∘ δ) .ᴹ _ _ γᴹ = σ .ᴹ _ _(δ .ᴹ _ _ γᴹ)
(σ ∘ δ) .ᴰ _ γᴰ   = σ .ᴰ _ (δ .ᴰ _ γᴰ)
(σ ∘ δ) .ˢ _ _ γˢ = σ .ˢ _ _ (δ .ˢ _ _ γˢ)

_,ₛ_ : ∀{Γ Δ A}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▶ A)
(σ ,ₛ t) .ᴬ γ      = _ , t .ᴬ γ
(σ ,ₛ t) .ᴹ _ _ γᴹ = _ , t .ᴹ _ _ γᴹ
(σ ,ₛ t) .ᴰ _ γᴰ   = _ , t .ᴰ _ γᴰ
(σ ,ₛ t) .ˢ _ _ γˢ = _ , t .ˢ _ _ γˢ

π₁ : ∀{Γ Δ}{A : Ty Δ} → Sub Γ (Δ ▶ A) →  Sub Γ Δ
π₁ σ .ᴬ γ      = ₁ (σ .ᴬ γ)
π₁ σ .ᴹ _ _ γᴹ = ₁ (σ .ᴹ _ _ γᴹ)
π₁ σ .ᴰ _ γᴰ   = ₁ (σ .ᴰ _ γᴰ)
π₁ σ .ˢ _ _ γˢ = ₁ (σ .ˢ _ _ γˢ)

_[_] : ∀{Γ Δ}{A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
(t [ σ ]) .ᴬ γ      = t .ᴬ (σ .ᴬ γ)
(t [ σ ]) .ᴹ _ _ γᴹ = t .ᴹ _ _(σ .ᴹ _ _ γᴹ)
(t [ σ ]) .ᴰ _ γᴰ   = t .ᴰ _ (σ .ᴰ _ γᴰ)
(t [ σ ]) .ˢ _ _ γˢ = t .ˢ _ _ (σ .ˢ _ _ γˢ)

π₂ : ∀{Γ Δ}{A : Ty Δ} → (σ : Sub Γ (Δ ▶ A)) → Tm Γ (A [ π₁ σ ]T)
π₂ σ .ᴬ γ      = ₂ (σ .ᴬ γ)
π₂ σ .ᴹ _ _ γᴹ = ₂ (σ .ᴹ _ _ γᴹ)
π₂ σ .ᴰ _ γᴰ   = ₂ (σ .ᴰ _ γᴰ)
π₂ σ .ˢ _ _ γˢ = ₂ (σ .ˢ _ _ γˢ)

[id]T : ∀{Γ}{A : Ty Γ} → A [ id ]T ≡ A
[id]T = refl

[][]T : ∀{Γ Δ Σ}{A : Ty Σ}{σ : Sub Δ Σ}{δ : Sub Γ Δ} → A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[][]T = refl

idl : {Γ Δ : Con} {σ : Sub Γ Δ} → id ∘ σ ≡ σ
idl = refl

idr : {Γ Δ : Con} {σ : Sub Γ Δ} → σ ∘ id ≡ σ
idr = refl

ass : ∀{Γ Δ Σ Ω}{σ : Sub Σ Ω}{δ : Sub Δ Σ}{ν : Sub Γ Δ}
      → (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
ass = refl

,∘ : ∀{Γ Δ Σ}{δ : Sub Γ Δ}{σ : Sub Σ Γ}{A : Ty Δ}{t : Tm Γ (A [ δ ]T)}
     → (_,ₛ_ {A = A} δ t) ∘ σ ≡ δ ∘ σ ,ₛ (t [ σ ])
,∘ = refl

π₁β : ∀{Γ Δ}{A : Ty Δ}{δ : Sub Γ Δ}{a : Tm Γ (A [ δ ]T)}
      → π₁ (_,ₛ_ {A = A} δ a) ≡ δ
π₁β = refl

π₂β : ∀{Γ Δ}{A : Ty Δ}{δ : Sub Γ Δ}{a : Tm Γ (A [ δ ]T)}
      → π₂ (_,ₛ_ {A = A} δ a) ≡ a
π₂β = refl

πη : ∀{Γ Δ}{A : Ty Δ}{δ : Sub Γ (Δ ▶ A)}
      → _,ₛ_ {A = A} (π₁ δ) (π₂ δ) ≡ δ
πη = refl

εη : ∀{Γ}{σ : Sub Γ ∙}
      → σ ≡ ε
εη = refl

wk : ∀{Γ}{A : Ty Γ} → Sub (Γ ▶ A) Γ
wk {Γ}{A} = π₁ {Γ ▶ A}{Γ}{A} id

vz : ∀{Γ}{A : Ty Γ} → Tm (Γ ▶ A) (A [ wk ]T)
vz {Γ}{A} = π₂ {Γ ▶ A}{Γ}{A} id

vs : ∀{Γ}{A B : Ty Γ} → Tm Γ A → Tm (Γ ▶ B) (A [ wk ]T)
vs {Γ}{A}{B} x = x [ wk ]

infixl 5 _^_
_^_ : {Γ Δ : Con}(σ : Sub Γ Δ)(A : Ty Δ) → Sub (Γ ▶ A [ σ ]T) (Δ ▶ A)
_^_ {Γ}{Δ} σ A = σ ∘ wk ,ₛ vz

-- ID
--------------------------------------------------------------------------------

ID : ∀ {Γ A} → Tm Γ A → Tm Γ A → Ty Γ
ID {Γ}{A} t u .ᴬ γ              = t .ᴬ γ ≡ u .ᴬ γ
ID {Γ}{A} t u .ᴹ γ₀ γ₁ e₀ e₁ γᴹ = tr2 (λ α₀ α₁ → A .ᴹ _ _ α₀ α₁ γᴹ) e₀ (tr-const e₀ ◾ e₁) (t .ᴹ _ _ γᴹ) ≡ u .ᴹ _ _ γᴹ
ID {Γ}{A} t u .ᴰ γ e γᴰ         = tr (λ α → A .ᴰ _ α γᴰ) e (t .ᴰ _ γᴰ) ≡ u .ᴰ _ γᴰ
ID {Γ}{A} t u .ˢ γ γᴰ e eᴰ γˢ   = tr2 (λ α αᴰ → A .ˢ _ _ α αᴰ γˢ) e eᴰ (t .ˢ _ _ γˢ) ≡ u .ˢ _ _ γˢ

ID[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A t u } → ID {Δ}{A} t u [ σ ]T ≡ ID (t [ σ ]) (u [ σ ])
ID[] = refl

REFL : ∀ {Γ A t} → Tm Γ (ID {Γ}{A} t t)
REFL {t = t} .ᴬ γ      = refl
REFL {t = t} .ᴹ _ _ γᴹ = refl
REFL {t = t} .ᴰ _ γᴰ   = refl
REFL {t = t} .ˢ _ _ γˢ = refl

REFL[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A t} → REFL {Δ}{A}{t} [ σ ] ≡ REFL {t = t [ σ ]}
REFL[] = refl

IDJ : ∀ {Γ A}{x : Tm Γ A}(P : Ty (Γ ▶ A ▶ ID (x [ wk ]) vz))
      → Tm Γ (P [ id ,ₛ x ,ₛ REFL ]T)
      → (y : Tm Γ A)
      → (p : Tm Γ (ID x y))
      → Tm Γ (P [ id ,ₛ y ,ₛ p ]T)
IDJ P pr y p .ᴬ γ with y .ᴬ γ | p .ᴬ γ
... | _ | refl = pr .ᴬ γ
IDJ P pr y p .ᴹ γ₀ γ₁ γᴹ with y .ᴹ γ₀ γ₁ γᴹ | p .ᴹ _ _ γᴹ
... | _ | refl with y .ᴬ γ₀ | p .ᴬ γ₀ | y .ᴬ γ₁ | p .ᴬ γ₁
... | _ | refl | _ | refl  = pr .ᴹ _ _ γᴹ
IDJ P pr y p .ᴰ γ γᴰ with y .ᴬ γ | p .ᴬ γ | y .ᴰ γ γᴰ | p .ᴰ γ γᴰ
... | _ | refl | _ | refl = pr .ᴰ _ γᴰ
IDJ P pr y p .ˢ γ γᴰ γˢ with y .ˢ γ γᴰ γˢ | p .ˢ _ _ γˢ
... | _ | refl with y .ᴬ γ | p .ᴬ γ | y .ᴰ _ γᴰ | p .ᴰ _ γᴰ
... | _ | refl | _ | refl  = pr .ˢ _ _ γˢ

-- These would be refl if we used J expressions in IDJ instead of pattern matching
-- pattern matching definitions are opaque to Agda conversion.

-- IDJ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{A}{x : Tm Δ A}(P : Ty (Δ ▶ A ▶ ID (x [ wk ]) vz))
--       → (pr : Tm Δ (P [ id ,ₛ x ,ₛ REFL ]T))
--       → (y : Tm Δ A)
--       → (p : Tm Δ (ID x y))
--       → IDJ {Δ}{A}{x} P pr y p [ σ ]
--       ≡ IDJ {Γ}{A [ σ ]T} (P [ σ ∘ wk ∘ wk ,ₛ vs vz ,ₛ vz ]T) (pr [ σ ]) (y [ σ ]) (p [ σ ])
-- IDJ[] P pr y p = {!refl!}

-- IDβ : ∀ {Γ A}{x : Tm Γ A}(P : Ty (Γ ▶ A ▶ ID (x [ wk ]) vz))
--       → (pr : Tm Γ (P [ id ,ₛ x ,ₛ REFL ]T))
--       → IDJ {Γ}{A}{x} P pr x REFL ≡ pr
-- IDβ = {!!}


-- Universe
--------------------------------------------------------------------------------

U : ∀{Γ} → Ty Γ
U .ᴬ _          = Set
U .ᴹ _ _ a b _  = a → b
U .ᴰ _ a _      = a → Set
U .ˢ _ _ α αᴰ _ = ∀ x → αᴰ x

U[] : ∀{Γ Δ}{σ : Sub Γ Δ} → U [ σ ]T ≡ U
U[] = refl

El : ∀{Γ}(a : Tm Γ U) → Ty Γ
El a .ᴬ γ                    = Lift (a .ᴬ γ)
El a .ᴹ _ _ (↑ α₀) (↑ α₁) γᴹ = a .ᴹ _ _ γᴹ α₀ ≡ α₁
El a .ᴰ _ (↑ α) γᴰ           = Lift (a .ᴰ _ γᴰ α)
El a .ˢ _ _ (↑ α) (↑ αᴰ) γˢ  = a .ˢ _ _ γˢ α ≡ αᴰ

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U} → El a [ σ ]T ≡ El (a [ σ ])
El[] = refl

-- Inductive functions
--------------------------------------------------------------------------------

Π : ∀{Γ}(a : Tm Γ U)(B : Ty (Γ ▶ El a)) → Ty Γ
Π a B .ᴬ γ              = (α : a .ᴬ γ) → B .ᴬ (γ , ↑ α)
Π a B .ᴹ γ₀ γ₁ t₀ t₁ γᴹ = ∀ α → B .ᴹ _ _ (t₀ α) (t₁ (a .ᴹ _ _ γᴹ α)) (γᴹ , refl)
Π a B .ᴰ γ t γᴰ         = ∀ α αᴰ → B .ᴰ (γ , (↑ α)) (t α) (γᴰ , (↑ αᴰ))
Π a B .ˢ γ γᴰ t tᴰ γˢ   = ∀ α → B .ˢ _ _ (t α) (tᴰ _ (a .ˢ _ _ γˢ α)) (γˢ , refl)

Π[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B : Ty (Δ ▶ El a)}
    → (Π a B) [ σ ]T ≡ Π (a [ σ ]) (B [ σ ∘ wk ,ₛ vz ]T)
Π[] = refl

-- βη up to ID
app : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm Γ (Π a B) → Tm (Γ ▶ El a) B
app t .ᴬ (γ , ↑ α)                        = t .ᴬ γ α
app t .ᴹ (γ₀ , ↑ α₀) (γ₁ , _) (γᴹ , refl) = t .ᴹ _ _ γᴹ α₀
app t .ᴰ (γ , ↑ α) (γᴰ , ↑ αᴰ)            = t .ᴰ γ γᴰ α αᴰ
app t .ˢ (γ , ↑ α)(γᴰ , ↑ αᴰ) (γˢ , refl) = t .ˢ _ _ γˢ α

lam : ∀{Γ}{a : Tm Γ U}{B : Ty (Γ ▶ El a)} → Tm (Γ ▶ El a) B → Tm Γ (Π a B)
lam t .ᴬ γ      α  = t .ᴬ (γ , ↑ α)
lam t .ᴹ _ _ γᴹ α  = t .ᴹ _ _ (γᴹ , refl)
lam t .ᴰ _ γᴰ α αᴰ = t .ᴰ _ (γᴰ , (↑ αᴰ))
lam t .ˢ _ _ γˢ α  = t .ˢ _ _ (γˢ , refl)

lam[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ U}{B t} → (lam {Δ}{a}{B} t) [ σ ] ≡ lam (t [ σ ∘ wk ,ₛ vz ])
lam[] = refl

-- External functions
--------------------------------------------------------------------------------

Πᵉˣᵗ : ∀ {Γ}(Ix : Set) → (Ix → Ty Γ) → Ty Γ
Πᵉˣᵗ Ix B .ᴬ γ            = ∀ i → B i .ᴬ γ
Πᵉˣᵗ Ix B .ᴹ _ _ f₀ f₁ γᴹ = ∀ i → B i .ᴹ _ _ (f₀ i) (f₁ i) γᴹ
Πᵉˣᵗ Ix B .ᴰ _ f γᴰ       = ∀ i → B i .ᴰ _ (f i) γᴰ
Πᵉˣᵗ Ix B .ˢ _ _ f fᴰ γˢ  = ∀ i → B i .ˢ _ _ (f i) (fᴰ i) γˢ

Πᵉˣᵗ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{Ix : Set}{B : Ix → Ty Δ} → Πᵉˣᵗ Ix B [ σ ]T ≡ Πᵉˣᵗ Ix (λ i → B i [ σ ]T)
Πᵉˣᵗ[] = refl

appᵉˣᵗ : ∀ {Γ}{Ix}{B : Ix → Ty Γ} → Tm Γ (Πᵉˣᵗ Ix B) → ∀ i → Tm Γ (B i)
appᵉˣᵗ t i .ᴬ γ      = t .ᴬ γ i
appᵉˣᵗ t i .ᴹ _ _ γᴹ = t .ᴹ _ _ γᴹ i
appᵉˣᵗ t i .ᴰ _ γᴰ   = t .ᴰ _ γᴰ i
appᵉˣᵗ t i .ˢ _ _ γˢ = t .ˢ _ _ γˢ i

appᵉˣᵗ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{Ix}{B : Ix → Ty Δ}{t : Tm Δ (Πᵉˣᵗ Ix B)}{i}
           → appᵉˣᵗ {Δ}{Ix}{B} t i [ σ ] ≡ appᵉˣᵗ {Γ}{Ix}{λ i → B i [ σ ]T} (t [ σ ]) i
appᵉˣᵗ[] = refl

lamᵉˣᵗ : ∀ {Γ}{Ix}{B : Ix → Ty Γ} → (∀ i → Tm Γ (B i)) → Tm Γ (Πᵉˣᵗ Ix B)
lamᵉˣᵗ t .ᴬ γ      i = t i .ᴬ γ
lamᵉˣᵗ t .ᴹ _ _ γᴹ i = t i .ᴹ _ _ γᴹ
lamᵉˣᵗ t .ᴰ _ γᴰ   i = t i .ᴰ _ γᴰ
lamᵉˣᵗ t .ˢ _ _ γˢ i = t i .ˢ _ _ γˢ

Πᵉˣᵗβ : ∀ {Γ}{Ix}{B : Ix → Ty Γ}{t : ∀ i → Tm Γ (B i)} → appᵉˣᵗ {Γ}{Ix}{B} (lamᵉˣᵗ {Γ}{Ix}{B} t) ≡ t
Πᵉˣᵗβ = refl

Πᵉˣᵗη : ∀ {Γ}{Ix}{B : Ix → Ty Γ}{t} → lamᵉˣᵗ {Γ}{Ix}{B} (appᵉˣᵗ {Γ}{Ix}{B} t) ≡ t
Πᵉˣᵗη = refl


-- Infinitary functions
--------------------------------------------------------------------------------

Πⁱⁿᶠ : ∀ {Γ}(Ix : Set) → (Ix → Tm Γ U) → Tm Γ U
Πⁱⁿᶠ Ix b .ᴬ γ          = ∀ i → b i .ᴬ γ
Πⁱⁿᶠ Ix b .ᴹ _ _ γᴹ f i = b i .ᴹ _ _ γᴹ (f i)
Πⁱⁿᶠ Ix b .ᴰ _ γᴰ   f   = ∀ i → b i .ᴰ _ γᴰ (f i)
Πⁱⁿᶠ Ix b .ˢ _ _ γˢ f i = b i .ˢ _ _ γˢ (f i)

Πⁱⁿᶠ[] : ∀ {Γ Δ : Con} {σ : Sub Γ Δ} {Ix : Set} {b : Ix → Tm Δ (U {Δ})}
         → Πⁱⁿᶠ Ix b [ σ ] ≡ Πⁱⁿᶠ Ix (λ i → b i [ σ ])
Πⁱⁿᶠ[] = refl

-- βη up to ID (using strong funext)

appⁱⁿᶠ : ∀ {Γ}{Ix}{b : Ix → Tm Γ U} → Tm Γ (El (Πⁱⁿᶠ Ix b)) → ∀ i → Tm Γ (El (b i))
appⁱⁿᶠ t i .ᴬ γ      = ↑ (t .ᴬ γ .↓ i)
appⁱⁿᶠ t i .ᴹ _ _ γᴹ = happly (t .ᴹ _ _ γᴹ) i
appⁱⁿᶠ t i .ᴰ _ γᴰ   = ↑ (t .ᴰ _ γᴰ .↓ i)
appⁱⁿᶠ t i .ˢ _ _ γˢ = happly (t .ˢ _ _ γˢ) i

appⁱⁿᶠ[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{Ix}{b : Ix → Tm Δ U}{t : Tm Δ (El (Πⁱⁿᶠ Ix b))}{i}
           → appⁱⁿᶠ {Δ}{Ix}{b} t i [ σ ] ≡ appⁱⁿᶠ {Γ} {Ix} (t [ σ ]) i
appⁱⁿᶠ[] = refl

lamⁱⁿᶠ : ∀ {Γ}{Ix}{b : Ix → Tm Γ U} → (∀ i → Tm Γ (El (b i))) → Tm Γ (El (Πⁱⁿᶠ Ix b))
lamⁱⁿᶠ t .ᴬ γ      = ↑ λ i → t i .ᴬ γ .↓
lamⁱⁿᶠ t .ᴹ _ _ γᴹ = ext λ i → t i .ᴹ _ _ γᴹ
lamⁱⁿᶠ t .ᴰ _ γᴰ   = ↑ λ i → t i .ᴰ _ γᴰ .↓
lamⁱⁿᶠ t .ˢ _ _ γˢ = ext λ i → t i .ˢ _ _ γˢ

-- ⊤ : Tm Γ U
--------------------------------------------------------------------------------

Top : ∀ {Γ} → Tm Γ U
Top .ᴬ _     = ⊤
Top .ᴹ _ _ _ = _
Top .ᴰ _ _ _ = ⊤
Top .ˢ _ _ _ = _

Top[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Top [ σ ] ≡ Top
Top[] = refl

Tt : ∀ {Γ} → Tm Γ (El Top)
Tt .ᴬ _     = _
Tt .ᴹ _ _ _ = refl
Tt .ᴰ _ _   = _
Tt .ˢ _ _ _ = refl

Tt[] : ∀ {Γ Δ}{σ : Sub Γ Δ} → Tt [ σ ] ≡ Tt
Tt[] = refl

⊤-set : (p q : tt ≡ tt) → p ≡ q
⊤-set refl refl = refl

Topη : ∀ {Γ}{t u : Tm Γ (El Top)} → Tm Γ (ID t u)
Topη .ᴬ γ      = refl
Topη .ᴹ _ _ γᴹ = ⊤-set _ _
Topη .ᴰ _ _    = refl
Topη .ˢ _ _ γˢ = ⊤-set _ _

Topη[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{t u : Tm Δ (El Top)} → Topη {Δ}{t}{u} [ σ ] ≡ Topη
Topη[] = refl


-- Σ
--------------------------------------------------------------------------------

Sg : ∀ {Γ}(a : Tm Γ U) → Tm (Γ ▶ El a) U → Tm Γ U
Sg a b .ᴬ γ                = Σ (a .ᴬ γ) λ α → b .ᴬ (γ , ↑ α)
Sg a b .ᴹ _ _ γᴹ (α₀ , β₀) = (a .ᴹ _ _ γᴹ α₀) , b .ᴹ _ _ (γᴹ , refl) β₀
Sg a b .ᴰ _ γᴰ   (α , β)   = Σ (a .ᴰ _ γᴰ α) λ αᴰ → b .ᴰ _ (γᴰ , ↑ αᴰ) β
Sg a b .ˢ _ _ γˢ (α , β)   = (a .ˢ _ _ γˢ α) , b .ˢ _ _ (γˢ , refl) β

Sg[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a b} → Sg {Δ} a b [ σ ] ≡ Sg (a [ σ ]) (b [ σ ∘ wk ,ₛ vz ])
Sg[] = refl

Proj1 : ∀ {Γ a b} → Tm Γ (El (Sg a b)) → Tm Γ (El a)
Proj1 t .ᴬ γ      = ↑ (t .ᴬ γ .↓ .₁)
Proj1 t .ᴹ _ _ γᴹ = ap ₁ (t .ᴹ _ _ γᴹ)
Proj1 t .ᴰ _ γᴰ   = ↑ (t .ᴰ _ γᴰ .↓ .₁)
Proj1 t .ˢ _ _ γˢ = ap ₁ (t .ˢ _ _ γˢ)

Proj1[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a b t} → Proj1 {Δ}{a}{b} t [ σ ] ≡ Proj1 {Γ} {a [ σ ]} {b [ σ ∘ wk ,ₛ vz ]}(t [ σ ])
Proj1[] = refl

Proj2 : ∀ {Γ a b}(t : Tm Γ (El (Sg a b))) → Tm Γ (El (b [ id ,ₛ Proj1 {Γ}{a}{b} t ]))
Proj2 t .ᴬ γ      = ↑ (t .ᴬ γ .↓ .₂)
Proj2 t .ᴹ γ₀ γ₁ γᴹ with t .ᴬ γ₁ .↓ | t .ᴹ _ _ γᴹ
... | _ | refl = refl
Proj2 t .ᴰ _ γᴰ   = ↑ (t .ᴰ _ γᴰ .↓ .₂)
Proj2 t .ˢ _ γᴰ γˢ with t .ᴰ _ γᴰ .↓ | t .ˢ _ _ γˢ
... | _ | refl = refl

-- Proj2[] : ...

-- For some reason pattern matching fails here. Let's do copy-pasted J definitions instead.
Pair : ∀ {Γ a b}(t : Tm  Γ (El a)) → Tm Γ (El (b [ id ,ₛ t ])) → Tm Γ (El (Sg a b))
Pair t u .ᴬ γ      = ↑ ((t .ᴬ γ .↓) , u .ᴬ γ .↓)
Pair {a = a} {b} t u .ᴹ γ₀ γ₁ γᴹ =
    J (λ uᴬγ₁↓ _ →  (a .ᴹ γ₀ γ₁ γᴹ (t .ᴬ γ₀ .↓) ,
           b .ᴹ (γ₀ , ↑ (t .ᴬ γ₀ .↓)) (γ₁ , ↑ (a .ᴹ γ₀ γ₁ γᴹ (t .ᴬ γ₀ .↓)))
           (γᴹ , refl) (u .ᴬ γ₀ .↓))
          ≡ (t .ᴬ γ₁ .↓ , uᴬγ₁↓))
      (J (λ tᴬγ₁↓ tᴹγᴹ →
            (a .ᴹ γ₀ γ₁ γᴹ (t .ᴬ γ₀ .↓) ,
             b .ᴹ (γ₀ , ↑ (t .ᴬ γ₀ .↓)) (γ₁ , ↑ (a .ᴹ γ₀ γ₁ γᴹ (t .ᴬ γ₀ .↓)))
             (γᴹ , refl) (u .ᴬ γ₀ .↓))
            ≡
            (tᴬγ₁↓ ,
             b .ᴹ (γ₀ , t .ᴬ γ₀) (γ₁ , ↑ tᴬγ₁↓) (γᴹ , tᴹγᴹ)
             (u .ᴬ γ₀ .↓)))
         refl
         (t .ᴹ _ _ γᴹ))
      (u .ᴹ _ _ γᴹ)
Pair t u .ᴰ γ γᴰ   = ↑ (t .ᴰ _ γᴰ .↓ , u .ᴰ _ γᴰ .↓)
Pair {a = a} {b} t u .ˢ γ γᴰ γˢ =
    J (λ uᴰ↓ uˢγˢ →
        (a .ˢ γ γᴰ γˢ (t .ᴬ γ .↓) ,
         b .ˢ (γ , ↑ (t .ᴬ γ .↓)) (γᴰ , ↑ (a .ˢ γ γᴰ γˢ (t .ᴬ γ .↓)))
         (γˢ , refl) (u .ᴬ γ .↓))
         ≡ (t .ᴰ γ γᴰ .↓ , uᴰ↓))
      (J (λ tᴰ↓ tˢγˢ →
           (a .ˢ γ γᴰ γˢ (t .ᴬ γ .↓) , b .ˢ (γ , ↑ (t .ᴬ γ .↓)) (γᴰ , ↑ (a .ˢ γ
           γᴰ γˢ (t .ᴬ γ .↓))) (γˢ , refl) (u .ᴬ γ .↓)) ≡ (tᴰ↓ , b .ˢ (γ
           , t .ᴬ γ) (γᴰ , ↑ tᴰ↓) (γˢ , tˢγˢ) (u .ᴬ γ .↓)))
         refl
         (t .ˢ _ _ γˢ))
      (u .ˢ _ _ γˢ)

-- Works with J.
Pair[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a b t u}
       → Pair {Δ}{a}{b} t u [ σ ] ≡ Pair {Γ}{a [ σ ]}{b [ σ ∘ wk ,ₛ vz ]} (t [ σ ]) (u [ σ ])
Pair[] = refl

-- βη up to ID


-- Id
--------------------------------------------------------------------------------

Id : ∀ {Γ a} → Tm Γ (El a) → Tm Γ (El a) → Tm Γ U
Id {Γ}{a} t u .ᴬ γ        = t .ᴬ γ .↓ ≡ u .ᴬ γ .↓
Id {Γ}{a} t u .ᴹ _ _ γᴹ e = t .ᴹ _ _ γᴹ ⁻¹ ◾ ap (a .ᴹ _ _ γᴹ) e ◾ u .ᴹ _ _ γᴹ
Id {Γ}{a} t u .ᴰ _ γᴰ e   = tr (a .ᴰ _ γᴰ) e (t .ᴰ _ γᴰ .↓) ≡ u .ᴰ _ γᴰ .↓
Id {Γ}{a} t u .ˢ _ _ γˢ e = ap (tr (a .ᴰ _ _) e) (t .ˢ _ _ γˢ ⁻¹) ◾ apd (a .ˢ _ _ γˢ) e ◾ u .ˢ _ _ γˢ

Id[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a t u} → Id {Δ}{a} t u [ σ ] ≡ Id {Γ} (t [ σ ]) (u [ σ ])
Id[] = refl

Refl : ∀ {Γ a}(t : Tm Γ (El a)) → Tm Γ (El (Id t t))
Refl {Γ} {a} t .ᴬ γ      = ↑ refl
Refl {Γ} {a} t .ᴹ _ _ γᴹ = inv (t .ᴹ _ _ γᴹ)
Refl {Γ} {a} t .ᴰ _ γᴰ   = ↑ refl
Refl {Γ} {a} t .ˢ _ _ γˢ = ap (_◾ t .ˢ _ _ γˢ) (ap-id (t .ˢ _ _ γˢ ⁻¹)) ◾ inv (t .ˢ _ _ γˢ)

Refl[] : ∀ {Γ Δ}{σ : Sub Γ Δ}{a t} → Refl {Δ}{a} t [ σ ] ≡ Refl {Γ} (t [ σ ])
Refl[] = refl


-- This one requires path shuffling which was (at least to me) very technical.
-- I skip IdJ[] and IdJβ, these would be hard for Agda (and/or me) to handle.

IdJ : ∀ {Γ a}{x : Tm Γ (El a)}(P : Ty (Γ ▶ El a ▶ El (Id (x [ wk ]) vz)))
      → Tm Γ (P [ id ,ₛ x ,ₛ Refl x ]T)
      → (y : Tm Γ (El a))
      → (p : Tm Γ (El (Id x y)))
      → Tm Γ (P [ id ,ₛ y ,ₛ p ]T)
IdJ {Γ} {a} {x} P pr y p .ᴬ γ =
  J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) (p .ᴬ γ .↓)


IdJ {Γ} {a} {x} P pr y p .ᴹ γ₀ γ₁ γᴹ =

  J (λ pᴬγ₀↓ pᴹ →
       P .ᴹ ((γ₀ , y .ᴬ γ₀) , p .ᴬ γ₀) ((γ₁ , y .ᴬ γ₁) , ↑ pᴬγ₀↓)
            (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₀ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₀)
             (p .ᴬ γ₀ .↓))
            (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
             pᴬγ₀↓)
            ((γᴹ , y .ᴹ γ₀ γ₁ γᴹ) , pᴹ))
    (J (λ yᴬγ₁↓ yᴹ →
         P .ᴹ ((γ₀ , y .ᴬ γ₀) , p .ᴬ γ₀)
               ((γ₁ , ↑ yᴬγ₁↓) ,
                ↑
                (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾
                 ap (a .ᴹ γ₀ γ₁ γᴹ) (p .ᴬ γ₀ .↓) ◾ yᴹ))
               (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₀ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₀)
                (p .ᴬ γ₀ .↓))
               (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
                (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾
                 ap (a .ᴹ γ₀ γ₁ γᴹ) (p .ᴬ γ₀ .↓) ◾ yᴹ))
               ((γᴹ , yᴹ) , refl))
       (J (λ yᴬγ₀↓ pᴬγ₀↓ →
             P .ᴹ ((γ₀ , ↑ yᴬγ₀↓) , ↑ pᴬγ₀↓)
                   ((γ₁ , ↑ (a .ᴹ γ₀ γ₁ γᴹ yᴬγ₀↓)) ,
                    ↑ (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ ap (a .ᴹ γ₀ γ₁ γᴹ) pᴬγ₀↓ ◾ refl))
                   (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₀ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₀)
                    pᴬγ₀↓)
                   (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
                    (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ ap (a .ᴹ γ₀ γ₁ γᴹ) pᴬγ₀↓ ◾ refl))
                   ((γᴹ , refl) , refl))
          (
           let lem1 : x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl ≡ x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl
               lem1 = ap (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾_) (inv⁻¹ (x .ᴹ γ₀ γ₁ γᴹ)) ⁻¹
                   ◾ ◾-ass (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (x .ᴹ γ₀ γ₁ γᴹ) (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) ⁻¹
                   ◾ ap (_◾ x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (inv (x .ᴹ _ _ γᴹ))
                   ◾ ◾refl _ ⁻¹

               lem2 : lem1 ≡ refl
               lem2 = J (λ _ xᴹ → ap (xᴹ ⁻¹ ◾_) (inv⁻¹ (xᴹ)) ⁻¹ ◾
                          ◾-ass (xᴹ ⁻¹) (xᴹ) (xᴹ ⁻¹) ⁻¹ ◾
                          ap (_◾ xᴹ ⁻¹) (inv (xᴹ)) ◾
                          ◾refl (xᴹ ⁻¹) ⁻¹
                          ≡ refl) refl (x .ᴹ _ _ γᴹ)

               lem3 : x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ x .ᴹ γ₀ γ₁ γᴹ ◾ x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ≡
                      x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl
               lem3 = ◾-ass (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (x .ᴹ γ₀ γ₁ γᴹ) (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) ⁻¹
                      ◾ ap (_◾ x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (inv (x .ᴹ _ _ γᴹ))
                      ◾ ◾refl (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) ⁻¹

               lem4 : x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ x .ᴹ γ₀ γ₁ γᴹ ◾ refl ≡ refl
               lem4 =  ◾-ass (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (x .ᴹ γ₀ γ₁ γᴹ) refl ⁻¹
                    ◾  ap (_◾ refl) (inv (x .ᴹ γ₀ γ₁ γᴹ)) ◾ refl

               lem5 : x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ x .ᴹ γ₀ γ₁ γᴹ ◾ refl ≡ refl
               lem5 = ap (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾_) (◾refl (x .ᴹ _ _ γᴹ) ⁻¹ ⁻¹)
                    ◾ inv (x .ᴹ γ₀ γ₁ γᴹ)

               lem6 : lem4 ≡ lem5
               lem6 = J (λ _ p →
                             ◾-ass (p ⁻¹) p refl ⁻¹ ◾ ap (_◾ refl) (inv p) ◾ refl
                           ≡ ap (p ⁻¹ ◾_) ((◾refl p ⁻¹) ⁻¹) ◾ inv p)
                        refl
                        (x .ᴹ _ _ γᴹ)

           in
            J (λ foo bar →
                  P .ᴹ ((γ₀ , ↑ (x .ᴬ γ₀ .↓)) , ↑ refl)
                  ((γ₁ , ↑ (a .ᴹ γ₀ γ₁ γᴹ (x .ᴬ γ₀ .↓))) ,
                   ↑ (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl))
                  (pr .ᴬ γ₀)
                  (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
                   (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl))
                  ((γᴹ , refl) , foo))
                (J (λ foo bar →
                        P .ᴹ ((γ₀ , ↑ (x .ᴬ γ₀ .↓)) , ↑ refl)
                              ((γ₁ , ↑ (a .ᴹ γ₀ γ₁ γᴹ (x .ᴬ γ₀ .↓))) ,
                               ↑ (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl))
                              (pr .ᴬ γ₀)
                              (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
                               (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾ refl))
                              ((γᴹ , foo) ,
                               ap (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾_) bar ⁻¹ ◾
                               ◾-ass (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (x .ᴹ γ₀ γ₁ γᴹ) (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) ⁻¹ ◾
                               ap (_◾ x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (inv (x .ᴹ γ₀ γ₁ γᴹ)) ◾
                               ◾refl (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) ⁻¹))
                    (J (λ foo xᴹ⁻¹ →
                           P .ᴹ ((γ₀ , ↑ (x .ᴬ γ₀ .↓)) , ↑ refl)
                                 ((γ₁ , ↑ foo) ,
                                  ↑ (xᴹ⁻¹ ◾ refl))
                                 (pr .ᴬ γ₀)
                                 (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ₁ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ₁)
                                  (xᴹ⁻¹ ◾ refl))
                                 ((γᴹ , x .ᴹ γ₀ γ₁ γᴹ ◾ xᴹ⁻¹) ,
                                  ◾-ass (x .ᴹ γ₀ γ₁ γᴹ ⁻¹) (x .ᴹ γ₀ γ₁ γᴹ) (xᴹ⁻¹) ⁻¹ ◾
                                  ap (_◾ xᴹ⁻¹) (inv (x .ᴹ γ₀ γ₁ γᴹ)) ◾
                                  ◾refl xᴹ⁻¹ ⁻¹))
                        (J (λ foo _ →
                              P .ᴹ ((γ₀ , ↑ (x .ᴬ γ₀ .↓)) , ↑ refl)
                             ((γ₁ , ↑ (x .ᴬ γ₁ .↓)) , ↑ refl) (pr .ᴬ γ₀) (pr .ᴬ γ₁)
                             ((γᴹ , x .ᴹ γ₀ γ₁ γᴹ ◾ refl) , foo))
                           (J (λ foo bar →
                                 P .ᴹ ((γ₀ , ↑ (x .ᴬ γ₀ .↓)) , ↑ refl)
                                       ((γ₁ , ↑ (x .ᴬ γ₁ .↓)) , ↑ refl) (pr .ᴬ γ₀) (pr .ᴬ γ₁)
                                       ((γᴹ , foo) ,
                                        ap (x .ᴹ γ₀ γ₁ γᴹ ⁻¹ ◾_) (bar ⁻¹) ◾
                                        inv (x .ᴹ γ₀ γ₁ γᴹ)))
                               (pr .ᴹ _ _ γᴹ)
                               (◾refl (x .ᴹ _ _ γᴹ) ⁻¹))
                           (lem6 ⁻¹))
                        (x .ᴹ _ _ γᴹ ⁻¹))
                    (inv⁻¹ (x .ᴹ _ _ γᴹ)))
                lem2)
          (p .ᴬ γ₀ .↓))
       (y .ᴹ _ _ γᴹ))
    (p .ᴹ _ _ γᴹ)


IdJ {Γ} {a} {x} P pr y p .ᴰ γ γᴰ    =
  J (λ yᴰ↓ pᴰ↓ →
       P .ᴰ ((γ , y .ᴬ γ) , p .ᴬ γ)
         (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ)
          (p .ᴬ γ .↓))
         ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓))
    (J (λ yᴬ↓ pᴬ↓ →
          P .ᴰ ((γ , ↑ yᴬ↓) , ↑ pᴬ↓)
          (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ)
          pᴬ↓)
          ((γᴰ , ↑ (tr (a .ᴰ γ γᴰ) pᴬ↓ (x .ᴰ γ γᴰ .↓))) , ↑ refl))
       (pr .ᴰ _ γᴰ)
       (p .ᴬ γ .↓))
    (p .ᴰ _ γᴰ .↓)


IdJ {Γ} {a} {x} P pr y p .ˢ γ γᴰ γˢ =
  J (λ pᴰ↓ pˢ →
      P .ˢ ((γ , y .ᴬ γ) , p .ᴬ γ) ((γᴰ , y .ᴰ γ γᴰ) , ↑ pᴰ↓) (J (λ yᴬγ↓ pᴬγ↓ →
      P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) (p .ᴬ γ .↓)) (J (λ yᴰ↓ pᴰ↓ → P .ᴰ
      ((γ , y .ᴬ γ) , p .ᴬ γ) (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓))
      (pr .ᴬ γ) (p .ᴬ γ .↓)) ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓)) (J (λ yᴬ↓ pᴬ↓ → P .ᴰ ((γ ,
      ↑ yᴬ↓) , ↑ pᴬ↓) (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ)
      pᴬ↓) ((γᴰ , ↑ (tr (a .ᴰ γ γᴰ) pᴬ↓ (x .ᴰ γ γᴰ .↓))) , ↑ refl)) (pr .ᴰ γ γᴰ)
      (p .ᴬ γ .↓)) (pᴰ↓)) ((γˢ , y .ˢ γ γᴰ γˢ) , pˢ))
    (J (λ yᴰ↓ yˢ →
           P .ˢ ((γ , y .ᴬ γ) , p .ᴬ γ) ((γᴰ , ↑ yᴰ↓) , ↑ (ap (tr (a .ᴰ γ γᴰ)
           (p .ᴬ γ .↓)) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ apd (a .ˢ γ γᴰ γˢ) (p .ᴬ γ .↓) ◾
           yˢ)) (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) (p .ᴬ
           γ .↓)) (J (λ yᴰ↓ pᴰ↓ → P .ᴰ ((γ , y .ᴬ γ) , p .ᴬ γ) (J (λ yᴬγ↓ pᴬγ↓ →
           P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) (p .ᴬ γ .↓)) ((γᴰ , ↑ yᴰ↓) ,
           ↑ pᴰ↓)) (J (λ yᴬ↓ pᴬ↓ → P .ᴰ ((γ , ↑ yᴬ↓) , ↑ pᴬ↓) (J (λ yᴬγ↓ pᴬγ↓ →
           P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) pᴬ↓) ((γᴰ , ↑ (tr (a .ᴰ γ γᴰ)
           pᴬ↓ (x .ᴰ γ γᴰ .↓))) , ↑ refl)) (pr .ᴰ γ γᴰ) (p .ᴬ γ .↓)) (ap (tr (a
           .ᴰ γ γᴰ) (p .ᴬ γ .↓)) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ apd (a .ˢ γ γᴰ γˢ) (p .ᴬ γ
           .↓) ◾ yˢ)) ((γˢ , yˢ) , refl))
       (J (λ yᴬ↓ pᴬ↓ →
             P .ˢ ((γ , ↑ yᴬ↓) , ↑ pᴬ↓) ((γᴰ , ↑ (a .ˢ γ γᴰ γˢ yᴬ↓)) , ↑ (ap (tr
             (a .ᴰ γ γᴰ) pᴬ↓) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ apd (a .ˢ γ γᴰ γˢ) pᴬ↓
             ◾ refl)) (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr
             .ᴬ γ) pᴬ↓) (J (λ yᴰ↓ pᴰ↓ → P .ᴰ ((γ , ↑ yᴬ↓) , ↑ pᴬ↓) (J (λ
             yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ γ) (pᴬ↓))
             ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓)) (J (λ yᴬ↓ pᴬ↓ → P .ᴰ ((γ , ↑ yᴬ↓) , ↑
             pᴬ↓) (J (λ yᴬγ↓ pᴬγ↓ → P .ᴬ ((γ , ↑ yᴬγ↓) , ↑ pᴬγ↓)) (pr .ᴬ
             γ) pᴬ↓) ((γᴰ , ↑ (tr (a .ᴰ γ γᴰ) pᴬ↓ (x .ᴰ γ γᴰ .↓))) , ↑
             refl)) (pr .ᴰ γ γᴰ) pᴬ↓) (ap (tr (a .ᴰ γ γᴰ) pᴬ↓) (x .ˢ γ γᴰ
             γˢ ⁻¹) ◾ apd (a .ˢ γ γᴰ γˢ) pᴬ↓ ◾ refl)) ((γˢ , refl) ,
             refl))
         (
         let
             lem1 : ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ refl ≡
                    ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ refl
             lem1 = ap (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾_) (inv⁻¹ (x .ˢ γ γᴰ γˢ) ⁻¹)
                  ◾ ◾-ass (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)) (x .ˢ γ γᴰ γˢ) (x .ˢ γ γᴰ γˢ ⁻¹) ⁻¹
                  ◾ ap (λ p → (p ◾ x .ˢ γ γᴰ γˢ) ◾ x .ˢ γ γᴰ γˢ ⁻¹) (ap-id (x .ˢ γ γᴰ γˢ ⁻¹))
                  ◾ ap (_◾ x .ˢ γ γᴰ γˢ ⁻¹) (inv (x .ˢ γ γᴰ γˢ))
                  ◾ ap-id (x .ˢ γ γᴰ γˢ ⁻¹) ⁻¹
                  ◾ ◾refl (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)) ⁻¹

             lem2 : lem1 ≡ refl
             lem2 = J (λ _ p →
                         ap (ap (λ p₁ → p₁) (p ⁻¹) ◾_) (inv⁻¹ (p) ⁻¹) ◾ ◾-ass (ap (λ p₁ → p₁) (p ⁻¹))
                         (p) (p ⁻¹) ⁻¹ ◾ ap (λ p₁ → (p₁ ◾ p) ◾ p ⁻¹) (ap-id (p ⁻¹)) ◾ ap (_◾ p ⁻¹)
                         (inv (p)) ◾ ap-id (p ⁻¹) ⁻¹ ◾ ◾refl (ap (λ p₁ → p₁) (p ⁻¹)) ⁻¹ ≡
                         refl)
                      refl (x .ˢ _ _ γˢ)

             lem3 : ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ x .ˢ γ γᴰ γˢ ◾ refl ≡ refl
             lem3 = ◾-ass (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)) (x .ˢ γ γᴰ γˢ) refl ⁻¹
                  ◾ ap (λ p₁ → (p₁ ◾ x .ˢ γ γᴰ γˢ) ◾ refl) (ap-id (x .ˢ γ γᴰ γˢ ⁻¹))
                  ◾ ap (_◾ refl) (inv (x .ˢ γ γᴰ γˢ)) ◾ refl

             lem4 : ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ x .ˢ γ γᴰ γˢ ◾ refl ≡ refl
             lem4 = ap (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾_) (◾refl (x .ˢ γ γᴰ γˢ) ⁻¹ ⁻¹)
                  ◾ ap (_◾ x .ˢ γ γᴰ γˢ) (ap-id (x .ˢ γ γᴰ γˢ ⁻¹))
                  ◾ inv (x .ˢ γ γᴰ γˢ)

             lem5 : lem3 ≡ lem4
             lem5 = J (λ _ p →
                           ◾-ass (ap (λ p₁ → p₁) (p ⁻¹)) (p) refl ⁻¹ ◾ ap (λ
                           p₁ → (p₁ ◾ p) ◾ refl) (ap-id (p ⁻¹)) ◾ ap (_◾
                           refl) (inv (p)) ◾ refl ≡ ap (ap (λ p₁ → p₁) (p ⁻¹)
                           ◾_) ((◾refl (p) ⁻¹) ⁻¹) ◾ ap (_◾ p)
                           (ap-id (p ⁻¹)) ◾ inv (p))
                        refl (x .ˢ _ _ γˢ)

         in tr (λ foo →
                  P .ˢ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl) ((γᴰ , ↑ (a .ˢ γ γᴰ γˢ (x .ᴬ γ .↓))) , ↑ (ap
                  (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ refl)) (pr .ᴬ γ) (J (λ yᴰ↓ pᴰ↓ → P .ᴰ ((γ
                  , ↑ (x .ᴬ γ .↓)) , ↑ refl) (pr .ᴬ γ) ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓)) (pr .ᴰ γ γᴰ)
                  (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾ refl)) ((γˢ , refl) , foo))
               lem2
               (J (λ foo bar →
                     P .ˢ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl) ((γᴰ , ↑ (a .ˢ γ γᴰ γˢ
                     (x .ᴬ γ .↓))) , ↑ (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)
                     ◾ refl)) (pr .ᴬ γ) (J (λ yᴰ↓ pᴰ↓ → P .ᴰ ((γ , ↑ (x
                     .ᴬ γ .↓)) , ↑ refl) (pr .ᴬ γ) ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓))
                     (pr .ᴰ γ γᴰ) (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾
                     refl)) ((γˢ , foo) , ap (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ
                     ⁻¹) ◾_) (bar ⁻¹) ◾ ◾-ass (ap (λ p₁ → p₁) (x .ˢ γ
                     γᴰ γˢ ⁻¹)) (x .ˢ γ γᴰ γˢ) (x .ˢ γ γᴰ γˢ ⁻¹) ⁻¹ ◾ ap
                     (λ p₁ → (p₁ ◾ x .ˢ γ γᴰ γˢ) ◾ x .ˢ γ γᴰ γˢ ⁻¹)
                     (ap-id (x .ˢ γ γᴰ γˢ ⁻¹)) ◾ ap (_◾ x .ˢ γ γᴰ γˢ ⁻¹)
                     (inv (x .ˢ γ γᴰ γˢ)) ◾ ap-id (x .ˢ γ γᴰ γˢ ⁻¹) ⁻¹ ◾
                     ◾refl (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)) ⁻¹))
                 (J (λ foo xˢ⁻¹ →
                         P .ˢ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl)
                         ((γᴰ , ↑ foo) ,
                          ↑ (ap (λ p₁ → p₁) xˢ⁻¹ ◾ refl))
                         (pr .ᴬ γ)
                         (J
                          (λ yᴰ↓ pᴰ↓ →
                             P .ᴰ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl) (pr .ᴬ γ)
                             ((γᴰ , ↑ yᴰ↓) , ↑ pᴰ↓))
                          (pr .ᴰ γ γᴰ) (ap (λ p₁ → p₁) xˢ⁻¹ ◾ refl))
                         ((γˢ , x .ˢ γ γᴰ γˢ ◾ xˢ⁻¹) ,
                          ◾-ass (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹)) (x .ˢ γ γᴰ γˢ) xˢ⁻¹ ⁻¹
                          ◾ ap (λ p₁ → (p₁ ◾ x .ˢ γ γᴰ γˢ) ◾ xˢ⁻¹) (ap-id (x .ˢ γ γᴰ γˢ ⁻¹))
                          ◾ ap (_◾ xˢ⁻¹) (inv (x .ˢ γ γᴰ γˢ))
                          ◾ ap-id (xˢ⁻¹) ⁻¹ ◾
                          ◾refl (ap (λ p₁ → p₁) xˢ⁻¹) ⁻¹))
                    (tr (λ foo →
                           P .ˢ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl)
                           ((γᴰ , ↑ (x .ᴰ γ γᴰ .↓)) , ↑ refl) (pr .ᴬ γ) (pr .ᴰ γ γᴰ)
                           ((γˢ , x .ˢ γ γᴰ γˢ ◾ refl) , foo))
                        (lem5 ⁻¹)
                        (J (λ foo bar →
                              P .ˢ ((γ , ↑ (x .ᴬ γ .↓)) , ↑ refl) ((γᴰ , ↑ (x .ᴰ γ γᴰ .↓)) , ↑ refl) (pr
                              .ᴬ γ) (pr .ᴰ γ γᴰ) ((γˢ , foo) , ap (ap (λ p₁ → p₁) (x .ˢ γ γᴰ γˢ ⁻¹) ◾_)
                              (bar ⁻¹) ◾ ap (_◾ x .ˢ γ γᴰ γˢ) (ap-id (x .ˢ γ γᴰ γˢ ⁻¹)) ◾ inv (x .ˢ γ
                              γᴰ γˢ)))
                            (pr .ˢ _ _ γˢ)
                            (◾refl (x .ˢ _ _ γˢ) ⁻¹)))
                    (x .ˢ _ _ γˢ ⁻¹))
                 (inv⁻¹ (x .ˢ γ γᴰ γˢ)))
         )
         (p .ᴬ γ .↓))
       (y .ˢ _ _ γˢ))
    (p .ˢ _ _ γˢ)
