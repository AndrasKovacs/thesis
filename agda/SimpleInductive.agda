{-# OPTIONS --without-K --safe #-}

module SimpleInductive where

open import Lib

infix 3 ι⇒_
data Ty : Set where
  ι   : Ty
  ι⇒_ : Ty → Ty

infixl 2 _▶_
data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ A} → Var (Γ ▶ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A} → Var Γ A → Tm Γ A
  app : ∀ {A} → Tm Γ (ι⇒ A) → Tm Γ ι → Tm Γ A

infixl 2 _∷_
data Sub (Γ : Con) : Con → Set where
  ε   : Sub Γ ∙
  _∷_ : ∀ {Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
var vz     [ σ ∷ t ] = t
var (vs x) [ σ ∷ t ] = var x [ σ ]
app t u    [ σ     ] = app (t [ σ ]) (u [ σ ])

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
ε       ∘ δ = ε
(σ ∷ t) ∘ δ = (σ ∘ δ) ∷ (t [ δ ])

wkTm : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▶ B) A
wkTm (var x  ) = var (vs x)
wkTm (app t u) = app (wkTm t) (wkTm u)

wkSub : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▶ A) Δ
wkSub ε       = ε
wkSub (σ ∷ t) = wkSub σ ∷ wkTm t

id : ∀ {Γ} → Sub Γ Γ
id {∙}     = ε
id {Γ ▶ A} = wkSub id ∷ var vz

------------------------------------------------------------

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ ∙       X = ⊤
Conᴬ (Γ ▶ A) X = Conᴬ Γ X × Tyᴬ A X

-- Can be only inner!
Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var vz) γ = ₂ γ
Tmᴬ (var (vs x)) γ = Tmᴬ (var x) (₁ γ)
Tmᴬ (app t u) γ = Tmᴬ t γ (Tmᴬ u γ)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ ε       γ = tt
Subᴬ (σ ∷ t) γ = Subᴬ σ γ , Tmᴬ t γ

--------------------------------------------------------------------------------

Tyᴹ : ∀ A {X₀ X₁} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x₀ → Tyᴹ A Xᴹ (α₀ x₀) (α₁ (Xᴹ x₀))

Conᴹ : ∀ Γ {X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ ∙       Xᴹ γ₀ γ₁ = ⊤
Conᴹ (Γ ▶ A) Xᴹ γ₀ γ₁ = Conᴹ Γ Xᴹ (₁ γ₀) (₁ γ₁) × Tyᴹ A Xᴹ (₂ γ₀) (₂ γ₁)

-- Tmᴹ : ∀ {Γ A} (t : Tm Γ A)
--     → ∀ {X₀ X₁}{Xᴹ : X₀ → X₁}{γ₀ γ₁} → Conᴹ Γ Xᴹ γ₀ γ₁ → Tyᴹ A Xᴹ (Tmᴬ t γ₀) (Tmᴬ t γ₁)
-- Tmᴹ (var vz)     γᴹ = ₂ γᴹ
-- Tmᴹ (var (vs x)) γᴹ = Tmᴹ (var x) (₁ γᴹ)
-- Tmᴹ (app t u)    γᴹ rewrite Tmᴹ u γᴹ ⁻¹ = Tmᴹ t γᴹ (Tmᴬ u _)

-- Subᴹ : ∀ {Γ Δ} (σ : Sub Γ Δ)
--     → ∀ {X₀ X₁}{Xᴹ : X₀ → X₁}{γ₀ γ₁} → Conᴹ Γ Xᴹ γ₀ γ₁ → Conᴹ Δ Xᴹ (Subᴬ σ γ₀) (Subᴬ σ γ₁)
-- Subᴹ ε       γᴹ = tt
-- Subᴹ (σ ∷ t) γᴹ = Subᴹ σ γᴹ , Tmᴹ t γᴹ

--------------------------------------------------------------------------------




--------------------------------------------------------------------------------

module TermAlgebra (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ ∙       ν       = tt
  Conᵀ (Γ ▶ t) (ν ∷ u) = Conᵀ Γ ν , Tyᵀ t u

  -- Tmᵀ : ∀ {Γ A}(t : Tm Γ A)(ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  -- Tmᵀ (var vz)     (ν ∷ _) = refl
  -- Tmᵀ (var (vs x)) (ν ∷ t) = Tmᵀ (var x) ν
  -- Tmᵀ (app t u) ν = (Tmᵀ t ν ⊗ refl) ◾ (Tmᴬ t (Conᵀ _ ν) & Tmᵀ u ν)

  -- Subᵀ : ∀ {Γ Δ}(σ : Sub Γ Δ)(ν : Sub Ω Γ) → Conᵀ Δ (σ ∘ ν) ≡ Subᴬ σ (Conᵀ Γ ν)
  -- Subᵀ ε       ν = refl
  -- Subᵀ (σ ∷ t) ν = _,_ & Subᵀ σ ν ⊗ Tmᵀ t ν

  module Recursion (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω -- Tmᴬ t ω     -- t : Tm₀ ↓Ω ι

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω) -- conversion!
    Tyᴿ ι      t = refl -- refl
    Tyᴿ (ι⇒ A) t = λ x₀ → Tyᴿ A (app t x₀)

    Conᴿ : (Γ : Con)(ν : Sub Ω Γ) → Conᴹ Γ ιᴿ (Conᵀ Γ ν) (Subᴬ ν ω)
    Conᴿ ∙       ν       = tt
    Conᴿ (Γ ▶ A) (ν ∷ t) = Conᴿ Γ ν , Tyᴿ A t


    -- weak initiality


    -- Tm Ω ι → (Ωᴬ X → X)

    -- have to implement -ᴬ fully internally!
    -- Church encoding?

    -- Γᴬ X ≃ (↓Γ)ᴬ X      -- outer vs. inner algebras
    -- Aᴬ X ≃ (↓A)ᴬ X

    -- Ty₀
    -- ↑ : Ty₀ → Set
    -- A : Ty₀ -> ↑A : Set

    -- (Ty₀,↑) closed under 0 type formers, elimination to Ty₀

    -- Term algebra: from any inner model of ToS, we get a model for every Ω

    -- Weak initiality: we only need Tm Ω ι → Conᴬ Ω X → X

    -- Church encoding: the inner model is *defined* to be the impredicative set model.
    -- Assume U₀ is impredicative, Russell-style

    -- Tm Ω ι ≡ ∀ {X} → Ωᴬ X → X  : U


open TermAlgebra
open Recursion

Alg : Con → Set₁
Alg Ω = ∃ (Conᴬ Ω)

Hom : ∀ {Ω : Con} → Alg Ω → Alg Ω → Set
Hom {Ω}(X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

InitAlg : ∀ Ω → Alg Ω
InitAlg Ω = ιᵀ Ω , Conᵀ Ω Ω id

Recursor : ∀ Ω → (A : Alg Ω) → Hom (InitAlg Ω) A
Recursor Ω (X , ω) =
  ιᴿ Ω X ω , tr (Conᴹ Ω (ιᴿ Ω X ω) (Conᵀ Ω Ω id)) {!!} (Conᴿ Ω X ω Ω id)
