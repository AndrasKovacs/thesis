
{-# OPTIONS --without-K --safe #-}

module SimpleInductive2 where

open import Lib
open import Function using (id; _∘_)

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

Sub : Con → Con → Set
Sub Γ Δ = ∀ {A} → Var Δ A → Tm Γ A

------------------------------------------------------------

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ {A} → Var Γ A → Tyᴬ A X

-- Can be only inner!
Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var x)   γ = γ x
Tmᴬ (app t u) γ = Tmᴬ t γ (Tmᴬ u γ)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ σ γ x = Tmᴬ (σ x) γ

--------------------------------------------------------------------------------

Tyᴹ : ∀ A {X₀ X₁} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x₀ → Tyᴹ A Xᴹ (α₀ x₀) (α₁ (Xᴹ x₀))

Conᴹ : ∀ Γ {X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ Γ Xᴹ γ₀ γ₁ = ∀ {A}(x : Var Γ A) → Tyᴹ A Xᴹ (γ₀ x) (γ₁ x)

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν {A} x = Tyᵀ A (ν x)

  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω)
    Tyᴿ ι      t = refl
    Tyᴿ (ι⇒ A) t = λ x₀ → Tyᴿ A (app t x₀)

    Conᴿ : (Γ : Con)(ν : Sub Ω Γ) → Conᴹ Γ ιᴿ (Conᵀ Γ ν) (Subᴬ ν ω)
    Conᴿ Γ ν {A} x = Tyᴿ A (ν x)

Alg : Con → Set₁
Alg Ω = ∃ (Conᴬ Ω)

Hom : ∀ {Ω : Con} → Alg Ω → Alg Ω → Set
Hom {Ω}(X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

InitAlg : ∀ Ω → Alg Ω
InitAlg Ω = ιᵀ Ω , Conᵀ Ω Ω var

Recursor : ∀ Ω → (A : Alg Ω) → Hom (InitAlg Ω) A
Recursor Ω (X , ω) = ιᴿ Ω X ω , Conᴿ Ω X ω Ω var

--------------------------------------------------------------------------------

module Nat1 where

  NatSig = ∙ ▶ ι ▶ ι⇒ ι

  Nat  = InitAlg NatSig .₁
  zero = InitAlg NatSig .₂ (vs vz)
  suc  = InitAlg NatSig .₂ vz

  NatRec : (A : Alg NatSig) → Nat → A .₁
  NatRec A = Recursor NatSig A .₁

  zeroβ : ∀ {A} → NatRec A zero ≡ A .₂ (vs vz)
  zeroβ = refl

  sucβ : ∀ {A} n → NatRec A (suc n) ≡ A .₂ vz (NatRec A n)
  sucβ n = refl
