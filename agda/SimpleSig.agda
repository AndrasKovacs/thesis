
{-# OPTIONS --without-K #-}

module SimpleSig where

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

Sub : Con → Con → Set
Sub Γ Δ = ∀ A → Var Δ A → Tm Γ A

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
var x   [ σ ] = σ _ x
app t u [ σ ] = app (t [ σ ]) (u [ σ ])

id : ∀ {Γ} → Sub Γ Γ
id A = var

[id] : ∀ {Γ A}{t : Tm Γ A} → t [ id ] ≡ t
[id] {t = var x}   = refl
[id] {t = app t u} = ap app [id] ⊗ [id]

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) A x = (σ A x) [ δ ]

-- algebras
------------------------------------------------------------

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ A → Var Γ A → Tyᴬ A X

Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var x)   γ = γ _ x
Tmᴬ (app t u) γ = Tmᴬ t γ (Tmᴬ u γ)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ σ γ A x = Tmᴬ (σ _ x) γ

-- morphisms
--------------------------------------------------------------------------------

Tyᴹ : (A : Ty) → {X₀ X₁ : Set} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x → Tyᴹ A Xᴹ (α₀ x ) (α₁ (Xᴹ x))

Conᴹ : ∀ (Γ : Con){X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ Γ Xᴹ γ₀ γ₁ = ∀ A x → Tyᴹ A Xᴹ (γ₀ _ x) (γ₁ _ x)

Tmᴹ : ∀ {Γ A}(t : Tm Γ A){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Tyᴹ A Xᴹ (Tmᴬ t γ₀) (Tmᴬ t γ₁)
Tmᴹ (var x)   γᴹ = γᴹ _ x
Tmᴹ (app t u) γᴹ rewrite Tmᴹ u γᴹ ⁻¹ = Tmᴹ t γᴹ (Tmᴬ u _)

Subᴹ : ∀ {Γ Δ}(σ : Sub Γ Δ){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Conᴹ Δ Xᴹ (Subᴬ σ γ₀) (Subᴬ σ γ₁)
Subᴹ σ γᴹ A x = Tmᴹ (σ _ x) γᴹ

-- displayed algebras
--------------------------------------------------------------------------------

Tyᴰ : ∀ A {X} → (X → Set) → Tyᴬ A X → Set
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set) → Conᴬ Γ X → Set
Conᴰ Γ Xᴰ γ = ∀ A x → Tyᴰ A Xᴰ (γ _ x)

Tmᴰ : ∀ {Γ A}(t : Tm Γ A) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Tyᴰ A Xᴰ (Tmᴬ t γ)
Tmᴰ (var x)   γᴰ = γᴰ _ x
Tmᴰ (app t u) γᴰ = Tmᴰ t γᴰ (Tmᴬ u _) (Tmᴰ u γᴰ)

Subᴰ : ∀ {Γ Δ}(σ : Sub Γ Δ) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Conᴰ Δ Xᴰ (Subᴬ σ γ)
Subᴰ σ γᴰ A x = Tmᴰ (σ _ x) γᴰ

-- sections
--------------------------------------------------------------------------------

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set
Tyˢ ι      Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A) Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set
Conˢ Γ Xˢ γ γᴰ = ∀ {A} x → Tyˢ A Xˢ (γ _ x) (γᴰ _ x)

Tmˢ : ∀ {Γ A}(t : Tm Γ A){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Tyˢ A Xˢ (Tmᴬ t γ) (Tmᴰ t γᴰ)
Tmˢ (var x)   γˢ = γˢ x
Tmˢ (app t u) γˢ rewrite Tmˢ u γˢ ⁻¹ = Tmˢ t γˢ (Tmᴬ u _)

Subˢ : ∀ {Γ Δ}(σ : Sub Γ Δ){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Conˢ Δ Xˢ (Subᴬ σ γ) (Subᴰ σ γᴰ)
Subˢ σ γˢ x = Tmˢ (σ _ x) γˢ


--------------------------------------------------------------------------------

module _ (Ω : Con) where

  -- term algebras
  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν A x = Tyᵀ A (ν _ x)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A)(ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (var x)   ν = refl
  Tmᵀ (app t u) ν = Tmᵀ t ν ⊗ Tmᵀ u ν

  Subᵀ : ∀ {Γ Δ}(σ : Sub Γ Δ)(ν : Sub Ω Γ) A x → Conᵀ Δ (σ ∘ ν) A x ≡ Subᴬ σ (Conᵀ Γ ν) A x
  Subᵀ σ ν A x = Tmᵀ (σ A x) ν

  -- recursors
  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω)
    Tyᴿ ι      t = refl
    Tyᴿ (ι⇒ A) t = λ u → Tyᴿ A (app t u)

    Conᴿ : (Γ : Con)(ν : Sub Ω Γ) → Conᴹ Γ ιᴿ (Conᵀ Γ ν) (Subᴬ ν ω)
    Conᴿ Γ ν A x = Tyᴿ A (ν A x)

  -- eliminators
  module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω id)) where

    lem : (t : Tm Ω ι) → Tmᴬ t (Conᵀ Ω id) ≡ t
    lem t = (Tmᵀ t id) ⁻¹ ◾ [id]

    ιᵉ : (t : Tm Ω ι) → Xᴰ t
    ιᵉ t = tr Xᴰ (lem t) (Tmᴰ t ωᴰ)

    Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id)) (Tmᴰ t ωᴰ)
    Tyᵉ ι      t   =
        apd⁻¹ ιᵉ (lem t)
      ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl (lem t)
    Tyᵉ (ι⇒ A) t =
       λ x →
       J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
         (Tyᵉ A (app t x))
         (lem x)

    Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω id)) (Subᴰ ν ωᴰ)
    Conᵉ Γ ν {A} x = Tyᵉ A (ν _ x)

-- packing up underlying sorts with extra data
module _ (Ω : Con) where

  Alg : Set₁
  Alg = ∃ (Conᴬ Ω)

  Mor : Alg → Alg → Set
  Mor (X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

  DispAlg : Alg → Set₁
  DispAlg (X , ω) = ∃ λ Xᴰ → Conᴰ Ω Xᴰ ω

  Section : (ω : Alg) → DispAlg ω → Set
  Section (X , ω) (Xᴰ , ωᴰ) = ∃ λ Xˢ → Conˢ Ω Xˢ ω ωᴰ

  TmAlg : Alg
  TmAlg = ιᵀ Ω , Conᵀ Ω Ω id

  Recursor : (ω : Alg) → Mor TmAlg ω
  Recursor (X , ω) = ιᴿ Ω X ω , Conᴿ Ω X ω Ω id

  Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
  Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ Ω id

-- natural numbers
--------------------------------------------------------------------------------

NatSig = ∙ ▶ ι ▶ ι⇒ ι
NatSyn = TmAlg NatSig
Nat    = NatSyn .₁
zero   = NatSyn .₂ _ (vs vz)
suc    = NatSyn .₂ _ vz

NatElim : (ωᴰ : DispAlg _ NatSyn) → ∀ n → ωᴰ .₁ n
NatElim ωᴰ = Elim NatSig ωᴰ .₁

zeroβ : ∀ ωᴰ → NatElim ωᴰ zero ≡ ωᴰ .₂ _ (vs vz)
zeroβ ωᴰ = refl

sucβ : ∀ n ωᴰ → NatElim ωᴰ (suc n) ≡ ωᴰ .₂ _ vz n (NatElim ωᴰ n)
sucβ n ωᴰ = Elim NatSig ωᴰ .₂ vz n -- not refl
