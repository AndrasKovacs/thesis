{-# OPTIONS --without-K --safe #-}

module SimpleInductive4 where

open import Lib
open import Function using (id; _∘_)

infix 3 ι⇒_
infixr 3 _⇒_
data Ty : Set₁ where
  ι   : Ty
  ι⇒_ : Ty → Ty
  _⇒_ : (A : Set) → (A → Ty) → Ty

infixl 2 _▶_
data Con : Set₁ where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Var : Con → Ty → Set₁ where
  vz : ∀ {Γ A} → Var (Γ ▶ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set₁ where
  var : ∀ {A} → Var Γ A → Tm Γ A
  app : ∀ {A} → Tm Γ (ι⇒ A) → Tm Γ ι → Tm Γ A
  app̂ : ∀ {A B} → Tm Γ (A ⇒ B) → (α : A) → Tm Γ (B α)

Sub : Con → Con → Set₁
Sub Γ Δ = ∀ {A} → Var Δ A → Tm Γ A

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
var x   [ σ ] = σ x
app t u [ σ ] = app (t [ σ ]) (u [ σ ])
app̂ t α [ σ ] = app̂ (t [ σ ]) α

[var] : ∀ {Γ A}{t : Tm Γ A} → t [ var ] ≡ t
[var] {t = var x}   = refl
[var] {t = app t u} = app & [var] ⊗ [var]
[var] {t = app̂ t α} = (λ t → app̂ t α) & [var]


------------------------------------------------------------

Tyᴬ : Ty → Set₁ → Set₁
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X
Tyᴬ (A ⇒ B) X = ∀ α → Tyᴬ (B α) X

Conᴬ : Con → Set₁ → Set₁
Conᴬ Γ X = ∀ {A} → Var Γ A → Tyᴬ A X

Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var x)   γ = γ x
Tmᴬ (app t u) γ = Tmᴬ t γ (Tmᴬ u γ)
Tmᴬ (app̂ t α) γ = Tmᴬ t γ α

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ σ γ x = Tmᴬ (σ x) γ

--------------------------------------------------------------------------------

Tyᴰ : ∀ A {X} → (X → Set₁) → Tyᴬ A X → Set₁
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)
Tyᴰ (A ⇒ B) Xᴰ α = ∀ x → Tyᴰ (B x) Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set₁) → Conᴬ Γ X → Set₁
Conᴰ Γ Xᴰ γ = ∀ {A} x → Tyᴰ A Xᴰ (γ x)

Tmᴰ : ∀ {Γ A}(t : Tm Γ A) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Tyᴰ A Xᴰ (Tmᴬ t γ)
Tmᴰ (var x)   γᴰ = γᴰ x
Tmᴰ (app t u) γᴰ = Tmᴰ t γᴰ _ (Tmᴰ u γᴰ)
Tmᴰ (app̂ t α) γᴰ = Tmᴰ t γᴰ α

Subᴰ : ∀ {Γ Δ}(σ : Sub Γ Δ) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Conᴰ Δ Xᴰ (Subᴬ σ γ)
Subᴰ σ γᴰ {A} x = Tmᴰ (σ x) γᴰ

--------------------------------------------------------------------------------

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set₁
Tyˢ ι       Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A)  Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))
Tyˢ (A ⇒ B) Xˢ α αᴰ = ∀ x → Tyˢ (B x) Xˢ (α x) (αᴰ x)

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set₁
Conˢ Γ Xˢ γ γᴰ = ∀ {A} x → Tyˢ A Xˢ (γ x) (γᴰ x)

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set₁
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι       t = t
  Tyᵀ (ι⇒ A)  t = λ u → Tyᵀ A (app t u)
  Tyᵀ (A ⇒ B) t = λ x → Tyᵀ (B x) (app̂ t x)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν {A} x = Tyᵀ A (ν x)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A)(ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (var x)   ν = refl
  Tmᵀ (app t u) ν = Tmᵀ t ν ⊗ Tmᵀ u ν
  Tmᵀ (app̂ t α) ν = happly (Tmᵀ t ν) α

  module _ (Xᴰ : ιᵀ → Set₁)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω var)) where

    lem : ∀ t → Tmᴬ t (Conᵀ Ω var) ≡ t
    lem t = Tmᵀ t var ⁻¹ ◾ [var]

    ιᵉ : ∀ t → Xᴰ t
    ιᵉ t = tr Xᴰ (lem t) (Tmᴰ t ωᴰ)

    Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω var)) (Tmᴰ t ωᴰ)
    Tyᵉ ι      t   =
        apd⁻¹ ιᵉ (lem t)
      ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl _ (lem t)
    Tyᵉ (ι⇒ A) t x =
       J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω var) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
         (Tyᵉ A (app t x))
         _ (lem x)
    Tyᵉ (A ⇒ B) t x =
      Tyᵉ (B x) (app̂ t x)

    Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω var)) (Subᴰ ν ωᴰ)
    Conᵉ Γ ν {A} x = Tyᵉ A (ν x)

module _ (Ω : Con) where

  Alg : Set₂
  Alg = ∃ (Conᴬ Ω)

  DispAlg : Alg → Set₂
  DispAlg (X , ω) = ∃ λ Xᴰ → Conᴰ Ω Xᴰ ω

  Section : (ω : Alg) → DispAlg ω → Set₁
  Section (X , ω) (Xᴰ , ωᴰ) = ∃ λ Xˢ → Conˢ Ω Xˢ ω ωᴰ

  InitAlg : Alg
  InitAlg = ιᵀ Ω , Conᵀ Ω Ω var

  Elim : (ωᴰ : DispAlg InitAlg) → Section InitAlg ωᴰ
  Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ Ω var

--------------------------------------------------------------------------------

NatSig = ∙ ▶ ι ▶ ι⇒ ι
NatSyn = InitAlg NatSig
Nat  = NatSyn .₁
zero = NatSyn .₂ (vs vz)
suc  = NatSyn .₂ vz

NatElim : (ωᴰ : DispAlg _ NatSyn) → ∀ n → ωᴰ .₁ n
NatElim ωᴰ = Elim NatSig ωᴰ .₁

zeroβ : ∀ ωᴰ → NatElim ωᴰ zero ≡ ωᴰ .₂ (vs vz)
zeroβ ωᴰ = refl

sucβ : ∀ n ωᴰ → NatElim ωᴰ (suc n) ≡ ωᴰ .₂ vz n (NatElim ωᴰ n)
sucβ n ωᴰ = Elim NatSig ωᴰ .₂ vz n -- not refl
