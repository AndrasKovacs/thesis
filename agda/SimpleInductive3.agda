
{-# OPTIONS --without-K --safe #-}

module SimpleInductive3 where

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
Sub Γ Δ = ∀ {A} → Var Δ A → Tm Γ A

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
var x   [ σ ] = σ x
app t u [ σ ] = app (t [ σ ]) (u [ σ ])

id : ∀ {Γ} → Sub Γ Γ
id = var

[id] : ∀ {Γ A}{t : Tm Γ A} → t [ id ] ≡ t
[id] {t = var x}   = refl
[id] {t = app t u} = app & [id] ⊗ [id]

------------------------------------------------------------

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ {A} → Var Γ A → Tyᴬ A X

Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var x)   γ = γ x
Tmᴬ (app t u) γ = Tmᴬ t γ (Tmᴬ u γ)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ σ γ x = Tmᴬ (σ x) γ

--------------------------------------------------------------------------------

Tyᴹ : (A : Ty) → {X₀ X₁ : Set} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x → Tyᴹ A Xᴹ (α₀ x ) (α₁ (Xᴹ x))

Conᴹ : ∀ (Γ : Con){X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ Γ Xᴹ γ₀ γ₁ = ∀ {A} x → Tyᴹ A Xᴹ (γ₀ x) (γ₁ x)

Tmᴹ : ∀ {Γ A}(t : Tm Γ A){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Tyᴹ A Xᴹ (Tmᴬ t γ₀) (Tmᴬ t γ₁)
Tmᴹ (var x)   γᴹ = γᴹ x
Tmᴹ (app t u) γᴹ rewrite Tmᴹ u γᴹ ⁻¹ = Tmᴹ t γᴹ (Tmᴬ u _)

Subᴹ : ∀ {Γ Δ}(σ : Sub Γ Δ){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Conᴹ Δ Xᴹ (Subᴬ σ γ₀) (Subᴬ σ γ₁)
Subᴹ σ γᴹ {A} x = Tmᴹ (σ x) γᴹ

--------------------------------------------------------------------------------

Tyᴰ : ∀ A {X} → (X → Set) → Tyᴬ A X → Set
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set) → Conᴬ Γ X → Set
Conᴰ Γ Xᴰ γ = ∀ {A} x → Tyᴰ A Xᴰ (γ x)

Tmᴰ : ∀ {Γ A}(t : Tm Γ A) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Tyᴰ A Xᴰ (Tmᴬ t γ)
Tmᴰ (var x)   γᴰ = γᴰ x
Tmᴰ (app t u) γᴰ = Tmᴰ t γᴰ (Tmᴬ u _) (Tmᴰ u γᴰ)

Subᴰ : ∀ {Γ Δ}(σ : Sub Γ Δ) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Conᴰ Δ Xᴰ (Subᴬ σ γ)
Subᴰ σ γᴰ {A} x = Tmᴰ (σ x) γᴰ

--------------------------------------------------------------------------------

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set
Tyˢ ι      Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A) Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set
Conˢ Γ Xˢ γ γᴰ = ∀ {A} x → Tyˢ A Xˢ (γ x) (γᴰ x)

Tmˢ : ∀ {Γ A}(t : Tm Γ A){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Tyˢ A Xˢ (Tmᴬ t γ) (Tmᴰ t γᴰ)
Tmˢ (var x)   γˢ = γˢ x
Tmˢ (app t u) γˢ rewrite Tmˢ u γˢ ⁻¹ = Tmˢ t γˢ (Tmᴬ u _)

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν {A} x = Tyᵀ A (ν x)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A)(ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (var x)   ν = refl
  Tmᵀ (app t u) ν = Tmᵀ t ν ⊗ Tmᵀ u ν

{-
  ιᵀ : Ty₀
  ιᵀ = Tm₀ ↓Ω ι

  Tyᵀ : (A : Ty) → Tm₀ ↓Ω ↓A ⇒ Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν {A } x = Tyᵀ A (↓ (ν x))

  -- Sub is better as first-order data on both levels (or not, b.c. we need fun anyway)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A) → (ν : Sub Ω Γ) → Tyᵀ A (↓(t[ν])) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (var x)   ν = refl
  Tmᵀ (app t u) ν = Tmᵀ t ν ⊗ Tmᵀ u ν
-}

  -- weak initiality
  module _ (X : Set)(ω : Conᴬ Ω X) where


  -- dependent elimination
  -- (Xᴰ : ιᵀ ⇒ U)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω id))
  module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω id)) where
{-
    lem : (t : Tm Ω ι) → Tmᴬ t (Conᵀ Ω id) ≡ t  -- only works on meta terms!

    ιᵉ : (t : Tm₀ ↓Ω ι) ⇒ El (Xᴰ t)
    ιᵉ t = Tmᴰ t ωᴰ  -- evaluate Tm₀ + lem works on Tm₀ !!

-}
    lem : (t : Tm Ω ι) → Tmᴬ t (Conᵀ Ω id) ≡ t
    lem t = Tmᵀ t id ⁻¹ ◾ [id]

    ιᵉ : ∀ t → Xᴰ t
    ιᵉ t = tr Xᴰ (lem t) (Tmᴰ t ωᴰ)

    Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id)) (Tmᴰ t ωᴰ)
    Tyᵉ ι      t   =
        apd⁻¹ ιᵉ (lem t)
      ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl _ (lem t)
    Tyᵉ (ι⇒ A) t x =
       J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
         (Tyᵉ A (app t x))
         _ (lem x)

    Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω id)) (Subᴰ ν ωᴰ)
    Conᵉ Γ ν {A} x = Tyᵉ A (ν x)

module _ (Ω : Con) where

  Alg : Set₁
  Alg = ∃ (Conᴬ Ω)

  Mor : Alg → Alg → Set
  Mor (X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

  DispAlg : Alg → Set₁
  DispAlg (X , ω) = ∃ λ Xᴰ → Conᴰ Ω Xᴰ ω

  Section : (ω : Alg) → DispAlg ω → Set
  Section (X , ω) (Xᴰ , ωᴰ) = ∃ λ Xˢ → Conˢ Ω Xˢ ω ωᴰ

  InitAlg : Alg
  InitAlg = ιᵀ Ω , Conᵀ Ω Ω id

  Elim : (ωᴰ : DispAlg InitAlg) → Section InitAlg ωᴰ
  Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ Ω id

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
