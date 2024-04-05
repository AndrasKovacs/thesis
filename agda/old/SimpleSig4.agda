
{-# OPTIONS --without-K #-}

module SimpleSig4 where

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

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  -- term algebras
  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Ωᵀ : Conᴬ Ω ιᵀ
  Ωᵀ A x = Tyᵀ A (var x)

  Tmᵀ : ∀ {A}(t : Tm Ω A) → Tyᵀ A t ≡ Tmᴬ t Ωᵀ
  Tmᵀ (var x)   = refl
  Tmᵀ (app t u) = Tmᵀ t ⊗ Tmᵀ u

  -- recursors
  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω)
    Tyᴿ ι      t = refl
    Tyᴿ (ι⇒ A) t = λ u → Tyᴿ A (app t u)

    Conᴿ : Conᴹ Ω ιᴿ Ωᵀ ω
    Conᴿ A x = Tyᴿ A (var x)

  -- eliminators
  module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ Ωᵀ) where

    elim : ∀ {A}(t : Tm Ω A) → Tyᴰ A Xᴰ (Tyᵀ A t)
    elim (var x)   = ωᴰ _ x
    elim (app t u) = elim t u (elim u)

    ιᵉ : (t : Tm Ω ι) → Xᴰ t
    ιᵉ t = tr Xᴰ (Tmᵀ t ⁻¹) (Tmᴰ t ωᴰ)

    ιᵉ' : (t : Tm Ω ι) → Xᴰ t
    ιᵉ' = elim

    eq : ∀ {A} (t : Tm Ω A) → tr (Tyᴰ A Xᴰ) (Tmᵀ t ⁻¹) (Tmᴰ t ωᴰ) ≡ elim t
    eq (var x)       = refl
    eq {A} (app t u) = {!!}

    Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t Ωᵀ) (Tmᴰ t ωᴰ)
    Tyᵉ ι      t   =
        apd⁻¹ ιᵉ (Tmᵀ t ⁻¹)
      ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl (Tmᵀ t ⁻¹)
    Tyᵉ (ι⇒ A) t =
       λ x →
       J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t Ωᵀ x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
         (Tyᵉ A (app t x))
         (Tmᵀ x ⁻¹)

    Conᵉ : Conˢ Ω ιᵉ Ωᵀ ωᴰ
    Conᵉ x = Tyᵉ _ (var x)

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
  TmAlg = ιᵀ Ω , Ωᵀ Ω

  Recursor : (ω : Alg) → Mor TmAlg ω
  Recursor (X , ω) = ιᴿ Ω X ω , Conᴿ Ω X ω

  -- Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
  -- Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ

  Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
  Elim (Xᴰ , ωᴰ) = {!elim Ω Xᴰ ωᴰ!} , Conᵉ Ω Xᴰ ωᴰ

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
