
{-# OPTIONS --without-K --safe #-}

module SpineTm where

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

mutual
  Tm : Con → Ty → Set
  Tm Γ B = ∃ λ A → Var Γ A × Sp Γ A B

  data Sp (Γ : Con) : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _,_ : ∀ {B C} → Tm Γ ι → Sp Γ B C → Sp Γ (ι⇒ B) C

Sub : Con → Con → Set
Sub Γ Δ = ∀ A → Var Δ A → Tm Γ A

infixr 4 _++_
_++_ : ∀ {Γ A B C} → Sp Γ A B → Sp Γ B C → Sp Γ A C
ε        ++ sp' = sp'
(t , sp) ++ sp' = t , (sp ++ sp')

-- app : ∀ {Γ A B} → Tm Γ  → Tm Γ A → Tm Γ B

appₛ : ∀ {Γ A B} → Tm Γ A → Sp Γ A B → Tm Γ B
appₛ (_ , x , sp) sp' = _ , x , (sp ++ sp')

infix 5 _[_] _[_]ₛ
_[_]   : ∀ {Γ Δ A}   → Tm Δ A → Sub Γ Δ → Tm Γ A
_[_]ₛ  : ∀ {Γ Δ A B} → Sp Δ A B → Sub Γ Δ → Sp Γ A B
(_ , x , sp) [ σ ]  = appₛ (σ _ x) (sp [ σ ]ₛ)
ε            [ σ ]ₛ = ε
(t , sp)     [ σ ]ₛ = t [ σ ] , sp [ σ ]ₛ

id : ∀ {Γ} → Sub Γ Γ
id A x = _ , x , ε

[id]  : ∀ {Γ A}  {t  : Tm Γ A}   → t [ id ] ≡ t
[id]ₛ : ∀ {Γ A B}{sp : Sp Γ A B} → sp [ id ]ₛ ≡ sp
[id] {t = _ , x , sp} rewrite [id]ₛ {sp = sp} = refl
[id]ₛ {sp = ε     } = refl
[id]ₛ {sp = t , sp} rewrite [id] {t = t} | [id]ₛ {sp = sp} = refl

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
(σ ∘ δ) A x = (σ A x) [ δ ]

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ A → Var Γ A → Tyᴬ A X

Tmᴬ : ∀ {Γ A}   → Tm Γ A   → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Spᴬ : ∀ {Γ A B} → Sp Γ A B → ∀ {X} → Conᴬ Γ X → Tyᴬ A X → Tyᴬ B X
Tmᴬ (B , x , sp) γ   = Spᴬ sp γ (γ _ x)
Spᴬ ε            γ α = α
Spᴬ (t , sp)     γ α = Spᴬ sp γ (α (Tmᴬ t γ))

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ σ γ A x = Tmᴬ (σ _ x) γ

module NatExample where

  Nat : Set
  Nat = Tm (∙ ▶ ι⇒ ι ▶ ι) ι

  pattern zero  = (_ , vz , ε)
  pattern suc n = (_ , vs vz , (n , ε))

  NatElim : (P : Nat → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
  NatElim P pz ps zero    = pz
  NatElim P pz ps (suc n) = ps n (NatElim P pz ps n)

--------------------------------------------------------------------------------

Tyᴹ : (A : Ty) → {X₀ X₁ : Set} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x → Tyᴹ A Xᴹ (α₀ x ) (α₁ (Xᴹ x))

Conᴹ : ∀ (Γ : Con){X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ Γ Xᴹ γ₀ γ₁ = ∀ A x → Tyᴹ A Xᴹ (γ₀ _ x) (γ₁ _ x)

Tmᴹ : ∀ {Γ A}(t : Tm Γ A){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Tyᴹ A Xᴹ (Tmᴬ t γ₀) (Tmᴬ t γ₁)
Spᴹ : ∀ {Γ A B}(sp : Sp Γ A B){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → {α₀ : Tyᴬ A X₀}{α₁ : Tyᴬ A X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁
      → Tyᴹ A Xᴹ α₀ α₁
      → Tyᴹ B Xᴹ (Spᴬ sp γ₀ α₀) (Spᴬ sp γ₁ α₁)
Tmᴹ (_ , x , sp) γᴹ = Spᴹ sp γᴹ (γᴹ _ x)
Spᴹ ε        γᴹ αᴹ = αᴹ
Spᴹ (t , sp) γᴹ αᴹ rewrite Tmᴹ t γᴹ ⁻¹ = Spᴹ sp γᴹ (αᴹ _)

Subᴹ : ∀ {Γ Δ}(σ : Sub Γ Δ){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Conᴹ Δ Xᴹ (Subᴬ σ γ₀) (Subᴬ σ γ₁)
Subᴹ σ γᴹ A x = Tmᴹ (σ _ x) γᴹ

--------------------------------------------------------------------------------

Tyᴰ : ∀ A {X} → (X → Set) → Tyᴬ A X → Set
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set) → Conᴬ Γ X → Set
Conᴰ Γ Xᴰ γ = ∀ A x → Tyᴰ A Xᴰ (γ _ x)

Tmᴰ : ∀ {Γ A}(t : Tm Γ A)
    → ∀ {X Xᴰ}{γ : Conᴬ Γ X}
    → Conᴰ Γ {X} Xᴰ γ
    → Tyᴰ A Xᴰ (Tmᴬ t γ)

Spᴰ : ∀ {Γ A B}(sp : Sp Γ A B)
      → ∀ {X Xᴰ}{γ : Conᴬ Γ X}{α : Tyᴬ A X}
      → Conᴰ Γ {X} Xᴰ γ
      → Tyᴰ A Xᴰ α
      → Tyᴰ B Xᴰ (Spᴬ sp γ α)
Tmᴰ (_ , x , sp) γ = Spᴰ sp γ (γ _ x)
Spᴰ ε        γ α = α
Spᴰ (t , sp) γ α = Spᴰ sp γ (α _ (Tmᴰ t γ))

Subᴰ : ∀ {Γ Δ}(σ : Sub Γ Δ) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Conᴰ Δ Xᴰ (Subᴬ σ γ)
Subᴰ σ γᴰ A x = Tmᴰ (σ _ x) γᴰ

--------------------------------------------------------------------------------

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set
Tyˢ ι      Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A) Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set
Conˢ Γ Xˢ γ γᴰ = ∀ {A} x → Tyˢ A Xˢ (γ _ x) (γᴰ _ x)

Tmˢ : ∀ {Γ A}(t : Tm Γ A){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Tyˢ A Xˢ (Tmᴬ t γ) (Tmᴰ t γᴰ)
Spˢ : ∀ {Γ A B}(sp : Sp Γ A B){X Xᴰ Xˢ}
      → {γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → {α : Tyᴬ A X}{αᴰ : Tyᴰ A Xᴰ α}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ
      → Tyˢ A Xˢ α αᴰ
      → Tyˢ B Xˢ (Spᴬ sp γ α) (Spᴰ sp γᴰ αᴰ)
Tmˢ (_ , x , sp) γˢ = Spˢ sp γˢ (γˢ x)
Spˢ ε        γˢ αˢ = αˢ
Spˢ (t , sp) γˢ αˢ rewrite Tmˢ t γˢ ⁻¹ = Spˢ sp γˢ (αˢ _)

Subˢ : ∀ {Γ Δ}(σ : Sub Γ Δ){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Conˢ Δ Xˢ (Subᴬ σ γ) (Subᴰ σ γᴰ)
Subˢ σ γˢ x = Tmˢ (σ _ x) γˢ

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (appₛ t (u , ε))

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ Γ ν A x = Tyᵀ A (ν _ x)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A) (ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (_ , x , sp) ν = {!!}

  Subᵀ : ∀ {Γ Δ}(σ : Sub Γ Δ)(ν : Sub Ω Γ) A x → Conᵀ Δ (σ ∘ ν) A x ≡ Subᴬ σ (Conᵀ Γ ν) A x
  Subᵀ σ ν A x = Tmᵀ (σ A x) ν

  -- weak initiality
  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω)
    Tyᴿ ι      t = refl
    Tyᴿ (ι⇒ A) t = λ x₀ → {!Tyᴿ A (appₛ t (x₀ , ε))!}

    Conᴿ : (Γ : Con)(ν : Sub Ω Γ) → Conᴹ Γ ιᴿ (Conᵀ Γ ν) (Subᴬ ν ω)
    Conᴿ Γ ν A x = Tyᴿ A (ν A x)

--   -- induction
--   module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω id)) where

--     lem : (t : Tm Ω ι) → Tmᴬ t (Conᵀ Ω id) ≡ t
--     lem t = (Tmᵀ t id) ⁻¹ ◾ [id]

--     ιᵉ : (t : Tm Ω ι) → Xᴰ t
--     ιᵉ t = tr Xᴰ (lem t) (Tmᴰ t ωᴰ)

--     Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id)) (Tmᴰ t ωᴰ)
--     Tyᵉ ι      t   =
--         apd⁻¹ ιᵉ (lem t)
--       ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl _ (lem t)
--     Tyᵉ (ι⇒ A) t =
--        λ x →
--        J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
--          (Tyᵉ A (app t x))
--          x (lem x)

--     Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω id)) (Subᴰ ν ωᴰ)
--     Conᵉ Γ ν {A} x = Tyᵉ A (ν _ x)


-- module _ (Ω : Con) where

--   Alg : Set₁
--   Alg = ∃ (Conᴬ Ω)

--   Mor : Alg → Alg → Set
--   Mor (X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

--   DispAlg : Alg → Set₁
--   DispAlg (X , ω) = ∃ λ Xᴰ → Conᴰ Ω Xᴰ ω

--   Section : (ω : Alg) → DispAlg ω → Set
--   Section (X , ω) (Xᴰ , ωᴰ) = ∃ λ Xˢ → Conˢ Ω Xˢ ω ωᴰ

--   TmAlg : Alg
--   TmAlg = ιᵀ Ω , Conᵀ Ω Ω id

--   Recursor : (ω : Alg) → Mor TmAlg ω
--   Recursor (X , ω) = ιᴿ Ω X ω , Conᴿ Ω X ω Ω id

--   Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
--   Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ Ω id

-- --------------------------------------------------------------------------------

-- NatSig = ∙ ▶ ι ▶ ι⇒ ι
-- NatSyn = TmAlg NatSig
-- Nat  = NatSyn .₁
-- zero = NatSyn .₂ _ (vs vz)
-- suc  = NatSyn .₂ _ vz

-- NatElim : (ωᴰ : DispAlg _ NatSyn) → ∀ n → ωᴰ .₁ n
-- NatElim ωᴰ = Elim NatSig ωᴰ .₁

-- zeroβ : ∀ ωᴰ → NatElim ωᴰ zero ≡ ωᴰ .₂ _ (vs vz)
-- zeroβ ωᴰ = refl

-- sucβ : ∀ n ωᴰ → NatElim ωᴰ (suc n) ≡ ωᴰ .₂ _ vz n (NatElim ωᴰ n)
-- sucβ n ωᴰ = Elim NatSig ωᴰ .₂ vz n -- not refl
