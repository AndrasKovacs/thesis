

{-# OPTIONS --without-K --safe #-}

module SimpleInductive6FirstOrder where

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

wkTm : ∀ {Γ A B} → Tm Γ A → Tm (Γ ▶ B) A
wkTm (var x)   = var (vs x)
wkTm (app t u) = app (wkTm t) (wkTm u)

data Sub (Γ : Con) : Con → Set where
  ε   : Sub Γ ∙
  _,_ : ∀ {Δ A} → Sub Γ Δ → Tm Γ A → Sub Γ (Δ ▶ A)

lookup : ∀ {Γ Δ A} → Var Δ A → Sub Γ Δ → Tm Γ A
lookup vz     (σ , t) = t
lookup (vs x) (σ , t) = lookup x σ

infix 5 _[_]
_[_] : ∀ {Γ Δ A} → Tm Δ A → Sub Γ Δ → Tm Γ A
var x   [ σ ] = lookup x σ
app t u [ σ ] = app (t [ σ ]) (u [ σ ])

wkSub : ∀ {Γ Δ A} → Sub Γ Δ → Sub (Γ ▶ A) Δ
wkSub ε       = ε
wkSub (σ , t) = wkSub σ , wkTm t

id : ∀ {Γ} → Sub Γ Γ
id {∙}     = ε
id {Γ ▶ A} = wkSub id , var vz

lookup-wkSub : ∀ {Γ Δ A B x σ}
              → lookup {A = A} x (wkSub {Γ}{Δ}{B} σ) ≡ wkTm (lookup x σ)
lookup-wkSub {x = vz}   {σ , t} = refl
lookup-wkSub {x = vs x} {σ , t} = lookup-wkSub {x = x}{σ}

lookup-id : ∀ {Γ A x} → lookup {Γ}{Γ}{A} x id ≡ var x
lookup-id {x = vz}   = refl
lookup-id {x = vs x} = lookup-wkSub {x = x}{id} ◾ wkTm & lookup-id {x = x}

[id] : ∀ {Γ A}{t : Tm Γ A} → t [ id ] ≡ t
[id] {t = var x}   = lookup-id {x = x}
[id] {t = app t u} = app & [id] ⊗ [id]

infixr 5 _∘_
_∘_ : ∀ {Γ Δ Ξ} → Sub Δ Ξ → Sub Γ Δ → Sub Γ Ξ
ε       ∘ δ = ε
(σ , t) ∘ δ = (σ ∘ δ) , (t [ δ ])

------------------------------------------------------------

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ ∙       X = ⊤
Conᴬ (Γ ▶ A) X = Conᴬ Γ X × Tyᴬ A X

Tmᴬ : ∀ {Γ A} → Tm Γ A → ∀ {X} → Conᴬ Γ X → Tyᴬ A X
Tmᴬ (var vz)     (γ , α) = α
Tmᴬ (var (vs x)) (γ , α) = Tmᴬ (var x) γ
Tmᴬ (app t u)    γ       = Tmᴬ t γ (Tmᴬ u γ)

Subᴬ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {X} → Conᴬ Γ X → Conᴬ Δ X
Subᴬ ε       γ = tt
Subᴬ (σ , t) γ = (Subᴬ σ γ) , (Tmᴬ t γ)

--------------------------------------------------------------------------------

Tyᴹ : (A : Ty) → {X₀ X₁ : Set} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x → Tyᴹ A Xᴹ (α₀ x ) (α₁ (Xᴹ x))

Conᴹ : ∀ (Γ : Con){X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ ∙       Xᴹ γ₀        γ₁        = ⊤
Conᴹ (Γ ▶ A) Xᴹ (γ₀ , α₀) (γ₁ , α₁) = Conᴹ Γ Xᴹ γ₀ γ₁ × Tyᴹ A Xᴹ α₀ α₁

Tmᴹ : ∀ {Γ A}(t : Tm Γ A){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Tyᴹ A Xᴹ (Tmᴬ t γ₀) (Tmᴬ t γ₁)
Tmᴹ (var vz)     (γᴹ , αᴹ) = αᴹ
Tmᴹ (var (vs x)) (γᴹ , αᴹ) = Tmᴹ (var x) γᴹ
Tmᴹ (app t u) γᴹ rewrite Tmᴹ u γᴹ ⁻¹ = Tmᴹ t γᴹ (Tmᴬ u _)

Subᴹ : ∀ {Γ Δ}(σ : Sub Γ Δ){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Conᴹ Δ Xᴹ (Subᴬ σ γ₀) (Subᴬ σ γ₁)
Subᴹ ε       γᴹ = tt
Subᴹ (σ , t) γᴹ = (Subᴹ σ γᴹ) , (Tmᴹ t γᴹ)

--------------------------------------------------------------------------------

Tyᴰ : ∀ A {X} → (X → Set) → Tyᴬ A X → Set
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set) → Conᴬ Γ X → Set
Conᴰ ∙       Xᴰ γ       = ⊤
Conᴰ (Γ ▶ A) Xᴰ (γ , α) = Conᴰ Γ Xᴰ γ × Tyᴰ A Xᴰ α

Tmᴰ : ∀ {Γ A}(t : Tm Γ A) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Tyᴰ A Xᴰ (Tmᴬ t γ)
Tmᴰ (var vz)     (γᴰ , αᴰ) = αᴰ
Tmᴰ (var (vs x)) (γᴰ , αᴰ) = Tmᴰ (var x) γᴰ
Tmᴰ (app t u)    γᴰ        = Tmᴰ t γᴰ (Tmᴬ u _) (Tmᴰ u γᴰ)

Subᴰ : ∀ {Γ Δ}(σ : Sub Γ Δ) → ∀ {X Xᴰ}{γ : Conᴬ Γ X} → Conᴰ Γ {X} Xᴰ γ → Conᴰ Δ Xᴰ (Subᴬ σ γ)
Subᴰ ε       γᴰ = tt
Subᴰ (σ , t) γᴰ = (Subᴰ σ γᴰ) , (Tmᴰ t γᴰ)

--------------------------------------------------------------------------------

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set
Tyˢ ι      Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A) Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set
Conˢ ∙       Xˢ γ       γᴰ        = ⊤
Conˢ (Γ ▶ A) Xˢ (γ , α) (γᴰ , αᴰ) = Conˢ Γ Xˢ γ γᴰ × Tyˢ A Xˢ α αᴰ

Tmˢ : ∀ {Γ A}(t : Tm Γ A){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Tyˢ A Xˢ (Tmᴬ t γ) (Tmᴰ t γᴰ)
Tmˢ (var vz)     (γˢ , αˢ) = αˢ
Tmˢ (var (vs x)) (γˢ , αˢ) = Tmˢ (var x) γˢ
Tmˢ (app t u) γˢ rewrite Tmˢ u γˢ ⁻¹ = Tmˢ t γˢ (Tmᴬ u _)

Subˢ : ∀ {Γ Δ}(σ : Sub Γ Δ){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Conˢ Δ Xˢ (Subᴬ σ γ) (Subᴰ σ γᴰ)
Subˢ ε       γˢ = tt
Subˢ (σ , t) γˢ = Subˢ σ γˢ , Tmˢ t γˢ

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω ι

  Tyᵀ : (A : Ty) → Tm Ω A → Tyᴬ A ιᵀ
  Tyᵀ ι      t = t
  Tyᵀ (ι⇒ A) t = λ u → Tyᵀ A (app t u)

  Conᵀ : (Γ : Con) → Sub Ω Γ → Conᴬ Γ ιᵀ
  Conᵀ ∙       ν       = tt
  Conᵀ (Γ ▶ A) (ν , t) = (Conᵀ Γ ν) , (Tyᵀ A t)

  Tmᵀ : ∀ {Γ A}(t : Tm Γ A)(ν : Sub Ω Γ) → Tyᵀ A (t [ ν ]) ≡ Tmᴬ t (Conᵀ Γ ν)
  Tmᵀ (var vz)     (ν , t) = refl
  Tmᵀ (var (vs x)) (ν , t) = Tmᵀ (var x) ν
  Tmᵀ (app t u)    ν       = Tmᵀ t ν ⊗ Tmᵀ u ν

  Subᵀ : ∀ {Γ Δ}(σ : Sub Γ Δ)(ν : Sub Ω Γ) → Conᵀ Δ (σ ∘ ν) ≡ Subᴬ σ (Conᵀ Γ ν)
  Subᵀ ε       ν = refl
  Subᵀ (σ , t) ν rewrite Subᵀ σ ν | Tmᵀ t ν = refl

  -- weak initiality
  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : (A : Ty)(t : Tm Ω A) → Tyᴹ A ιᴿ (Tyᵀ A t) (Tmᴬ t ω)
    Tyᴿ ι      t = refl
    Tyᴿ (ι⇒ A) t = λ u → Tyᴿ A (app t u)

    Conᴿ : (Γ : Con)(ν : Sub Ω Γ) → Conᴹ Γ ιᴿ (Conᵀ Γ ν) (Subᴬ ν ω)
    Conᴿ ∙       ν       = tt
    Conᴿ (Γ ▶ A) (ν , t) = (Conᴿ Γ ν) , (Tyᴿ A t)

  -- induction
  module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ (Conᵀ Ω id)) where

    lem : (t : Tm Ω ι) → Tmᴬ t (Conᵀ Ω id) ≡ t
    lem t = (Tmᵀ t id) ⁻¹ ◾ [id]

    ιᵉ : (t : Tm Ω ι) → Xᴰ t
    ιᵉ t = tr Xᴰ (lem t) (Tmᴰ t ωᴰ)

    Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id)) (Tmᴰ t ωᴰ)
    Tyᵉ ι      t   =
        apd⁻¹ ιᵉ (lem t)
      ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl _ (lem t)
    Tyᵉ (ι⇒ A) t =
       λ x →
       J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
         (Tyᵉ A (app t x))
         x (lem x)

    Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω id)) (Subᴰ ν ωᴰ)
    Conᵉ ∙       ν       = tt
    Conᵉ (Γ ▶ A) (ν , t) = (Conᵉ Γ ν) , (Tyᵉ A t)

wkTmᴬ : ∀ {Γ Δ A X t γ α} → Tmᴬ (wkTm {Γ}{Δ}{A} t) {X} (γ , α) ≡ Tmᴬ t γ
wkTmᴬ {t = var x} = refl
wkTmᴬ {t = app t u}{γ}{α} rewrite wkTmᴬ {t = t}{γ}{α} | wkTmᴬ {t = u}{γ}{α} = refl

wkSubᴬ : ∀ {Γ Δ A X σ γ α} → Subᴬ (wkSub {Γ}{Δ}{A} σ) {X} (γ , α) ≡ Subᴬ σ γ
wkSubᴬ {σ = ε}     = refl
wkSubᴬ {σ = σ , t} {γ}{α} rewrite wkSubᴬ {σ = σ}{γ}{α} | wkTmᴬ {t = t}{γ}{α} = refl

idᴬ : ∀ {Γ X}{ω : Conᴬ Γ X} → Subᴬ (id {Γ}) ω ≡ ω
idᴬ {∙}     = refl
idᴬ {Γ ▶ A} {_} {γ , α} rewrite wkSubᴬ {σ = id{Γ}} {γ}{α} | idᴬ {Γ = Γ}{_}{γ} = refl

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
  Recursor (X , ω) =
    ιᴿ Ω X ω , coe (Conᴹ Ω (λ t → Tmᴬ t ω) (Conᵀ Ω Ω id) & idᴬ)
                   (Conᴿ Ω X ω Ω id)

  Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
  Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , {!Conᵉ Ω Xᴰ ωᴰ Ω id!} --Conᵉ Ω Xᴰ ωᴰ Ω id

--------------------------------------------------------------------------------

NatSig = ∙ ▶ ι ▶ ι⇒ ι
NatSyn = TmAlg NatSig
Nat  = NatSyn .₁
zero = NatSyn .₂ .₂
suc  = NatSyn .₂ .₁ .₂

NatRec : (ω : Alg NatSig) → Mor NatSig NatSyn ω
NatRec ω = Recursor NatSig ω

-- NatElim : (ωᴰ : DispAlg _ NatSyn) → ∀ n → ωᴰ .₁ n
-- NatElim ωᴰ = Elim NatSig ωᴰ .₁

-- zeroβ : ∀ ωᴰ → NatElim ωᴰ zero ≡ ωᴰ .₂ _ (vs vz)
-- zeroβ ωᴰ = refl

-- sucβ : ∀ n ωᴰ → NatElim ωᴰ (suc n) ≡ ωᴰ .₂ _ vz n (NatElim ωᴰ n)
-- sucβ n ωᴰ = Elim NatSig ωᴰ .₂ vz n -- not refl
