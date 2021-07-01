
{-# OPTIONS --safe #-}

module SpineTm6 where

open import Lib
open import Function using (_∋_)
open import Data.Empty

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
  Tm : Con → Set
  Tm Γ = ∃ λ A → Var Γ A × Sp Γ A ι

  data Sp (Γ : Con) : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _$_ : ∀ {A B} → Sp Γ A (ι⇒ B) → Tm Γ → Sp Γ A B
infixl 8 _$_

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ A → Var Γ A → Tyᴬ A X

Tmᴬ : ∀ {Γ}     → Tm Γ     → ∀ {X} → Conᴬ Γ X → X
Spᴬ : ∀ {Γ A B} → Sp Γ A B → ∀ {X} → Conᴬ Γ X → Tyᴬ A X → Tyᴬ B X
Tmᴬ (B , x , sp) γ   = Spᴬ sp γ (γ _ x)
Spᴬ ε            γ α = α
Spᴬ (sp $ t)     γ α = Spᴬ sp γ α (Tmᴬ t γ)

Tyᴹ : (A : Ty) → {X₀ X₁ : Set} → (X₀ → X₁) → Tyᴬ A X₀ → Tyᴬ A X₁ → Set
Tyᴹ ι      Xᴹ α₀ α₁ = Xᴹ α₀ ≡ α₁
Tyᴹ (ι⇒ A) Xᴹ α₀ α₁ = ∀ x → Tyᴹ A Xᴹ (α₀ x ) (α₁ (Xᴹ x))

Conᴹ : ∀ (Γ : Con){X₀ X₁} → (X₀ → X₁) → Conᴬ Γ X₀ → Conᴬ Γ X₁ → Set
Conᴹ Γ Xᴹ γ₀ γ₁ = ∀ A x → Tyᴹ A Xᴹ (γ₀ _ x) (γ₁ _ x)

Tmᴹ : ∀ {Γ}(t : Tm Γ){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁ → Xᴹ (Tmᴬ t γ₀) ≡ Tmᴬ t γ₁
Spᴹ : ∀ {Γ A B}(sp : Sp Γ A B){X₀ X₁ Xᴹ}{γ₀ : Conᴬ Γ X₀}{γ₁ : Conᴬ Γ X₁}
      → {α₀ : Tyᴬ A X₀}{α₁ : Tyᴬ A X₁}
      → Conᴹ Γ Xᴹ γ₀ γ₁
      → Tyᴹ A Xᴹ α₀ α₁
      → Tyᴹ B Xᴹ (Spᴬ sp γ₀ α₀) (Spᴬ sp γ₁ α₁)
Tmᴹ (_ , x , sp) γᴹ = Spᴹ sp γᴹ (γᴹ _ x)
Spᴹ ε         γᴹ αᴹ = αᴹ
Spᴹ (sp $ t)  γᴹ αᴹ rewrite Tmᴹ t γᴹ ⁻¹ = Spᴹ sp γᴹ αᴹ _

Tyᴰ : ∀ A {X} → (X → Set) → Tyᴬ A X → Set
Tyᴰ ι      Xᴰ α = Xᴰ α
Tyᴰ (ι⇒ A) Xᴰ α = ∀ x (xᴰ : Xᴰ x) → Tyᴰ A Xᴰ (α x)

Conᴰ : ∀ Γ {X} → (X → Set) → Conᴬ Γ X → Set
Conᴰ Γ Xᴰ γ = ∀ A x → Tyᴰ A Xᴰ (γ _ x)

Tmᴰ : ∀ {Γ}(t : Tm Γ){X Xᴰ γ} → Conᴰ Γ {X} Xᴰ γ → Xᴰ (Tmᴬ t γ)
Spᴰ : ∀ {Γ A B}(sp : Sp Γ A B){X Xᴰ γ α} → Conᴰ Γ {X} Xᴰ γ → Tyᴰ A Xᴰ α → Tyᴰ B Xᴰ (Spᴬ sp γ α)
Tmᴰ (_ , x , sp) γᴰ = Spᴰ sp γᴰ (γᴰ _ x)
Spᴰ ε        γᴰ α = α
Spᴰ (sp $ t) γᴰ α = Spᴰ sp γᴰ α _ (Tmᴰ t γᴰ)

Tyˢ : ∀ A {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(α : Tyᴬ A X) → Tyᴰ A Xᴰ α → Set
Tyˢ ι      Xˢ α αᴰ = Xˢ α ≡ αᴰ
Tyˢ (ι⇒ A) Xˢ α αᴰ = ∀ x → Tyˢ A Xˢ (α x) (αᴰ x (Xˢ x))

Conˢ : ∀ Γ {X Xᴰ}(Xˢ : ∀ x → Xᴰ x)(γ : Conᴬ Γ X) → Conᴰ Γ Xᴰ γ → Set
Conˢ Γ Xˢ γ γᴰ = ∀ {A} x → Tyˢ A Xˢ (γ _ x) (γᴰ _ x)

Tmˢ : ∀ {Γ}(t : Tm Γ){X Xᴰ Xˢ}{γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ → Xˢ (Tmᴬ t γ) ≡ Tmᴰ t γᴰ
Spˢ : ∀ {Γ A B}(sp : Sp Γ A B){X Xᴰ Xˢ}
      → {γ : Conᴬ Γ X}{γᴰ : Conᴰ Γ Xᴰ γ}
      → {α : Tyᴬ A X}{αᴰ : Tyᴰ A Xᴰ α}
      → Conˢ Γ {X}{Xᴰ} Xˢ γ γᴰ
      → Tyˢ A Xˢ α αᴰ
      → Tyˢ B Xˢ (Spᴬ sp γ α) (Spᴰ sp γᴰ αᴰ)
Tmˢ (_ , x , sp) γˢ = Spˢ sp γˢ (γˢ x)
Spˢ ε        γˢ αˢ = αˢ
Spˢ (sp $ t) γˢ αˢ rewrite Tmˢ t γˢ ⁻¹ = Spˢ sp γˢ αˢ _

--------------------------------------------------------------------------------

module _ (Ω : Con) where

  ιᵀ : Set
  ιᵀ = Tm Ω

  Tyᵀ : ∀{A} B → Var Ω A → Sp Ω A B → Tyᴬ B ιᵀ
  Tyᵀ ι      x sp = _ , x , sp
  Tyᵀ (ι⇒ A) x sp = λ u → Tyᵀ A x (sp $ u)

  Conᵀ : Conᴬ Ω ιᵀ
  Conᵀ A x = Tyᵀ A x ε

  -- weak initiality
  module _ (X : Set)(ω : Conᴬ Ω X) where

    ιᴿ : ιᵀ → X
    ιᴿ t = Tmᴬ t ω

    Tyᴿ : ∀ {A} B (x : Var Ω A)(sp : Sp Ω A B) → Tyᴹ B ιᴿ (Tyᵀ B x sp) (Spᴬ sp ω (ω _ x))
    Tyᴿ ι      x sp = refl
    Tyᴿ (ι⇒ B) x sp = λ u → Tyᴿ B x (sp $ u)

    Conᴿ : Conᴹ Ω ιᴿ Conᵀ ω
    Conᴿ A x = Tyᴿ A x ε

  -- induction
  module _ (Xᴰ : ιᵀ → Set)(ωᴰ : Conᴰ Ω Xᴰ Conᵀ) where

    lem0 : ∀ {Γ A} → Sp Γ A (ι⇒ A) → ⊥
    lem0 (sp $ x) = {!lem0 !}

    sprefl : ∀ {Γ A B} → (e : A ≡ B) → (sp : Sp Γ A B) → sp ≡ tr (λ x → Sp Γ A x) e ε
    sprefl refl ε = refl
    sprefl refl (sp $ x) = {!!}



    lem : ∀ {A x sp} → Spᴬ sp Conᵀ (Tyᵀ A x ε) ≡ (Tm Ω ∋ (A , x , sp))
    lem {ι} {x} {sp} rewrite sprefl {A = ι} refl sp = refl
    lem {ι⇒ A} {x} {sp} = {!lem {A}!}


    ιᵉ  : (t : Tm Ω) → Xᴰ t
    ιᵉ (A , x , sp) = {!!}
    -- Spᵉ : ∀ {A B α}(sp : Sp Ω A B) → Tyᴰ A Xᴰ α → Tyᴰ B Xᴰ (Spᴬ sp Conᵀ α)
    -- ιᵉ (A , x , sp) = {!Spᵉ sp (ωᴰ _ x)!}
    -- Spᵉ sp = {!!}





-- -- --     Tyᵉ : (A : Ty)(t : Tm Ω A) → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id)) (Tmᴰ t ωᴰ)
-- -- --     Tyᵉ ι      t   =
-- -- --         apd⁻¹ ιᵉ (lem t)
-- -- --       ◾ J (λ y e → tr Xᴰ (e ⁻¹) (tr Xᴰ e (Tmᴰ t ωᴰ)) ≡ Tmᴰ t ωᴰ) refl _ (lem t)
-- -- --     Tyᵉ (ι⇒ A) t =
-- -- --        λ x →
-- -- --        J (λ x' e → Tyˢ A ιᵉ (Tmᴬ t (Conᵀ Ω id) x') (Tmᴰ t ωᴰ x' (tr Xᴰ e (Tmᴰ x ωᴰ))))
-- -- --          (Tyᵉ A (app t x))
-- -- --          x (lem x)

-- -- --     Conᵉ : (Γ : Con)(ν : Sub Ω Γ) → Conˢ Γ ιᵉ (Subᴬ ν (Conᵀ Ω id)) (Subᴰ ν ωᴰ)
-- -- --     Conᵉ Γ ν {A} x = Tyᵉ A (ν _ x)


-- -- -- module _ (Ω : Con) where

-- -- --   Alg : Set₁
-- -- --   Alg = ∃ (Conᴬ Ω)

-- -- --   Mor : Alg → Alg → Set
-- -- --   Mor (X₀ , ω₀) (X₁ , ω₁) = ∃ λ Xᴹ → Conᴹ Ω Xᴹ ω₀ ω₁

-- -- --   DispAlg : Alg → Set₁
-- -- --   DispAlg (X , ω) = ∃ λ Xᴰ → Conᴰ Ω Xᴰ ω

-- -- --   Section : (ω : Alg) → DispAlg ω → Set
-- -- --   Section (X , ω) (Xᴰ , ωᴰ) = ∃ λ Xˢ → Conˢ Ω Xˢ ω ωᴰ

-- -- --   TmAlg : Alg
-- -- --   TmAlg = ιᵀ Ω , Conᵀ Ω Ω id

-- -- --   Recursor : (ω : Alg) → Mor TmAlg ω
-- -- --   Recursor (X , ω) = ιᴿ Ω X ω , Conᴿ Ω X ω Ω id

-- -- --   Elim : (ωᴰ : DispAlg TmAlg) → Section TmAlg ωᴰ
-- -- --   Elim (Xᴰ , ωᴰ) = ιᵉ Ω Xᴰ ωᴰ , Conᵉ Ω Xᴰ ωᴰ Ω id

-- -- -- --------------------------------------------------------------------------------

-- -- -- NatSig = ∙ ▶ ι ▶ ι⇒ ι
-- -- -- NatSyn = TmAlg NatSig
-- -- -- Nat  = NatSyn .₁
-- -- -- zero = NatSyn .₂ _ (vs vz)
-- -- -- suc  = NatSyn .₂ _ vz

-- -- -- NatElim : (ωᴰ : DispAlg _ NatSyn) → ∀ n → ωᴰ .₁ n
-- -- -- NatElim ωᴰ = Elim NatSig ωᴰ .₁

-- -- -- zeroβ : ∀ ωᴰ → NatElim ωᴰ zero ≡ ωᴰ .₂ _ (vs vz)
-- -- -- zeroβ ωᴰ = refl

-- -- -- sucβ : ∀ n ωᴰ → NatElim ωᴰ (suc n) ≡ ωᴰ .₂ _ vz n (NatElim ωᴰ n)
-- -- -- sucβ n ωᴰ = Elim NatSig ωᴰ .₂ vz n -- not refl
