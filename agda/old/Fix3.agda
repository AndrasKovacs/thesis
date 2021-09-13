
{-# OPTIONS --postfix-projections #-}

module Fix3 where

open import Lib hiding (_⊗_)

open import Function using (_∘_)

infixr 4 _⊗_ _⊕_



data Sig : Set where
  Id  : Sig
  K⊤  : Sig
  _⊗_ : Sig → Sig → Sig
  _⊕_ : Sig → Sig → Sig

⟦_⟧ : Sig → Set → Set
⟦ Id    ⟧ X = X
⟦ K⊤    ⟧ X = ⊤
⟦ F ⊗ G ⟧ X = ⟦ F ⟧ X × ⟦ G ⟧ X
⟦ F ⊕ G ⟧ X = ⟦ F ⟧ X ⊎ ⟦ G ⟧ X

⟦_⟧ᴰ : ∀ (F : Sig){X}(Xᴰ : X → Set) → ⟦ F ⟧ X → Set
⟦ Id    ⟧ᴰ Xᴰ x        = Xᴰ x
⟦ K⊤    ⟧ᴰ Xᴰ x        = ⊤
⟦ F ⊗ G ⟧ᴰ Xᴰ x        = ⟦ F ⟧ᴰ Xᴰ (x .₁) × ⟦ G ⟧ᴰ Xᴰ (x .₂)
⟦ F ⊕ G ⟧ᴰ Xᴰ (inj₁ x) = ⟦ F ⟧ᴰ Xᴰ x
⟦ F ⊕ G ⟧ᴰ Xᴰ (inj₂ y) = ⟦ G ⟧ᴰ Xᴰ y

-- ⟦_⟧ˢ : ∀ F {X}{Xᴰ : X → Set}(Xˢ : ∀ x → Xᴰ x)(x : ⟦ F ⟧ X) → ⟦ F ⟧ᴰ Xᴰ x → Set
-- ⟦ Id    ⟧ˢ Xˢ x        xᴰ = Xˢ x ≡ xᴰ
-- ⟦ K⊤    ⟧ˢ Xˢ x        xᴰ = ⊤
-- ⟦ F ⊗ G ⟧ˢ Xˢ x        xᴰ = ⟦ F ⟧ˢ Xˢ (x .₁) (xᴰ .₁) × ⟦ G ⟧ˢ Xˢ (x .₂) (xᴰ .₂)
-- ⟦ F ⊕ G ⟧ˢ Xˢ (inj₁ x) xᴰ = ⟦ F ⟧ˢ Xˢ x xᴰ
-- ⟦ F ⊕ G ⟧ˢ Xˢ (inj₂ x) xᴰ = ⟦ G ⟧ˢ Xˢ x xᴰ

data Fix (F : Sig) : Set where
  con : ⟦ F ⟧ (Fix F) → Fix F

Alg : Sig → Set₁
Alg F = ∃ λ X → ⟦ F ⟧ X → X

Disp : ∀ {F} → Alg F → Set₁
Disp {F} (X , f) = ∃ λ Xᴰ → ∀ {x}(xᴰ : ⟦ F ⟧ᴰ {X} Xᴰ x) → Xᴰ (f x)

Syn : ∀ F → Alg F
Syn F = Fix F , con

module Elim {F}(P : Fix F → Set)(f : ∀ {x}(xᴰ : ⟦ F ⟧ᴰ P x) → P (con x)) where

  mutual
    elim : ∀ x → P x
    elim (con x) = f (go x)

    go : ∀ {G}(x : ⟦ G ⟧ (Fix F)) → ⟦ G ⟧ᴰ P x
    go {Id}    x        = elim x
    go {K⊤}    x        = x
    go {G ⊗ H} x        = go (x .₁) , go (x .₂)
    go {G ⊕ H} (inj₁ x) = go x
    go {G ⊕ H} (inj₂ x) = go x








-- map : ∀ {F : Sig}{X₀ X₁} → (X₀ → X₁) → ⟦ F ⟧ X₀ → ⟦ F ⟧ X₁
-- map {Id}    f x         = f x
-- map {K⊤}    f x         = x
-- map {F ⊗ G} f (x₀ , x₁) = map f x₀ , map f x₁
-- map {F ⊕ G} f (inj₁ x)  = inj₁ (map f x)
-- map {F ⊕ G} f (inj₂ x)  = inj₂ (map f x)

-- data Fix (F : Sig) : Set where
--   con : ⟦ F ⟧ (Fix F) → Fix F

-- module Rec1 where
--   {-# TERMINATING #-}
--   rec : ∀ {F X} → (⟦ F ⟧ X → X) → Fix F → X
--   rec f (con x) = f (map (rec f) x)

-- module Rec2 (F : Sig) {X}(alg : ⟦ F ⟧ X → X) where

--   mutual
--     rec : Fix F → X
--     rec (con x) = alg (maprec x)

--     maprec : ∀ {G} → ⟦ G ⟧ (Fix F) → ⟦ G ⟧ X
--     maprec {Id}    gx        = rec gx
--     maprec {K⊤}    gx        = gx
--     maprec {G ⊗ H} (gx , hx) = maprec gx , maprec hx
--     maprec {G ⊕ H} (inj₁ gx) = inj₁ (maprec gx)
--     maprec {G ⊕ H} (inj₂ hx) = inj₂ (maprec hx)
