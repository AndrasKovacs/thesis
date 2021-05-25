
module Fix where

open import Lib hiding (_⊗_)

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

map : ∀ {F : Sig}{X₀ X₁} → (X₀ → X₁) → ⟦ F ⟧ X₀ → ⟦ F ⟧ X₁
map {Id}    f x         = f x
map {K⊤}    f x         = x
map {F ⊗ G} f (x₀ , x₁) = map f x₀ , map f x₁
map {F ⊕ G} f (inj₁ x)  = inj₁ (map f x)
map {F ⊕ G} f (inj₂ x)  = inj₂ (map f x)

data Fix (F : Sig) : Set where
  con : ⟦ F ⟧ (Fix F) → Fix F

{-# TERMINATING #-}
rec : ∀ {F X} → (⟦ F ⟧ X → X) → Fix F → X
rec f (con x) = f (map (rec f) x)
