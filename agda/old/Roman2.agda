
{-# OPTIONS --type-in-type #-}

module _ (I : Set) where

open import Lib hiding (_⊗_)
infixr 4 _⊗_

data Desc : Set where
   sort : I → Desc
   _⊗_  : Desc → Desc → Desc
   π    : ∀ A → (A → Desc) → Desc
U = Desc

module _ (X : I → Set) where
  Uᴬ : U → Set
  Uᴬ (sort i) = X i
  Uᴬ (a ⊗ b)  = Uᴬ a × Uᴬ b
  Uᴬ (π A b)  = ∀ α → Uᴬ (b α)

  Descᴬ : Desc → I → Set
  Descᴬ (sort j) i = i ≡ j
  Descᴬ (a ⊗ B)  i = Uᴬ a × Descᴬ B i
  Descᴬ (π A B)  i = ∃ λ α → Descᴬ (B α) i

module _ {X : I → Set}(Xᴰ : ∀ {i} → X i → Set) where
  Uᴰ : ∀ (a : U) → Uᴬ X a → Set
  Uᴰ (sort i) x = Xᴰ x
  Uᴰ (a ⊗ b)  x = Uᴰ a (₁ x) × Uᴰ b (₂ x)
  Uᴰ (π A b)  x = ∀ α → Uᴰ (b α) (x α)

  Descᴰ : ∀ (A : Desc) → ∀ {i} → Descᴬ X A i → Set
  Descᴰ (sort i) p = ⊤
  Descᴰ (a ⊗ B)  x = Uᴰ a (₁ x) × Descᴰ B (₂ x)
  Descᴰ (π A B)  x = Descᴰ (B (₁ x)) (₂ x)

data Fix (A : Desc) i : Set where
  con : Descᴬ (Fix A) A i → Fix A i

module Elim A
  (P : ∀ {i} → Fix A i → Set)
  (f : ∀ {i x} → Descᴰ {Fix A} P A {i} x → P (con x)) where

  mutual
    elim : ∀ {i} x → P {i} x
    elim (con x) = f (go x)

    goU : ∀ {B} → (x : Uᴬ (Fix A) B) → Uᴰ P B x
    goU {sort j} x       = elim x
    goU {B ⊗ C}  (x , y) = goU {B} x , goU {C} y
    goU {π B C}  x       = λ α → goU {C α} (x α)

    go : ∀ {B i} x → Descᴰ P B {i} x
    go {sort j} x       = tt
    go {B ⊗ C}  (x , y) = goU {B} x , go y
    go {π B C}  (b , x) = go {C b} x
