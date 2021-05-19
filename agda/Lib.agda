{-# OPTIONS --without-K --safe #-}

module Lib where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (sym to infix 6 _⁻¹; trans to infixr 5 _◾_; subst to tr; cong to infixl 9 _&_)
  public

open import Data.Unit
  using (⊤; tt)
  public

open import Data.Product
  using (Σ; ∃; ∃₂; _,_; _×_)
  renaming (proj₁ to ₁; proj₂ to ₂)
  public

open import Level
  renaming (zero to lz; suc to ls)
  public

infixl 4 _⊗_
_⊗_ : ∀ {i j}{A : Set i}{B : Set j}{f g : A → B} → f ≡ g → ∀ {x y} → x ≡ y → f x ≡ g y
_⊗_ refl refl = refl

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

J : ∀ {i j}{A : Set i}{x : A}(P : ∀ y → x ≡ y → Set j) → P _ refl → ∀ y (e : x ≡ y) → P y e
J P pr _ refl = pr

apd : ∀ {i j}{A : Set i}{B : A → Set j}(f : ∀ a → B a){x y} → (e : x ≡ y) → tr B e (f x) ≡ f y
apd f refl = refl

apd⁻¹ : ∀ {i j}{A : Set i}{B : A → Set j}(f : ∀ a → B a){x y} → (e : x ≡ y) → f x ≡ tr B (e ⁻¹)(f y)
apd⁻¹ f refl = refl

happly : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a} → f ≡ g → ∀ x → f x ≡ g x
happly refl x = refl
