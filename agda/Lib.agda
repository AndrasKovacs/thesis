
{-# OPTIONS --without-K --rewriting #-}

module Lib where

open import Relation.Binary.PropositionalEquality
  using (_≡_; refl)
  renaming (sym to infix 6 _⁻¹; trans to infixr 5 _◾_; subst to tr; cong to ap)
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
  hiding (Lift; lift; lower)
  public

open import Data.Sum
  using (_⊎_; inj₁; inj₂)
  public

record Lift {a} {ℓ} (A : Set a) : Set (a ⊔ ℓ) where
  constructor ↑
  field ↓ : A
open Lift public

{-# BUILTIN REWRITE _≡_ #-}

infixl 4 _⊗_
_⊗_ : ∀ {i j}{A : Set i}{B : Set j}{f g : A → B} → f ≡ g → ∀ {x y} → x ≡ y → f x ≡ g y
_⊗_ refl refl = refl

coe : ∀ {i}{A B : Set i} → A ≡ B → A → B
coe refl x = x

J : ∀ {i j}{A : Set i}{x : A}(P : ∀ y → x ≡ y → Set j) → P _ refl → ∀ {y} (e : x ≡ y) → P y e
J P pr refl = pr

J⁻¹ : ∀ {i j}{A : Set i}{x : A}(P : ∀ y → x ≡ y → Set j) → ∀ {y} (e : x ≡ y) → P y e → P _ refl
J⁻¹ P refl pe = pe

apd : ∀ {i j}{A : Set i}{B : A → Set j}(f : ∀ a → B a){x y} → (e : x ≡ y) → tr B e (f x) ≡ f y
apd f refl = refl

apd⁻¹ : ∀ {i j}{A : Set i}{B : A → Set j}(f : ∀ a → B a){x y} → (e : x ≡ y) → f x ≡ tr B (e ⁻¹)(f y)
apd⁻¹ f refl = refl

ap2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}{C : Set k}(f : ∀ a → B a → C)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → f a₀ b₀ ≡ f a₁ b₁
ap2 f refl refl = refl

happly : ∀ {i j}{A : Set i}{B : A → Set j}{f g : ∀ a → B a} → f ≡ g → ∀ x → f x ≡ g x
happly refl x = refl

inv : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → ((p ⁻¹) ◾ p) ≡ refl
inv refl = refl

inv⁻¹ : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → (p ◾ p ⁻¹) ≡ refl
inv⁻¹ refl = refl

tr2 :
  ∀ {i j k}{A : Set i}{B : A → Set j}(C : ∀ a → B a → Set k)
    {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁)
    {b₀ : B a₀}{b₁ : B a₁}(b₂ : tr B a₂ b₀ ≡ b₁)
  → C a₀ b₀ → C a₁ b₁
tr2 {B = B} C {a₀}{.a₀} refl refl c₀ = c₀

tr-const : ∀ {i j}{A : Set i}{B : Set j}{x y : A}(e : x ≡ y){b : B} → tr (λ _ → B) e b ≡ b
tr-const refl = refl

ap-id : ∀ {α}{A : Set α}{x y : A}(p : x ≡ y) → ap (λ x → x) p ≡ p
ap-id refl = refl

ap-const : ∀ {α β}{A : Set α}{B : Set β}(b : B){x y : A}(p : x ≡ y) → ap (λ _ → b) p ≡ refl
ap-const b refl = refl

ap-◾ : ∀ {α β}{A : Set α}{B : Set β}(f : A → B){x y z : A}(p : x ≡ y)(q : y ≡ z) → (ap f (p ◾ q)) ≡ (ap f p ◾ ap f q)
ap-◾ f refl refl = refl

tr-ap : ∀ {i j}{A A' : Set i}(B : A' → Set j)(f : A → A')
       {a₀ : A}{a₁ : A}(a₂ : a₀ ≡ a₁){b₀ : B (f a₀)}
     → tr (λ z → B (f z)) a₂ b₀ ≡ tr B (ap f a₂) b₀
tr-ap B f refl = refl

◾refl : ∀ {i}{A : Set i}{x y : A}(p : x ≡ y) → p ◾ refl ≡ p
◾refl refl = refl

◾-ass : ∀ {i}{A : Set i}{a b c d : A}(p : a ≡ b)(q : b ≡ c)(r : c ≡ d)
        → (p ◾ q) ◾ r ≡ p ◾ q ◾ r
◾-ass refl q refl = refl

-- {-# REWRITE ◾refl ◾-ass #-}

postulate
  ext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
          → ((x : A) → f x  ≡ g x) → _≡_ f g

  exti : ∀{i j}{A : Set i}{B : A → Set j}{f g : {x : A} → B x}
          → ((x : A) → f {x} ≡ g {x}) → _≡_ {A = {x : A} → B x} f g
