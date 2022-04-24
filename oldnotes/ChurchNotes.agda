{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; sym to infixl 6 _⁻¹; subst to tr; trans to infixr 4 _◾_)
open import Data.Product
  renaming (proj₁ to ₁; proj₂ to ₂)

--------------------------------------------------------------------------------

NatAlg : Set
NatAlg = Σ Set λ N → (N → N) × N

NatHom : NatAlg → NatAlg → Set
NatHom (N₀ , s₀ , z₀) (N₁ , s₁ , z₁) =
  Σ (N₀ → N₁) λ Nᴹ → (∀ x → Nᴹ (s₀ x) ≡ s₁ (Nᴹ x)) × Nᴹ z₀ ≡ z₁


-- Church encoding: term model construction from the impredicative Set model of
-- signatures.
--------------------------------------------------------------------------------

-- Select components of the Set model

Conˢ : Set
Conˢ = Set    -- Set1

Subˢ : Conˢ → Conˢ → Set
Subˢ A₀ A₁ = (A₀ → A₁)     -- Set

Uˢ : Conˢ
Uˢ = Set                   -- Set1

Tyˢ : Conˢ → Set
Tyˢ A = (A → Set)

Tmˢ : (Γ : Conˢ) → Tyˢ Γ → Set
Tmˢ A Aᴰ = (∀ x → Aᴰ x)    --

Elˢ : ∀ {Γ} → Subˢ Γ Uˢ → Tyˢ Γ
Elˢ {A}(Aᴹ) = Aᴹ

_⇒ˢ_ : ∀ {Γ} → Subˢ Γ Uˢ → Tyˢ Γ → Tyˢ Γ; infixr 3 _⇒ˢ_
a ⇒ˢ B = (λ x → a x → B x)

appˢ : ∀ {Γ a B} → Tmˢ Γ (a ⇒ˢ B) → Tmˢ Γ (Elˢ a) → Tmˢ Γ B
appˢ {Γ}{a}{B} t u = (λ x → t x (u x))

NatSigˢ : Conˢ
NatSigˢ = NatAlg

Nˢ : Subˢ NatSigˢ Uˢ
Nˢ = (λ {(N , _ , _) → N})

sˢ : Tmˢ NatSigˢ (Nˢ ⇒ˢ Elˢ Nˢ)
sˢ = (λ {(_ , s , _) → s})

zˢ : Tmˢ NatSigˢ (Elˢ Nˢ)
zˢ = (λ {(_ , _ , z) → z})

module Church where

  N : Set
  N = Tmˢ NatSigˢ (Elˢ Nˢ)

  s : N → N
  s n = appˢ {B = Elˢ Nˢ} sˢ n

  z : N
  z = zˢ

  alg : NatAlg
  alg = N , s , z

  rec : (Γ : NatAlg) → NatHom alg Γ
  rec Γ = (λ n → n Γ) , (λ n → refl) , refl


-- Awodey-Frey-Speight encoding: term model construction in from the
-- impredicative graph model of ToS.
--------------------------------------------------------------------------------

-- Select components of the graph model

Conᴳ : Set
Conᴳ = Σ Conˢ λ A → (A → A → Set)

Subᴳ : Conᴳ → Conᴳ → Set
Subᴳ (A₀ , R₀) (A₁ , R₁) =
  Σ (A₀ → A₁) λ Aᴹ → ∀ {x y} → R₀ x y → R₁ (Aᴹ x) (Aᴹ y)

Uᴳ : Conᴳ
Uᴳ = Set , λ A B → A → B

Tyᴳ : Conᴳ → Set
Tyᴳ (A , R) =
  Σ (A → Set) λ Aᴰ → ∀ {x} → Aᴰ x → ∀ {y} → Aᴰ y → R x y → Set

Tmᴳ : (Γ : Conᴳ) → Tyᴳ Γ → Set
Tmᴳ (A , R) (Aᴰ , Rᴰ) =
  Σ (∀ x → Aᴰ x) λ Aˢ → ∀ {x y} f → Rᴰ (Aˢ x) (Aˢ y) f

Elᴳ : ∀ {Γ} → Subᴳ Γ Uᴳ → Tyᴳ Γ
Elᴳ {A , R}(Aᴹ , Rᴹ) = Aᴹ , (λ xx yy f → Rᴹ f xx ≡ yy)

_⇒ᴳ_ : ∀ {Γ} → Subᴳ Γ Uᴳ → Tyᴳ Γ → Tyᴳ Γ; infixr 3 _⇒ᴳ_
a ⇒ᴳ B =
  (λ x → ₁ a x → ₁ B x) ,
  (λ ff gg f → ∀ x → ₂ B (ff x) (gg (₂ a f x)) f)

appᴳ : ∀ {Γ a B} → Tmᴳ Γ (a ⇒ᴳ B) → Tmᴳ Γ (Elᴳ a) → Tmᴳ Γ B
appᴳ {Γ}{a}{B} t u =
  (λ x → ₁ t x (₁ u x)) ,
  (λ {x}{y} f → tr (λ ₁uy → ₂ B (₁ t x (₁ u x)) (₁ t y ₁uy) f) (₂ u f)
                   (₂ t f (₁ u x)))

NatSigᴳ : Conᴳ
NatSigᴳ = NatSigˢ , NatHom

Nᴳ : Subᴳ NatSigᴳ Uᴳ
Nᴳ = Nˢ , (λ {(Nᴹ , _ , _) → Nᴹ})

sᴳ : Tmᴳ NatSigᴳ (Nᴳ ⇒ᴳ Elᴳ Nᴳ)
sᴳ = sˢ , λ {(_ , sᴹ , _) → sᴹ}

zᴳ : Tmᴳ NatSigᴳ (Elᴳ Nᴳ)
zᴳ = zˢ , λ {(_ , _ , zᴹ) → zᴹ}

module AFS where

  N : Set
  N = Tmᴳ NatSigᴳ (Elᴳ Nᴳ)

  s : N → N
  s n = appᴳ {B = Elᴳ Nᴳ} sᴳ n

  z : N
  z = zᴳ

  alg : NatAlg
  alg = N , s , z

  rec : (Γ : NatAlg) → NatHom alg Γ
  rec Γ = (λ n → n .₁ Γ) , (λ _ → refl) , refl

  -- provable as in the AFS paper
  unique : ∀ {Γ}{M : NatHom (N , s , z) Γ} → M ≡ rec Γ
  unique {Γ}{M} = {!!}
