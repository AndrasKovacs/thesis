{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
  renaming (cong to ap; sym to infixl 6 _⁻¹; subst to tr; trans to infixr 4 _◾_)
import Axiom.Extensionality.Propositional as Axiom
open import Data.Product
 renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Unit

coe : {A B : Set} → A ≡ B → A → B
coe refl x = x

postulate
  ext : ∀ {i j} → Axiom.Extensionality i j

-- nat algebra stuff
Conᴺ : Set
Conᴺ = Σ Set λ N → (N → N) × N

Subᴺ : Conᴺ → Conᴺ → Set
Subᴺ (N₀ , s₀ , z₀) (N₁ , s₁ , z₁) =
  Σ (N₀ → N₁) λ Nᴹ → (∀ x → Nᴹ (s₀ x) ≡ s₁ (Nᴹ x)) × Nᴹ z₀ ≡ z₁

Tyᴺ : Conᴺ → Set
Tyᴺ (N , s , z) =
  Σ (N → Set) λ Nᴰ → (∀ {n} → Nᴰ n → Nᴰ (s n)) × Nᴰ z

Tmᴺ : (Γ : Conᴺ) → Tyᴺ Γ → Set
Tmᴺ (N , s , z) (Nᴰ , sᴰ , zᴰ) =
  Σ (∀ n → Nᴰ n) λ Nˢ → (∀ n → Nˢ (s n) ≡ sᴰ (Nˢ n)) × Nˢ z ≡ zᴰ

idᴺ : ∀ {Γ} → Subᴺ Γ Γ
idᴺ {Γ} = (λ n → n) , (λ _ → refl) , refl


-- Church encoding = term model construction in the set model
--------------------------------------------------------------------------------

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
NatSigˢ = Conᴺ

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

  rec : (Γ : Conᴺ) → Subᴺ (N , s , z) Γ
  rec Γ = (λ n → n Γ) , (λ n → refl) , refl


-- Awodey-Frey-Speight encoding = term model construction in the graph model
--------------------------------------------------------------------------------

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
NatSigᴳ = NatSigˢ , Subᴺ

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

  con : Conᴺ
  con = N , s , z

  rec : (Γ : Conᴺ) → Subᴺ con Γ
  rec Γ = (λ n → n .₁ Γ) , (λ _ → refl) , refl

  -- provable, as in the paper
  unique : ∀ {Γ}{M : Subᴺ (N , s , z) Γ} → M ≡ rec Γ
  unique {Γ}{M} = {!!}


-- Fam model
--------------------------------------------------------------------------------

Conᶠ : Set
Conᶠ = Σ Conˢ λ A → A → Set

Subᶠ : Conᶠ → Conᶠ → Set
Subᶠ (A₀ , F₀) (A₁ , F₁) =
  Σ (A₀ → A₁) λ Aᴹ → ∀ {x} → F₀ x → F₁ (Aᴹ x)

Uᶠ : Conᶠ
Uᶠ = Set , λ A → A → Set

Tyᶠ : Conᶠ → Set
Tyᶠ (A , F) =
  Σ (A → Set) λ Aᴰ → ∀ {x} → Aᴰ x → F x → Set

Tmᶠ : (Γ : Conᶠ) → Tyᶠ Γ → Set
Tmᶠ (A , F) (Aᴰ , Fᴰ) =
  Σ (∀ x → Aᴰ x) λ Aˢ → ∀ {x} xx → Fᴰ (Aˢ x) xx

Elᶠ : ∀ {Γ} → Subᶠ Γ Uᶠ → Tyᶠ Γ
Elᶠ {A , F}(Aᴹ , Fᴹ) = Aᴹ , λ xx f → Fᴹ f xx

_⇒ᶠ_ : ∀ {Γ} → Subᶠ Γ Uᶠ → Tyᶠ Γ → Tyᶠ Γ; infixr 3 _⇒ᶠ_
a ⇒ᶠ B =
  (λ x → ₁ a x → ₁ B x) , λ f γᴰ → ∀ {α} → ₂ a γᴰ α → ₂ B (f α) γᴰ

appᶠ : ∀ {Γ a B} → Tmᶠ Γ (a ⇒ᶠ B) → Tmᶠ Γ (Elᶠ a) → Tmᶠ Γ B
appᶠ {Γ}{a}{B} t u =
  (λ x → ₁ t x (₁ u x)) , λ γᴰ → ₂ t γᴰ (₂ u γᴰ)

NatSigᶠ : Conᶠ
NatSigᶠ = Conᴺ , Tyᴺ

Nᶠ : Subᶠ NatSigᶠ Uᶠ
Nᶠ = Nˢ , λ {(Nᴰ , sᴰ , zᴰ) → Nᴰ}

sᶠ : Tmᶠ NatSigᶠ (Nᶠ ⇒ᶠ Elᶠ Nᶠ)
sᶠ = sˢ , λ {(Nᴰ , sᴰ , zᴰ) → sᴰ}

zᶠ : Tmᶠ NatSigᶠ (Elᶠ Nᶠ)
zᶠ = zˢ , λ {(Nᴰ , sᴰ , zᴰ) → zᴰ}

module Fam where

  N : Set
  N = Tmᶠ NatSigᶠ (Elᶠ Nᶠ)

  s : N → N
  s n = appᶠ {B = Elᶠ Nᶠ} sᶠ n

  z : N
  z = zᶠ

  -- is this provable?
  ind : (A : Tyᴺ (N , s , z)) → Tmᴺ _ A
  ind (Nᴰ , sᴰ , zᴰ) =
    (λ n → coe {!!} (n .₂ (Nᴰ , sᴰ , zᴰ))) , {!!} , {!!}
