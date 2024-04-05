
{-# OPTIONS --without-K --type-in-type #-}

module InfSig where

open import Lib

infixr 3 _⇒_ _⇒ᵉ_
data U : Set where
  ι    : U
  _⇒_  : (A : Set) → (A → U) → U

data Ty : Set where
  El   : U → Ty
  _⇒_  : U → Ty → Ty
  _⇒ᵉ_ : (A : Set) → (A → Ty) → Ty

infixl 2 _▶_
data Con : Set where
  ∙   : Con
  _▶_ : Con → Ty → Con

data Var : Con → Ty → Set where
  vz : ∀ {Γ A} → Var (Γ ▶ A) A
  vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

data Tm (Γ : Con) : Ty → Set where
  var  : ∀ {A}   → Var Γ A → Tm Γ A
  app  : ∀ {a B} → Tm Γ (a ⇒ B) → Tm Γ (El a) → Tm Γ B
  appᵉ : ∀ {A B} → Tm Γ (A ⇒ᵉ B) → (a : A) → Tm Γ (B a)
  appⁱ : ∀ {A b} → Tm Γ (El (A ⇒ b)) → (a : A) → Tm Γ (El (b a))

Data : Con → Set
Data Γ = Tm Γ (El ι)

Motive : Con → Set
Motive Γ = Data Γ → Set

UMethod : ∀ {Γ} a → Motive Γ → Tm Γ (El a) → Set
UMethod ι       P t = P t
UMethod (A ⇒ b) P t = ∀ a → UMethod (b a) P (appⁱ t a)

TyMethod : ∀ {Γ} A → Motive Γ → Tm Γ A → Set
TyMethod (El a)   P t = UMethod a P t
TyMethod (a ⇒ B)  P t = ∀ u → UMethod a P u → TyMethod B P (app t u)
TyMethod (A ⇒ᵉ B) P t = ∀ a → TyMethod (B a) P (appᵉ t a)

Methods : ∀ {Γ} → Motive Γ → Set
Methods {Γ} P = ∀ A (x : Var Γ A) → TyMethod A P (var x)

Elim : ∀ {Γ}(P : Motive Γ) → Methods P → ∀ {A}(t : Tm Γ A) → TyMethod A P t
Elim P ms (var x)    = ms _ x
Elim P ms (app t u)  = Elim P ms t u (Elim P ms u)
Elim P ms (appᵉ t a) = Elim P ms t a
Elim P ms (appⁱ t a) = Elim P ms t a
