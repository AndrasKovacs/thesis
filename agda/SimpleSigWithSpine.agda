
{-# OPTIONS --without-K --safe #-}

module SimpleSigWithSpine where

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

mutual
  Tm : Con → Ty → Set
  Tm Γ B = ∃ λ A → Var Γ A × Sp Γ A B

  data Sp (Γ : Con) : Ty → Ty → Set where
    ε   : ∀ {A} → Sp Γ A A
    _,_ : ∀ {B C} → Tm Γ ι → Sp Γ B C → Sp Γ (ι⇒ B) C

module NatExample where

  Nat : Set
  Nat = Tm (∙ ▶ ι⇒ ι ▶ ι) ι

  pattern zero  = (_ , vz , ε)
  pattern suc n = (_ , vs vz , (n , ε))

  NatElim : (P : Nat → Set) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
  NatElim P pz ps zero    = pz
  NatElim P pz ps (suc n) = ps n (NatElim P pz ps n)
