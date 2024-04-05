
{-# OPTIONS --without-K --type-in-type #-}

module InfIxSig6 where

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (proj₁ to ₁; proj₂ to ₂)

module _ (Ix : Set) where

  data Ty : Set where
    sort : Ix → Ty
    ext  : (A : Set) → (A → Ty) → Ty
    hind : (A : Set) → (A → Ix) → Ty → Ty
    ind  : Ix → Ty → Ty

  infixl 2 _▶_
  data Con : Set where
    ∙   : Con
    _▶_ : Con → Ty → Con

  data Var : Con → Ty → Set where
    vz : ∀ {Γ A} → Var (Γ ▶ A) A
    vs : ∀ {Γ A B} → Var Γ A → Var (Γ ▶ B) A

  data Tm (Γ : Con) : Ty → Set where
    var  : ∀ {A}     → Var Γ A → Tm Γ A
    app  : ∀ {i B}   → Tm Γ (ind i B) → Tm Γ (sort i) → Tm Γ B
    appʰ : ∀ {A i B} → Tm Γ (hind A i B) → (∀ a → Tm Γ (sort (i a))) → Tm Γ B
    appᵉ : ∀ {A B}   → Tm Γ (ext A B) → (a : A) → Tm Γ (B a)

  Data : Con → Ix → Set
  Data Γ i = Tm Γ (sort i)

  Motive : Con → Set
  Motive Γ = ∀ i → Data Γ i → Set

  Method : ∀ {A Γ} → Motive Γ → Tm Γ A → Set
  Method {sort i}     P t = P i t
  Method {ext A B}    P t = ∀ a → Method P (appᵉ t a)
  Method {hind A i B} P t = ∀ f → (∀ a → P (i a) (f a)) → Method P (appʰ t f)
  Method {ind i B}    P t = ∀ u → P i u → Method P (app t u)

  Methods : ∀ {Γ} → Motive Γ → Set
  Methods {Γ} P = ∀ A (x : Var Γ A) → Method P (var x)

  Elim' : ∀ {Γ}(P : Motive Γ) → Methods P → ∀ {A}(t : Tm Γ A) → Method P t
  Elim' P ms (var x)    = ms _ x
  Elim' P ms (app t u)  = Elim' P ms t u (Elim' P ms u)
  Elim' P ms (appʰ t f) = Elim' P ms t f (λ a → Elim' P ms (f a))
  Elim' P ms (appᵉ t a) = Elim' P ms t a


  -- currying Elim'
  ------------------------------------------------------------

  -- variable renaming
  Ren : Con → Con → Set
  Ren Γ Δ = ∀ {A} → Var Γ A → Var Δ A

  Methods→' : ∀ {Γ Δ} → Motive Γ → Ren Δ Γ → Set → Set
  Methods→' {Γ} {∙}     P ren Res = Res
  Methods→' {Γ} {Δ ▶ A} P ren Res = Method P (var (ren vz)) → Methods→' P (λ x → ren (vs x)) Res

  Methods→ : ∀ {Γ} → Motive Γ → Set → Set
  Methods→ P = Methods→' P (λ x → x)

  curryMethods' : ∀ {Γ Δ P Res}(ren : Ren Δ Γ)
                  → ((∀ A (x : Var Δ A) → Method P (var (ren x))) → Res)
                  → Methods→' P ren Res
  curryMethods' {Γ} {∙}    {P} ren f = f (λ _ ())
  curryMethods' {Γ} {Δ ▶ A}{P} ren f =
    λ m → curryMethods' (λ x → ren (vs x)) (λ ms → f (λ { A vz → m ; A (vs x) → ms _ x}))

  Elim : ∀ {Γ}(P : Motive Γ) → Methods→ P (∀ {A}(t : Tm Γ A) → Method P t)
  Elim P = curryMethods' (λ x → x) (Elim' P)


-- Vec
--------------------------------------------------------------------------------

VecSig : Set → Con ℕ
VecSig A = ∙ ▶ (ext ℕ λ n → ext A λ _ → ind n (sort (suc n)))
             ▶ sort 0

Vec : Set → ℕ → Set
Vec A = Data ℕ (VecSig A)

nil : ∀ {A} → Vec A 0
nil = var vz

cons : ∀ {A n} → A → Vec A n → Vec A (suc n)
cons {A}{n} a as = app (appᵉ (appᵉ (var (vs vz)) n) a) as

VecElim : ∀ {A}(P : ∀ n → Vec A n → Set) → P _ nil → (∀ n a as → P n as → P _ (cons a as))
          → ∀ {n} as → P n as
VecElim {A} P n c = Elim ℕ {VecSig A} P n c

nilβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n}{c} → VecElim P n c nil ≡ n
nilβ = refl

consβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n m c a as}
        → VecElim P n c (cons {A}{m} a as) ≡ c m a as (VecElim P n c as)
consβ = refl
