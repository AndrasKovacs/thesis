
{-# OPTIONS --without-K --type-in-type #-}

-- Strict eliminators for the term model of infinitary indexed families

module InfIxSig4 where

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

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

  Elim : ∀ {Γ}(P : Motive Γ) → Methods P → ∀ {A}(t : Tm Γ A) → Method P t
  Elim P ms (var x)    = ms _ x
  Elim P ms (app t u)  = Elim P ms t u (Elim P ms u)
  Elim P ms (appʰ t f) = Elim P ms t f (λ a → Elim P ms (f a))
  Elim P ms (appᵉ t a) = Elim P ms t a

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
VecElim {A} P n c = Elim ℕ P λ _ → λ {vz → n; (vs vz) → c}

nilβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n}{c} → VecElim P n c nil ≡ n
nilβ = refl

consβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n m c a as}
        → VecElim P n c (cons {A}{m} a as) ≡ c m a as (VecElim P n c as)
consβ = refl

-- W
--------------------------------------------------------------------------------

WSig : (S : Set) → (S → Set) → Con ⊤
WSig S P = ∙ ▶ ext S λ s → hind (P s) _ (sort _)

W : (S : Set) → (S → Set) → Set
W S P = Data ⊤ (WSig S P) tt

sup : ∀ {S P} s → (P s → W S P) → W S P
sup s f = appʰ (appᵉ (var vz) s) f

WElim : ∀ {A B}(P : W A B → Set) → (∀ a (f : B a → W A B) → (∀ b → P (f b)) → P (sup a f))
                                 → ∀ w → P w
WElim P psup = Elim ⊤ (λ _ → P) λ _ → λ {vz → psup}

supβ : ∀ A B (P : W A B → Set) psup a f
       → WElim P psup (sup a f) ≡ psup a f (λ b → WElim P psup (f b))
supβ A B P psup a f = refl

-- Id
--------------------------------------------------------------------------------

IdSig : (A : Set) → A → Con A
IdSig A a = ∙ ▶ sort a

Id : ∀ {A} → A → A → Set
Id {A} x y = Data A (IdSig A x) y

Refl : ∀ {A a} → Id {A} a a
Refl = var vz

J : ∀ {A a}(P : ∀ b → Id {A} a b → Set) → P a Refl → ∀ {b} p → P b p
J {A} P pr = Elim A P λ _ → λ {vz → pr}
