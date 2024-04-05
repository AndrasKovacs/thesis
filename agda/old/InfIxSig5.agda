
{-# OPTIONS --without-K #-}

module InfIxSig5 where

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

module M (Ix : Set)(U : Set)(El : U → Set) where

  data Ty : Set where
    sort : Ix → Ty
    ext  : (A : U) → (El A → Ty) → Ty
    hind : (A : U) → (El A → Ix) → Ty → Ty
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
    appᵉ : ∀ {A B}   → Tm Γ (ext A B) → (a : El A) → Tm Γ (B a)

  Data : Con → Ix → Set
  Data Γ i = Tm Γ (sort i)

  Motive : Con → Set₁
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

module Vec (A : Set) where

  data U : Set where ℕ' A' : U

  El : U → Set
  El ℕ' = ℕ
  El A' = A

  open M ℕ U El

  VecSig : Con
  VecSig = ∙ ▶ (ext ℕ' λ n → ext A' λ _ → ind n (sort (suc n)))
             ▶ sort 0

  Vec : ℕ → Set
  Vec = Data VecSig

  nil : Vec 0
  nil = var vz

  cons : ∀ {n} → A → Vec n → Vec (suc n)
  cons {n} a as = app (appᵉ (appᵉ (var (vs vz)) n) a) as

  VecElim : ∀ (P : ∀ n → Vec n → Set) → P _ nil → (∀ n a as → P n as → P _ (cons a as))
            → ∀ {n} as → P n as
  VecElim P n c = Elim P λ _ → λ {vz → n; (vs vz) → c}

  nilβ : ∀ {P : ∀ n → Vec n → Set}{n}{c} → VecElim P n c nil ≡ n
  nilβ = refl

  consβ : ∀ {P : ∀ n → Vec n → Set}{n m c a as}
          → VecElim P n c (cons {m} a as) ≡ c m a as (VecElim P n c as)
  consβ = refl

-- W
--------------------------------------------------------------------------------

module W (A : Set)(B : A → Set) where

  data U : Set where
    A' : U
    B' : A → U

  El : U → Set
  El A'     = A
  El (B' a) = B a

  open M ⊤ U El

  WSig : Con
  WSig = ∙ ▶ ext A' λ a → hind (B' a) _ (sort _)

  W : Set
  W = Data WSig tt

  sup : ∀ a → (B a → W) → W
  sup s f = appʰ (appᵉ (var vz) s) f

  WElim : ∀ (P : W → Set) → (∀ a (f : B a → W) → (∀ b → P (f b)) → P (sup a f)) → ∀ w → P w
  WElim P psup = Elim (λ _ → P) λ _ → λ {vz → psup}

  supβ : ∀ (P : W → Set) psup a f → WElim P psup (sup a f) ≡ psup a f (λ b → WElim P psup (f b))
  supβ P psup a f = refl
