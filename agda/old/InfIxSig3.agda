
{-# OPTIONS --without-K --type-in-type #-}

-- Strict eliminators for the term model of infinitary indexed families

module InfIxSig3 where

open import Data.Nat
open import Data.Unit
open import Relation.Binary.PropositionalEquality

module _ (Ix : Set) where

  infixr 3 _⇒_
  data U : Set where
    ι    : Ix → U
    _⇒_  : (A : Set) → (A → U) → U

  infixr 3 _⇒ᵉ_
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

  data Tm (Γ : Con) : Ty → Set
  data Ne (Γ : Con) : Ty → Set

  -- η-long normal terms
  data Tm Γ where
    lamⁱ : ∀ {A b} → (∀ a → Tm Γ (El (b a))) → Tm Γ (El (A ⇒ b))
    ne⇒  : ∀ {a B} → Ne Γ (a ⇒ B) → Tm Γ (a ⇒ B)
    ne⇒ᵉ : ∀ {A B} → Ne Γ (A ⇒ᵉ B) → Tm Γ (A ⇒ᵉ B)
    neι  : ∀ {i} → Ne Γ (El (ι i)) → Tm Γ (El (ι i))

  data Ne Γ where
    var  : ∀ {A}   → Var Γ A → Ne Γ A
    app  : ∀ {a B} → Ne Γ (a ⇒ B) → Tm Γ (El a) → Ne Γ B
    appᵉ : ∀ {A B} → Ne Γ (A ⇒ᵉ B) → (a : A) → Ne Γ (B a)
    appⁱ : ∀ {A b} → Ne Γ (El (A ⇒ b)) → (a : A) → Ne Γ (El (b a))

  ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ne {A = El (ι i)}   t = neι t
  ne {A = El (A ⇒ b)} t = lamⁱ λ a → ne (appⁱ t a)
  ne {A = a ⇒ B}      t = ne⇒ t
  ne {A = A ⇒ᵉ B}     t = ne⇒ᵉ t

  tappⁱ : ∀ {Γ A b} → Tm Γ (El (A ⇒ b)) → (a : A) → Tm Γ (El (b a))
  tappⁱ (lamⁱ t) a = t a

  tapp : ∀ {Γ a B} → Tm Γ (a ⇒ B) → Tm Γ (El a) → Tm Γ B
  tapp (ne⇒ t) u = ne (app t u)

  tappᵉ : ∀ {Γ A B} → Tm Γ (A ⇒ᵉ B) → (a : A) → Tm Γ (B a)
  tappᵉ (ne⇒ᵉ t) a = ne (appᵉ t a)

  Data : Con → Ix → Set
  Data Γ i = Tm Γ (El (ι i))

  Motive : Con → Set
  Motive Γ = ∀ i → Data Γ i → Set

  UMethod : ∀ {Γ} a → Motive Γ → Tm Γ (El a) → Set
  UMethod (ι i)   P t = P i t
  UMethod (A ⇒ b) P t = ∀ a → UMethod (b a) P (tappⁱ t a)

  TyMethod : ∀ {Γ} A → Motive Γ → Tm Γ A → Set
  TyMethod (El a)   P t = UMethod a P t
  TyMethod (a ⇒ B)  P t = ∀ u → UMethod a P u → TyMethod B P (tapp t u)
  TyMethod (A ⇒ᵉ B) P t = ∀ a → TyMethod (B a) P (tappᵉ t a)

  Methods : ∀ {Γ} → Motive Γ → Set
  Methods {Γ} P = ∀ A (x : Var Γ A) → TyMethod A P (ne (var x))

  Elim   : ∀ {Γ}(P : Motive Γ) → Methods P → ∀ {A}(t : Tm Γ A) → TyMethod A P t
  ElimNe : ∀ {Γ}(P : Motive Γ) → Methods P → ∀ {A}(t : Ne Γ A) → TyMethod A P (ne t)

  Elim P ms (lamⁱ t) = λ a → Elim P ms (t a)
  Elim P ms (ne⇒  t) = ElimNe P ms t
  Elim P ms (ne⇒ᵉ t) = ElimNe P ms t
  Elim P ms (neι  t) = ElimNe P ms t

  ElimNe P ms (var x)    = ms _ x
  ElimNe P ms (app t u)  = ElimNe P ms t u (Elim P ms u)
  ElimNe P ms (appᵉ t a) = ElimNe P ms t a
  ElimNe P ms (appⁱ t a) = ElimNe P ms t a

-- Vec
--------------------------------------------------------------------------------

VecSig : Set → Con ℕ
VecSig A = ∙ ▶ (ℕ ⇒ᵉ λ n → A ⇒ᵉ λ _ → ι n ⇒ El (ι (suc n)))
             ▶ El (ι 0)

Vec : Set → ℕ → Set
Vec A = Data ℕ (VecSig A)

nil : ∀ {A} → Vec A 0
nil = neι (var vz)

cons : ∀ {A n} → A → Vec A n → Vec A (suc n)
cons {A}{n} a as = neι (app (appᵉ (appᵉ (var (vs vz)) n) a) as)

VecElim : ∀ {A}(P : ∀ n → Vec A n → Set) → P _ nil → (∀ n a as → P n as → P _ (cons a as))
          → ∀ {n} as → P n as
VecElim {A} P n c = Elim ℕ P λ _ → λ {vz → n;(vs vz) → c}

nilβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n}{c} → VecElim P n c nil ≡ n
nilβ = refl

consβ : ∀ {A}{P : ∀ n → Vec A n → Set}{n m c a as}
        → VecElim P n c (cons {A}{m} a as) ≡ c m a as (VecElim P n c as)
consβ = refl


-- W
--------------------------------------------------------------------------------

WSig : (S : Set) → (S → Set) → Con ⊤
WSig S P = ∙ ▶ S ⇒ᵉ λ s → (P s ⇒ λ _ → ι _) ⇒ El (ι _)

W : (S : Set) → (S → Set) → Set
W S P = Data ⊤ (WSig S P) tt

sup : ∀ {S P} s → (P s → W S P) → W S P
sup s f = neι (app (appᵉ (var vz) s) (lamⁱ f))

WElim : ∀ {A B}(P : W A B → Set) → (∀ a (f : B a → W A B) → (∀ b → P (f b)) → P (sup a f))
                                 → ∀ w → P w
WElim P psup = Elim ⊤ (λ _ → P) λ _ → λ {vz → λ a → λ { (lamⁱ f) fp → psup a f fp }}

supβ : ∀ A B (P : W A B → Set) psup a f
       → WElim P psup (sup a f) ≡ psup a f (λ b → WElim P psup (f b))
supβ A B P psup a f = refl

--------------------------------------------------------------------------------
