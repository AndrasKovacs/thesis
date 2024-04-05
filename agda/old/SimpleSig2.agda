
{-# OPTIONS --without-K #-}

module SimpleSig2 where

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

pattern v0 = vz
pattern v1 = vs vz
pattern v2 = vs (vs vz)
pattern v3 = vs (vs (vs vz))

data Tm (Γ : Con) : Ty → Set where
  var : ∀ {A} → Var Γ A → Tm Γ A
  app : ∀ {A} → Tm Γ (ι⇒ A) → Tm Γ ι → Tm Γ A

Data : Con → Set
Data Γ = Tm Γ ι

Motive : Con → Set₁
Motive Γ = Data Γ → Set

Method : ∀ {Γ} → Motive Γ → ∀ A → Tm Γ A → Set
Method P ι      t = P t
Method P (ι⇒ A) t = ∀ u → P u → Method P A (app t u)

Methods : ∀ {Γ} → Motive Γ → Set
Methods P = ∀ {A}(x : Var _ A) → Method P A (var x)

Elim : ∀ {Γ} P → Methods {Γ} P → ∀ {A} t → Method P A t
Elim P ms (var x)   = ms x
Elim P ms (app t u) = Elim P ms t u (Elim P ms u)

Tyᴬ : Ty → Set → Set
Tyᴬ ι      X = X
Tyᴬ (ι⇒ A) X = X → Tyᴬ A X

Conᴬ : Con → Set → Set
Conᴬ Γ X = ∀ {A} → Var Γ A → Tyᴬ A X

Rec : ∀ {Γ} X → Conᴬ Γ X → ∀ {A} → Tm Γ A → Tyᴬ A X
Rec A alg (var x)   = alg x
Rec A alg (app t u) = Rec A alg t (Rec A alg u)

NatSig = ∙ ▶ ι ▶ ι⇒ ι

Nat = Data NatSig

zero : Nat
zero = var v1

suc : Nat → Nat
suc = app (var v0)

NatElim : (P : Nat → Set) → P zero → (∀ {n} → P n → P (suc n)) → ∀ n → P n
NatElim P pz ps = Elim P (λ {v0 → λ u → ps; v1 → pz})

zeroβ : ∀ {P : Nat → Set}{pz : P zero}{ps : ∀ {n} → P n → P (suc n)} → NatElim P pz ps zero ≡ pz
zeroβ = refl

sucβ : ∀ {P : Nat → Set}{pz : P zero}{ps : ∀ {n} → P n → P (suc n)}{n}
  → NatElim P pz ps (suc n) ≡ ps (NatElim P pz ps n)
sucβ = refl
