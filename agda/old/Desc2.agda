
module Desc2 where

open import Data.Unit
open import Relation.Binary.PropositionalEquality
  renaming (subst to tr; trans to infixr 4 _◾_; sym to infix 6 _⁻¹; cong to ap)
open import Relation.Nullary
open import Data.Product
  renaming (proj₁ to ₁; proj₂ to ₂)
open import Data.Empty

module _ {I : Set} where

  data Desc : Set₁ where
    ret  : I → Desc
    pi   : (A : Set) → (A → Desc) → Desc
    ind  : I → Desc → Desc
    hind : (A : Set) → (A → I) → Desc → Desc

  -- fancy analysis allows Tm' to be in Set, but if we have --without-K it
  -- must be in Set₁
  data Tm' (i : I) (Γ : Desc) : Desc → Set where
    ret  : Tm' i Γ (ret i)
    pi   : ∀ {A B} → ∀ a → Tm' i Γ (B a) → Tm' i Γ (pi A B)
    ind  : ∀ {A j} → Tm' j Γ Γ → Tm' i Γ A → Tm' i Γ (ind j A)
    hind : ∀ {A B j} → (∀ a → Tm' (j a) Γ Γ) → Tm' i Γ B → Tm' i Γ (hind A j B)

  Tm : Desc → I → Set
  Tm Γ i = Tm' i Γ Γ

  Motive' : Desc → Desc → Set₁
  Motive' Γ A = ∀ i → Tm' i Γ A → Set

  Motive : Desc → Set₁
  Motive Γ = Motive' Γ Γ

  DAlg' : ∀ {Γ A} → Motive Γ → Motive' Γ A → Set
  DAlg' {A = ret i}      P Q = Q i ret
  DAlg' {A = pi A B}     P Q = ∀ a → DAlg' P (λ i t → Q i (pi a t))
  DAlg' {A = ind j A}    P Q = ∀ t → P j t → DAlg' P (λ i u → Q i (ind t u))
  DAlg' {A = hind A j B} P Q = ∀ f → (∀ a → P (j a) (f a)) → DAlg' P (λ i t → Q i (hind f t))

  DAlg : ∀ {Γ} → Motive Γ → Set
  DAlg P = DAlg' P P

  Elim' : ∀ {Γ A}(P : Motive Γ)(Q : Motive' Γ A) → DAlg P → DAlg' P Q → ∀ {i} t → Q i t
  Elim' P Q f g ret        = g
  Elim' P Q f g (pi a t)   = Elim' P _ f (g a) t
  Elim' P Q f g (ind t u)  = Elim' P _ f (g t (Elim' P P f f t)) u
  Elim' P Q f g (hind t u) = Elim' P _ f (g t (λ a → Elim' P P f f (t a))) u

  Elim : ∀ {Γ}(P : Motive Γ) → DAlg P → ∀ {i} t → P i t
  Elim P f = Elim' P P f f

--------------------------------------------------------------------------------

data Nat' : Set where zero' suc' : Nat'

NatDesc : Desc {⊤}
NatDesc = pi Nat' (λ {zero' → ret _; suc' → ind _ (ret _)})

Nat : Set
Nat = Tm NatDesc _

Zero : Nat
Zero = pi zero' ret

Suc : Nat → Nat
Suc n = pi suc' (ind n ret)

NatElim : (P : Nat → Set) → P Zero → (∀ n → P n → P (Suc n)) → ∀ n → P n
NatElim P pz ps = Elim (λ _ → P) (λ {zero' → pz; suc' → ps})

Zeroβ : ∀ P pz ps → NatElim P pz ps Zero ≡ pz
Zeroβ P pz ps = refl

Sucβ : ∀ P pz ps n → NatElim P pz ps (Suc n) ≡ ps n (NatElim P pz ps n)
Sucβ P pz ps n = refl

--------------------------------------------------------------------------------

WDesc : (S : Set) → (S → Set) → Desc {⊤}
WDesc S P = pi S λ s → hind (P s) _ (ret _)

W : (S : Set) → (S → Set) → Set
W S P = Tm (WDesc S P) _

sup : ∀ {S P} s → (P s → W S P) → W S P
sup s f = pi s (hind f ret)

WElim : ∀ {A B}(P : W A B → Set) → (∀ a (f : B a → W A B) → (∀ b → P (f b)) → P (sup a f))
                                 → ∀ w → P w
WElim P psup = Elim (λ _ → P) psup

supβ : ∀ A B (P : W A B → Set) psup a f
       → WElim P psup (sup a f) ≡ psup a f (λ b → WElim P psup (f b))
supβ A B P psup a f = refl

-- Decidable equality
--------------------------------------------------------------------------------

Eq : Set → Set
Eq A = (x y : A) → Dec (x ≡ y)

EqDesc : ∀ {I} → Desc {I} → Set
EqDesc (ret i)      = ⊤
EqDesc (pi A B)     = Eq A × (∀ a → EqDesc (B a))
EqDesc (ind i A)    = EqDesc A
EqDesc (hind A i B) = ⊥

Tm≡?' : ∀ {I} → ∀ A → EqDesc {I} A → ∀ B → EqDesc B → ∀ {i}(t u : Tm' i A B) → Dec (t ≡ u)
Tm≡?' A eqA _ eqB ret       ret         = yes refl
Tm≡?' A eqA _ eqB (pi a t)  (pi a' t') with eqB .₁ a a'
... | no  p    = no λ {refl → p refl}
... | yes refl with Tm≡?' A eqA _ (eqB .₂ a) t t'
... | no  p    = no λ {refl → p refl}
... | yes refl = yes refl
Tm≡?' A eqA _ eqB (ind t u) (ind t' u') with Tm≡?' A eqA A eqA t t'
... | no p     = no λ {refl → p refl}
... | yes refl with Tm≡?' A eqA _ eqB u u'
... | no p     = no λ {refl → p refl}
... | yes refl = yes refl

Tm≡? : ∀ {I A}→ EqDesc {I} A → ∀ {i}(t u : Tm A i) → Dec (t ≡ u)
Tm≡? eqA = Tm≡?' _ eqA _ eqA

EqNat' : Eq Nat'
EqNat' zero' zero' = yes refl
EqNat' zero' suc' = no λ ()
EqNat' suc' zero' = no λ ()
EqNat' suc' suc' = yes refl

EqNat : Eq Nat
EqNat = Tm≡? (EqNat' , (λ { zero' → _ ; suc' → _}))
