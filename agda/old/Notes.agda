{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Product
open import Data.Bool
open import Data.Empty

-- labelled sums +
-- QW types?

data W (A : Set) (B : A → Set) : Set where
  sup  : ∀ a → (B a → W A B) → W A B

W-elim : ∀ {i A B}(P : W A B → Set i) → (∀ a f → (∀ b → P (f b)) → P (sup a f)) → ∀ x → P x
W-elim P psup (sup a f) = psup a f λ b → W-elim P psup (f b)

Nat' : Set
Nat' = W Bool λ b → if b then ⊥ else ⊤

Wf : Nat' → Set
Wf (sup false f) = Wf (f tt)
Wf (sup true  f) = f ≡ ⊥-elim

Nat : Set
Nat = ∃ Wf

zero : Nat
zero = (sup true ⊥-elim) , refl

suc : Nat → Nat
suc n = sup false (λ _ → proj₁ n) , proj₂ n

Nat-elim : ∀ {i}(P : Nat → Set i) → P zero → (∀ n → P n → P (suc n)) → ∀ n → P n
Nat-elim P pz ps (sup false f      , wf  ) = {!ps _ (Nat-elim P pz ps (f tt , wf))!}
Nat-elim P pz ps (sup true .⊥-elim , refl) = pz

-- minimal TT:
-- labelled finite sums + Id + records + W-types?
-- perhaps Id in SProp?
