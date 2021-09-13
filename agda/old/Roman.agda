
{-# OPTIONS --type-in-type #-}

open import Function
open import Relation.Binary.PropositionalEquality
open import Data.Product

infixr 6 _⊛_

-- I'll be using the form of descriptions introduced in the previous post:
-- http://effectfully.blogspot.com/2016/04/descriptions.html

data Desc I : Set where
  var : I -> Desc I
  π   : ∀ A -> (A -> Desc I) -> Desc I
  _⊛_ : Desc I -> Desc I -> Desc I

-- algebra interpretation of Desc as a (Tm Γ U)
⟦_⟧ : ∀ {I} -> Desc I -> (I -> Set) -> Set
⟦ var i ⟧ B = B i                -- sort
⟦ π A D ⟧ B = ∀ x -> ⟦ D x ⟧ B   -- infinitary
⟦ D ⊛ E ⟧ B = ⟦ D ⟧ B × ⟦ E ⟧ B  -- product

-- interpret Desc as indexed functor
Extend : ∀ {I} -> Desc I -> (I -> Set) -> I -> Set
Extend (var i) B j = i ≡ j                      -- sort
Extend (π A D) B i = ∃ λ x -> Extend (D x) B i  -- external function
Extend (D ⊛ E) B i = ⟦ D ⟧ B × Extend E B i     -- inductive function

data μ {I} (D : Desc I) j : Set where
  node : Extend D (μ D) j -> μ D j


ElimBy : ∀ {I B}
       -> ((D : Desc I) -> ⟦ D ⟧ B -> Set)     --
       -> (D : Desc I)
       -> (∀ {j} -> Extend D B j -> B j)
       -> Set
ElimBy C (var i) k = C (var i) (k refl)
ElimBy C (π A D) k = ∀ x -> ElimBy C (D x) (k ∘ _,_ x)
ElimBy C (D ⊛ E) k = ∀ {x} -> C D x -> ElimBy C E (k ∘ _,_ x)

Hyp : ∀ {I B} -> (∀ {i} -> B i -> Set) -> (D : Desc I) -> ⟦ D ⟧ B -> Set
Hyp C (var i)  y      = C y
Hyp C (π A D)  f      = ∀ x -> Hyp C (D x) (f x)
Hyp C (D ⊛ E) (x , y) = Hyp C D x × Hyp C E y

Elim : ∀ {I B}
     -> (∀ {i} -> B i -> Set)
     -> (D : Desc I)
     -> (∀ {j} -> Extend D B j -> B j)
     -> Set
Elim = ElimBy ∘ Hyp


module _ {I} {D₀ : Desc I} (P : ∀ {j} -> μ D₀ j -> Set) (h : Elim P D₀ node) where
  mutual
    elimExtend : ∀ {j}
               -> (D : Desc I) {k : ∀ {j} -> Extend D (μ D₀) j -> μ D₀ j}
               -> Elim P D k
               -> (e : Extend D (μ D₀) j)
               -> P (k e)
    elimExtend (var i) z  refl   = z
    elimExtend (π A D) h (x , e) = elimExtend (D x) (h  x)        e
    elimExtend (D ⊛ E) h (d , e) = elimExtend  E    (h (hyp D d)) e

    hyp : ∀ D -> (d : ⟦ D ⟧ (μ D₀)) -> Hyp P D d
    hyp (var i)  d      = elim d
    hyp (π A D)  f      = λ x -> hyp (D x) (f x)
    hyp (D ⊛ E) (x , y) = hyp D x , hyp E y

    elim : ∀ {j} -> (d : μ D₀ j) -> P d
    elim (node e) = elimExtend D₀ h e


--------------------------------------------------------------------------------

open import Data.Bool.Base
open import Data.Nat.Base

_<?>_ : ∀ {α} {A : Bool -> Set α} -> A true -> A false -> ∀ b -> A b
(x <?> y) true  = x
(x <?> y) false = y

_⊕_ : ∀ {I} -> Desc I -> Desc I -> Desc I
D ⊕ E = π Bool (D <?> E)

vec : Set -> Desc ℕ
vec A = var 0
      ⊕ π ℕ λ n -> π A λ _ -> var n ⊛ var (suc n)

Vec : Set -> ℕ -> Set
Vec A = μ (vec A)

pattern []           = node (true  , refl)
pattern _∷_ {n} x xs = node (false , n , x , xs , refl)

elimVec : ∀ {n A}
        -> (P : ∀ {n} -> Vec A n -> Set)
        -> (∀ {n} x {xs : Vec A n} -> P xs -> P (x ∷ xs))
        -> P []
        -> (xs : Vec A n)
        -> P xs
elimVec P f z = elim P (z <?> λ _ -> f)
