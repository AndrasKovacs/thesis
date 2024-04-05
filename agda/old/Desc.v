
Require Import Coq.Unicode.Utf8.

(*
As far as I can tell, there is way more literature in Agda on datatype-generic
programming than in Coq. I think part of the reason is that the Agda literature
makes liberal use of induction-recursion and fancy termination/positivity
checking, to define fixpoints of functors. These features are not available in
Coq.

But much of the fancy feature usage is unnecessary! In this file I define
descriptions for indexed inductive families, the same way as in Section 4 of

  https://www.irif.fr/~dagand/papers/levitation.pdf

and I also define inductive sets of terms, as an alternative definition to
fixpoints. Generic elimination on described types turns out to be quite easy.

The non-fixpoint-based definition here seems to be more convenient in Agda as
well, because it is a lot more transparent to termination checking than the
direct fixpoint definition.
*)

Inductive Desc (I : Type) : Type :=
| ret  : I → Desc I
| sg   : ∀ (A : Type), (A → Desc I) → Desc I
| ind  : I → Desc I → Desc I
| hind : ∀ (A : Type), (A → I) → Desc I → Desc I.

Arguments ret {I}.
Arguments sg {I}.
Arguments ind {I}.
Arguments hind {I}.

Inductive Tm' {I}(i : I) (Γ : Desc I) : Desc I → Type :=
| tret  : Tm' i Γ (ret i)
| tsg   : ∀ {A B} a, Tm' i Γ (B a) → Tm' i Γ (sg A B)
| tind  : ∀ {A j}, Tm' j Γ Γ → Tm' i Γ A → Tm' i Γ (ind j A)
| thind : ∀ {A B j}, (∀ a, Tm' (j a) Γ Γ) → Tm' i Γ B → Tm' i Γ (hind A j B).

Arguments tret  {I}{i}{Γ}.
Arguments tsg   {I}{i}{Γ}{A}{B}.
Arguments tind  {I}{i}{Γ}{A}{j}.
Arguments thind {I}{i}{Γ}{A}{B}{j}.

Definition Tm {I} Γ i := @Tm' I i Γ Γ.
Definition Motive' {I} Γ A := ∀ i, @Tm' I i Γ A → Type.
Definition Motive {I} Γ := @Motive' I Γ Γ.

Fixpoint Methods' {I}{A : Desc I} : ∀ {Γ : Desc I}(P : Motive Γ)(Q : Motive' Γ A), Type :=
  match A with
  | ret i      => λ Γ P Q, Q i tret
  | sg A B     => λ Γ P Q, ∀ a, Methods' P (λ i t, Q i (tsg a t))
  | ind j A    => λ Γ P Q, ∀ t, P j t → Methods' P (λ i u, Q i (tind t u))
  | hind A j b => λ Γ P Q, ∀ f, (∀ a, P (j a) (f a)) → Methods' P (λ i t, Q i (thind f t))
  end.

Definition Methods {I}{Γ}(P : @Motive I Γ) := @Methods' I Γ Γ P P.

Fixpoint Elim' {I}{Γ}{A}{i}(t : @Tm' I i Γ A) :
  ∀ (P : Motive Γ)(Q : Motive' Γ A), Methods P → Methods' P Q → Q i t :=
  match t with
  | tret      => λ P Q f g, g
  | tsg a t   => λ P Q f g, Elim' t P _ f (g a)
  | tind t u  => λ P Q f g, Elim' u P _ f (g t (Elim' t P P f f))
  | thind t u => λ P Q f g, Elim' u P _ f (g t (λ a, Elim' (t a) P P f f))
  end.

Definition Elim {I}{Γ}(P : @Motive I Γ)(f : Methods P){i}(t : Tm Γ i) : P i t :=
  Elim' t P P f f.

(* -------------------------------------------------------------------------------- *)

Inductive Nat' := zero' | suc'.  (* Constructor tags *)

Definition NatDesc : Desc unit :=
  sg Nat' (λ t, match t with zero' => ret tt | suc' => ind tt (ret tt) end).

Definition Nat : Type :=
  Tm NatDesc tt.

Definition Zero : Nat :=
  tsg zero' tret.

Definition Suc (n : Nat) : Nat :=
  tsg suc' (tind n tret).

Definition NatElim (P : Nat → Type)(pz : P Zero)(ps : ∀ n, P n → P (Suc n)) n : P n :=
  @Elim unit NatDesc
        (λ i,   match i with tt => _ end)
        (λ tag, match tag with zero' => pz | suc' => ps end)
        tt n.

Theorem Zeroβ P pz ps : NatElim P pz ps Zero = pz.
  reflexivity. Qed.

Theorem Sucβ P pz ps n : NatElim P pz ps (Suc n) = ps n (NatElim P pz ps n).
  reflexivity. Qed.



(* Examples *)
(* -------------------------------------------------------------------------------- *)

Inductive Vec' := nil' | cons'. (* constructor tags *)

Definition VecDesc (A : Type) : Desc nat :=
  sg Vec' (λ t, match t with
    nil'  => ret 0
  | cons' => sg nat (λ n, sg A (λ _, ind n (ret (S n)))) end).

Definition Vec A :=
  Tm (VecDesc A).

Definition nil {A} : Vec A O :=
  tsg nil' tret.

Definition cons {A}{n} (a : A) (v : Vec A n) : Vec A (S n) :=
  tsg cons' (tsg n (tsg a (tind v tret))).

Definition VecElim {A}
           (P : ∀ n, Vec A n → Type)
           (pn : P _ nil)
           (pc : ∀ n a v, P n v → P (S n) (cons a v))
           {n} v : P n v :=
  Elim P (λ t, match t with nil' => pn | cons' => pc end) v.


(* -------------------------------------------------------------------------------- *)

Definition WDesc (A : Type) (B : A → Type) : Desc unit :=
  sg A (λ a, hind (B a) (λ _, tt) (ret tt)).

Definition W A B := Tm (WDesc A B) tt.

Definition sup {A}{B}(a : A)(f : B a → W A B) : W A B :=
  tsg a (thind f tret).

Definition WElim {A}{B}
           (P : W A B → Type)
           (psup : ∀ s f, (∀ b, P (f b)) → P (sup s f))
           (w : W A B) : P w :=
  @Elim unit (WDesc A B) (λ i, match i with tt => _ end) psup tt w.

Theorem supβ {A}{B} P psup s f : @WElim A B P psup (sup s f) = psup s f (λ b, WElim P psup (f b)).
  reflexivity. Qed.

(* -------------------------------------------------------------------------------- *)

Inductive Desc' := ret' | sg' | ind' | hind'.

Definition DescDesc (I : Type) : Desc unit :=   (* description of descriptions ("levitation") *)
  sg Desc' (λ t, match t with
  | ret'  => sg I (λ _, ret tt)
  | sg'   => sg Type (λ A, hind A (λ _, tt) (ret tt))
  | ind'  => sg I (λ _, ind tt (ret tt))
  | hind' => sg Type (λ A, sg (A → I) (λ _, ind tt (ret tt)))
  end).

Definition LevDesc (I : Type) := Tm (DescDesc I) tt.

Definition LevRet {I} (i : I) : LevDesc I :=
  tsg ret' (tsg i tret).

Definition LevSg {I} A (B : A → LevDesc I) : LevDesc I :=
  tsg sg' (tsg A (thind B tret)).

Definition LevInd {I} (i : I) (A : LevDesc I) : LevDesc I :=
  tsg ind' (tsg i (tind A tret)).

Definition LevHind {I} (A : Type)(i : A → I)(B : LevDesc I) : LevDesc I :=
  tsg hind' (tsg A (tsg i (tind B tret))).

(* ElimLevDesc is left to the reader *)



(* Generic size function for finitary types, counting constructors *)
(* -------------------------------------------------------------------------------- *)

(* It should be possible to automate Finitary with classes or tactics *)
Fixpoint Finitary {I} (A : Desc I) : Prop :=
  match A with
  | ret i      => True
  | sg A B     => ∀ a, Finitary (B a)
  | ind i A    => Finitary A
  | hind A i B => False
  end.

Search False.

Fixpoint gsize' {I}{Γ A : Desc I}{i}(t : Tm' i Γ A) : Finitary Γ → Finitary A → nat :=
  match t with
  | tret      => λ fΓ fA, S O
  | tsg a t   => λ fΓ fA, gsize' t fΓ (fA a)
  | tind t u  => λ fΓ fA, gsize' t fΓ fΓ + gsize' u fΓ fA
  | thind t u => λ fΓ fA, False_rect _ fA
  end.

Definition gsize {I}{Γ : Desc I} (fΓ : Finitary Γ){i}(t : Tm Γ i) : nat :=
  gsize' t fΓ fΓ.
