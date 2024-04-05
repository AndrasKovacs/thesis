
Thank you for the review and comments! I will correct typos and references, and
I will also try to include a concluding chapter in the final version. Below I
address specific questions & comments.

#### 1, 3, 4.

Noted; I don't have further comments here.

#### 2.

I view 2LTT to be a specific HOAS implementation, a relatively simple one where
we only care about naturality over a single category. Modal TTs generalize this
to setups with e.g. multiple base categories and ways to move between them.

As to an "universe of natural constructions", that sounds like we have a
fragment of "non-natural" constructions as well. I imagine it would be a modal
TT but I don't know exactly how it would be set up. On mode could depend on
inner things naturally, and the other one could depend on them arbitrarily, and
probably the modality would forget that the dependence is natural.

#### 5.

Yes.

#### 6.

I don't really know what the more elementary proof is. All the more concrete
proofs of induction-initiality equivalence that I've seen follow the same
blueprint as Theorem 1. Abstractly, all proofs are the same since it's an
equivalence of propositions. The `ind (Id δ (ind (K Δ)))` is just the usual
inductive step of proving uniqueness of morphisms, and then `reflect` is the
necessary `funext` after that, since `Id` contains pointwise equalities.

On Γ being inconsistent, I think "inconsistent" is only appropriate from the
propositions-as-types perspective. In that case, initiality means falsehood, but
I wouldn't attach such logical baggage to initial objects in arbitrary
categories.  For algebraic signatures, if we pick the signature of a single set
(or proposition), then Γ is indeed the empty set and induction is exfalso, but
more generally it isn't.

#### 7.

I could do that. The two styles are equivalent (when level ordering is
decidable). I have found that lub-s are easier to handle, because I get a single
algebraic expression which summarizes the relevant size information, and I can
simplify the expression along lub equations. With level-wise rules +
cumulativity, I have to remember sizes of sub-types in types. It depends on the
use case which one's nicer. In a proof assistant, maybe lub-free is more
convenient, because the system tracks sizes for me in any case. On paper, I
prefer when sizes are easier to mentally track.

#### 8.

Fixing a level beforehand is not enough, because we want to eliminate from term
algebras to algebras at arbitrary levels, and we get the notion of algebras at
different levels by interpreting signatures in ToS models with different
"underlying set size" level parameters. So even with closed signatures only,
section 4.4. includes a number of places with universal quantification over
levels.

#### 9.

From the notion of ToS model we only derive the notion of ToS induction (and a
broader model theory of ToS). We don't derive term algebras. Those rely on the
existence of ToS syntaxes. We need the notion of ToS induction to state what
having a ToS syntax (initial algebra) means.

#### 10.

This is a good question. I haven't checked, but an identity specifically for
elements of U should work, interpreted as isos in the semantics. It would not
support equality reflection, but a transport or J rule in signatures would
probably work.

It looks like it'd work in the term algebra construction too. There, we'd need
to map from (Tm Ω (IdU a b)) to (aᴬ ≃ bᴬ), which would be possible by
back-and-forth IdU transport, and induction hypotheses saying (Tm Ω (El a) ≃ aᴬ)
and (Tm Ω (El b) ≃ bᴬ).

It seems IdU would be in fact more expressive than writing out an unfolded iso
in a signature, because IdU has an elimination rule, and the unfolded iso
doesn't. So IdU is more like an internal witness of iso-fibrancy. Signatures
probably even support an isoToIdU constructor.
