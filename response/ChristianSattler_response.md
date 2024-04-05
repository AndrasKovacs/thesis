
Thanks for the review! I'll fix typos and by default follow wording/definition
suggestions. Below I address specific comments where I can make substantial
response.

> sums-of-products

In the Haskell context it's actually finite sums of finite products, so it's
more restricted than polynomial functors. I'll point this out.

> In Notation 3, the symbol ⊗ is a bit unfortunate.

I tried to differentiate from the metatheoretical ×. Maybe it would be better
to just overload × here.

> How does having to model constant families help with that?

If a model has K, I can choose to define all the closed type formers as contexts
and then K automatically lifts them to arbitrary contexts. This is a technical
convenience for avoiding noise from the unused dependencies in semantic types. I
use this when defining universes in various models, in 4.2.5 and 5.2.2 and also
in the presheaf model in 3.4.

> positive and negative

I remarked "negative" in 3.2.3 to be type formers which can be specified using
isomorphisms, and later described positive types as those which are specified
with induction principles. I invented these specific definitions here, I think
they appropriately describe the informal usage of "positive"/"negative" that
I've seen. I can make this clearer at the start of 3.2.3.

> Regarding the comment that canonicity breaks if you add propositional uniqueness

That's an interesting point that I haven't though about. Your computation rules
seem to generally work, so I guess canonicity is not an issue with propositional
uniqueness.

> The "type former" of Nat in U is really the specification of a type former in
> the family (Tm(•, Ty), El) induced by (U, El) with elimination targeting the
> family (Ty, Tm).

I don't understand this comment. Should it be `(Tm(•, U), El)`?

> there is a step missing that you should fill in.

Looking at this section, I think that I mixed up a) specifying type formers for
a TT in HOAS style b) getting notions of internal algebras from a signature. For
the latter, it makes sense to evaluate signatures at ∙, but for the former, it
doesn't really, I think we just take the presheaf as it is, for a
specification.

But now I don't get the comment on the "missing step" here. For closed type
formers, if I just evaluate the signature in the psh model, I get what I want
quite directly. E.g.

    (∙ ▶ (Nat : Ty₀) ▶ (zero : Tm₀ Nat) ▶ (suc : Tm₀ Nat → Tm₀ Nat))

becomes

    Nat    : ∀ Γ → TyC Γ
    Nat[]  : ...
    zero   : ∀ Γ → TmC Γ Nat
    zero[] : ...
    suc    : ∀ Γ → TmC (Γ ▶ Nat) Nat
    suc[]  : ...

here the only interesting translation I applied is for the (Tm₀ Nat → Tm₀ Nat)
that has representable domain.

With open type formers, there's some extra baggage when I abstract over parameters:

    ListSpec := (A : Ty₀) → ((List : Ty₀) × Tm₀ List × (Tm₀ A → Tm₀ List → Tm₀ List) × ...)

Here `(A : Ty₀) → ` will be a proper presheaf Π type, so I get
a natural `∀ Γ Δ (σ : SubC Δ Γ)(A : TyC Δ) → ...`, but this is equivalent
to a natural `∀ Γ (A : TyC Γ) → ...`. So isn't it enough to just take
the presheaf as the type former specification?

> Signature type former terminology

I agree that "inductive" is too specific. "External" is also tied to the
signature use-case. I'm open to renaming these. I have difficulty though finding
non-awkward-sounding alternatives.
  - "U-small product" : not sure about this one, because "U-small" could also mean
     that the product type is itself in U.
  - "U-domain function" : how should we say this in English? "Function with
    domain in U" is grammatically correct, but too long. "U-domained function"?
  - What about having simply "product type" for Π? This is not ambiguous in the
    context of ToS. But it could be confused with proper Π types in cwfs in
    general.

For external functions, I like "external product" for the one which returns in
Ty, and "small external product" for the "infinitary" one.

> Probably you were alluding to the presentation of induction using sections of
> maps into the "initial" object.

Yes.

> Perhaps you can comment on how you arrived at finite limit cwfs instead of a
> more minimal "extension" of finitely complete categories as above.

Finite limit cwfs are a result of historical accretion, where we first noticed
that A-M-D-S looks like the underlying sets of a cwf, and later I noticed that
adding more type formers enables equivalence of induction and initiality. Then
in the infinitary QIIT paper I extended this to finite limit cwfs, which looked
like a nice point to stop adding components, because of the Clairambault-Dybjer
result showing biequivalence of flcwfs and finitely complete categories. Between
the different publications I wasn't really motivated to change the semantic
setup, because I could just reuse parts that were already checked in the
previous papers. So it is entirely possible that there's a better way to define
the semantics, maybe along the line you describe.

> where is the substitution of displayed objects needed?

It's used in the equivalence of induction and initiality in Theorem 1

> Why do you include Σ-types, but not unit types?

The unit type is derivable as (K ∙); I should mention this.

> But it makes the statements a bit weaker that assume a flcfw.

Right. Theorems 1-3 only need weak K, and otherwise in the chapter I only
produce flcwfs as output, where strict K strengthens my results. I should use
the appropriate assumption in each of these cases.

> I would expect that the first isomorphism appears in the indices of the second isomorphism.

Yes, I should apply the iso to η₀ and η₁ there on one side.

> So does C not need to also have (extensional) identity types?

In that paragraph I meant adding more types on the top of the default flcwf, so
extensional identity is already included.

> I do not understand the last paragraph, the remark about small limits
> semantics in a simply typed interpretation. Why do you not need a locally
> cartesian closed ℂ?

Here I went out of sync with myself. The specific Πᵉˣᵗᵤ can be interpreted using
exponentials in the simply-typed setting, but Πᵉˣᵗ by itself indeed does not
get us small limits. I'll correct this.

> * I do not understand the paragraph about cumulativity of algebras.
> The subtyping relation is a judgment, not itself a type.
> So what do you mean by proving it by internal induction?
> What does propositional resizing have to do with it?

I guess you meant "propositional reasoning" (which is what I wrote in the
text) here.

What you write here is what I meant in the text. Subtyping is a judgment, not a
type, so I can't prove it internally. "Propositional reasoning" is meant the
same way here as in propositional vs. definitional equality.

I can imagine a type theory where a subtyping judgment is internalized in a
type, but it's a rather exotic feature so I did not want to bother with it.

> I do not understand this paragraph and would like to know more about it

I think that this is now partially addressed in this paper (and I should discuss it
in the thesis):

  https://arxiv.org/pdf/2101.02994.pdf

The goal is to have an axiom (or some type former) from which the infinitary
QITs can be constructed. In the above paper it's called "indexed weakly initial
set of covers" (def 4.1). I haven't yet read this carefully though, and I don't
know at the moment if they have a computationally adequate TT syntax in which
QITs are constructible from an axiom, or if they only show QIT reductions in some
constructive semantics.

> The signature of Id is strange.

It should be `Tm Γ (El a) → Tm Γ (El a) → Ty Γ`.

> Do you justify somewhere why you include exactly the chosen closure operation?

In Section 5.4 I need exactly the assumed U type formers.

> Example 28 does not really seem to describe monads.

> A question related to Example 28, for the ETT-based semantics.
> Does your term construction justify the free monad on an endofunctor (or
> pointed endofunctor) on Set_i?

I'll add the missing laws to the signature.

The ETT-based semantics lets us recover algebras as monads, because we can
choose the universe levels to be the same in the input and output of M.

However, the levels don't match up for free monads. The level of the inductive
sets is j+1 if j is the level of external indexing types. What we get is
actually `M : Set i → Set (i + 2)`. I'll note this.

> In Chapter 4, it seems the category of flcwfs was itself the category of
> algebras of a signature.  This seems to fail with weak morphisms.

It doesn't fail. For each signature, the flcwf of algebras is almost exactly the
same in Chapter 5 as in Chapter 4, except for that K is weak in Chapter 5.  In
other words, the interpretation of signatures is mostly unchanged, we change
only the interpretation of ToS types, substitutions and terms.

> It is not so clear to me why you need the split notion instead of just the
> cloven notion.

It's needed to show functoriality of type substitution. E.g. on page 132,
the terminal object in A[σ] is defined using coercing A.∙ along σ. So in
`A[σ][δ] = A[σ ∘ δ]` we have to show that coercing ∙ twice is the same as
coercing it once over the composite isomorphism.

------------------------------------------------------------

> When you say QIIT, do you by default mean finitary or infinitary?

It's local to the given chapter.

> There was the example of an inductively defined operation M on types that has a
> constructor M (M A) → M A.  You say this is not covered by your framework.
> Can you imagine an extension that does?

I haven't thought about this. It should be an instance of "nested induction",
similarly to e.g.

    data List a = Nil | Cons a (List (List a))

I have seen semantics for these using fixpoints of functors in functor categories.
We would need at least a notion of polarity for type parameters to single out the
strictly positive signatures.

There's a less exotic kind of nested induction that I mentioned in section
4.1. (e.g. List-branching trees). Those also require some notion of formal
parameter with polarity, but the semantics would be similar to what we already
have.

> The design choices for the type formers in the theory of signatures feel a bit
> ad hoc.

I agree. The type formers are partially based on what I needed for all the
different constructions in the chapters, e.g. for term algebras and the
"signature-based semantics" in chapter 5.

> It's interesting that you seem to get a reduction to basic type formers or
> levitation, but not both at the same time.

For closed finitary signatures we get both at the same time, see 4.6.3.
