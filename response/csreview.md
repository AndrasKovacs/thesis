# Review of the doctoral thesis by András Kovács

This thesis is an important contribution to the type-theoretic study of algebraic theories, in the broadest sense.
It proposes a novel framework for describing signatures of such theories, defines their semantics in terms of categories of algebras, and proves several new and important results about the existence of initial objects in these categories, that is, inductive types (in the broadest sense, including quotient and higher inductive-inductive types).

The chosen topic is of extreme importance both for the theory of formal systems based on type theory and the practical implementation of proof assistants built on dependent type theory.
In predicative, constructive formal systems, inductive constructions generally fall into two classes:
* rigid combinators such as W-types and quotient types,
* limited and often ad hoc schemes for or types of codes parametrizing inductive constructions.

The theory of signatures proposes by the thesis provides a much more flexible framework for the specification of inductive types, while at the same time ensuring semantic adequacy via the careful study of the universal property inherent to these types in a category of algebras.
Such adequacy results are currently lacking in popular proof assistants such as Agda.

The research methods are up to date and conform to the standards of leading research in type theory.
Features and limitations of approaches are discussed in detail.
Comparisons to pre-existing notions, even outside the immediate area of type theory, are made and related work is discussed in a satisfactory manner.

The thesis is well-structured are written clearly and in a pedagogical style.
It consists of a series of chapters that progressively introduce more complicated kinds of algebraic theories and settings, starting from single-sorted algebraic theories in the traditional sense (with no use of dependent types in the signatures) and going all the way to higher inductive-inductive types in homotopy type theory.
Each chapter investigates the models and initial objects (inductive types) for signatures of the kind of algebraic theory under consideration.

We proceed with a short summary of each chapter and a discussion of the novel results contained.

## Chapter 2

After the introduction, a pedagogical "toy case" or motivational chapter (Chapter 2) illuminates the approach of the full framework developed in later chapters.
By intentionally restricting to closed, single-sorted, finitary signatures, complex dependency issues are removed from the picture.
Targeting the simplest case, the reader is allowed to focus on the essential new concept of a theory of signatures, the initial object in a category of cwfs (categories with families) with carefully chosen type formers.
This simplified setting still allows the development of toy instances of the technology that will be fully developed in the later chapters such as:
(1) notions of algebras, algebra morphisms, displayed algebras, and sections thereof,
(2) the equivalence between initiality and induction,
(3) the construction of initial algebra from the existence of the syntax of the theory of signatures.
All of these are novel results in this framework.

Of note, the constructions in Chapter 2 are fully formalized in Agda.
I have checked the formalization.

## Chapter 3

This chapter redevelops the concepts of the previous chapter in a systematic manner and more general setting.
A distinction between the metatheory and an object theory relative to which an algebraic theory is to be interpreted is made via the use of two-level type theory (2LTT).
The setting of 2LTT forms the backbone of a large part of the thesis material.

## Chapter 4

This is the first chapter with a fully fledged theory of signature, the so-called finitary quotient inductive-inductive case.
This chapter occupies the largest part of the thesis.
The notions of algebras, algebra morphisms, etc. of (1) are bundled up into a finite limit cwf model of the novel theory of signatures.
The level of abstraction attained in this manner highlights the quality of the research methods.

The development of the novel model of finite limit cwfs consumes a large part of the chapter and took me some time to check.
The same holds for term construction for (3), which only works if the inner theory of 2LTT replicates the features of the outer one.
The author is careful here about the use of universe levels to ensure consistency of the construction.
Elsewhere, the consideration of size and universe levels is elided, which I consider appropriate as there are no size problems to be expected.
Again, the versions of (1), (2), (3) for the theory of signatures of this chapter are novel results.

There is an interesting discussion on the possibility of "bootstrapping" the category of models of the theory of signatures.
For this, the author considers the theory of (closed) signatures to be itself specified by a signature.
(The restriction to closed signatures is lifted in Chapter 5.)

The chapter also contains an important and novel result on the reduction of FQIITs to W-types and quotients.

## Chapter 5

This chapter lifts the finiteness restriction in the theory of signatures considered in the previous chapter.
The price to pay is a more complicated semantics based on so-called weak morphisms of cwfs that do not preserve the empty context and context extension strictly.
The resulting theory of signatures is now powerful enough to cover all practically desired examples of algebraic theories.
In particular, it is powerful enough to bootstrap its own theory of signatures.
The framework is again novel and the author again manages to prove the novel versions of (1), (2), (3) in this setting.

The author gives informal reasons for why the reduction to combinators such as W-types and quotients does not seem possible in this setting.

## Chapter 6

The last chapter examines theories of signatures in a setting where the equality of the inner theory no longer reflects that of the outer one.
Such is the case in models of homotopy type theory (univalent foundations).
The quotient features in the previous setting turns into the possibility for so-called higher constructors in inductive types.
The dichotomy between the two equalities leads to schism in the notion of theory of signatures: the issue is whether morphisms of algebras should preserve structure up to inner (weak) or outer (strict) equality.
The author discusses both kinds of signatures and develops semantics (1) for both of them.
All of these are novel contributions.

## Concluding remarks

The thesis is well-written and generally complies with the spelling and grammatical rules of professional English language.
I could only find a few typos, minor kinds of punctuation issues, and a few notational issues. 
The writing is clear and intelligible.

The two attached publications:
* Signatures and induction principles for higher inductive-inductive types,
* Constructing quotient inductive-inductive types
adequately contain new findings that are included in the dissertation.
The thesis contains further generalizations building on the material of these and other publications of the author.
The additions are clearly marked.

The English summary is well-written and gives a coherent summary of the content of the thesis.

The dissertation can be accepted in its current form.
Below, I note some specific questions and comments for the author.

# Specific comments

The below comments fall into several classes:
* typos and grammar mistakes,
* remarks on notation,
* questions where I do not understand something,
* mathematical remarks relevant to the presentation,
* side-remarks that are connected to the material, but are not intended as writing suggestions.

I leave it to the candidate to decide which comments should be addressed (and how).

* Page 9:
	> Being closed implies being finitary.

	I disagree.
  Is it not possible to have closed, infinitary signatures by taking a metatheoretic branching type (rather than a type in the object theory)?
  For example, semi-lattices with externally countable joins (with suprema over externally indexed lists v₀, v₁, …).
  In a setting with 2LTT, allowing for closed and non-finitary signatures would correspond in the theory of signatures to closure of the universe U under externally-indexed products (external dependent function type).
  It seems this is not covered by the theories of signatures you discuss in later chapters.
  Do you comment on this somewhere?

  Another kind of closed, non-finitary signature (according to your usage of finitary in Chapter 4) would be quotient signatures with branching type given by the equality type of a type that is being defined.
  But I understand you are not considering quotients here and that use of equality can be encoded away anyway.

### 2.2.1

* The inductive definition of algebras would have been nicer if you lifted X : Set outside the induction.
  Of course, this does not extend to the generalizations in later chapters.
	The same comment applies to:
	- the definition of morphisms in Subsection 2.2.2 (lifting X₀ X₁ : Set with X^M : X₀ → X₁),
	- the definition of displayed algebras in Subsection 2.2.3 (lifting X : Set with X^D : X → Set),
  - the definition of sections of displayed algebras in Subsection 2.2.4 (lifting X : Set with X^D : X → Set and X^S : (x : X) → X^D x).

* Running text after Definition 5:
	Initiality already makes sense for graphs, not just for categories.

* [Typo] Page 17: "f function" should be "function f".

### 2.2.4

* After Definition 8, you say that Inductive {NatSig} (X, zero, suc) corresponds exactly to the usual induction principle for natural numbers (including its β-rules).
  However, the usual induction principle has the β-rules as strict equalities.
  Here, they are elements of the intensional identity type.
	You do not (yet) address this disparity.

## 2.3

* [Typo] In the second paragraph, please do not use a comma after: "That signatures do not depend on terms".
  The same remark applies to similar situations, which I will not point it out again.

* Third paragraph:
	Terms and substitutions were not just "useful" in the construction of term algebras, they were required!

* [Typo] Third paragraph on page 17:
	Please remove the comma before "because".
  The same remark applies to similar situations, which I will not point it out again.

### 2.4.1

* The term "F-algebra" is ill-defined unless you have introduced an endofunctor F somewhere.
  So you should not use it as a title.
  I suggest to say "comparison to algebras of endofunctors".

* The terminology in the relation of this section is inaccurate.
  It is not single-sorted inductive types, but their signatures, that can be presented as endofunctors.
  The actual type can be presented as an initial algebra.

* The assumption of κ-cocontinuity is only used in Adámek’s theorem, not for the notions of algebra and algebra morphism.
	I suggest you move it there.

* In the discussion of W-types, the name "positions" (of a shape) refers P s for a shape s, not P.

* [Typo]
  "S shapes", "P positions", "ℂ category" should be "shapes S", "positions P, "category ℂ", respectively.
  The same remark applies to similar situations, which I will not point it out again.

* The "sum-of-products" generics mentioned in the last paragraph sound very much like polynomial functors.
  Those can be thought of as normal forms for strictly positive functors as described in "fixpoints of functors".
  Is there a difference?
  You should discuss this.

## 3.1

* In Notation 3, the symbol ⊗ is a bit unfortunate.
  It suggest a general monoidal structure.
  The names p and q for the projections are interesting.
  They suggest you view this as a simplified case of context extension.
  You could comment on this.

* In Example 6, you say that algebras can be viewed as diagrams which preserve finite products.
  What do you mean by this?
  Diagrams over which category?
  It is not clear to me how this comment relates to the definition you have given.

### 3.2.2

* Regarding Notation 4 and 6: while I am fine with the named notation, it would be nice if you could justify it more formally.
  Some thoughts on this.

  Like in your notation for projections of dependent (binary) products, the variable names in a context could be names for the generic terms available in that context.
	One could introduce the category of weakenings (generated by substitution lifts of p).
  Given an extended context Γ.A, we could introduce var_name for the family q[w] ∈ Ty(Δ, A') natural in a weakening w : Δ → Γ.A such that A' = A[p w].
  By leaving the weakening implicit and coming up with rules for inferring the implicit weakening parameters, we could try to make Agda understand this notation.
  Substitution lifting could be justified by introducing the slice construction on cwfs and generalizing pullback along σ : Δ → Γ to an operation σ^* : Slice(Γ) → Slice(Δ) defined on objects that are weakenings into Γ or when σ is a weakening.

### 3.2.3

#### Negative types

* Regarding the remark on naturality, Notation 7, you could briefly remark that the way of making this precise is to write the specification of the type formers themselves in presheaves over the category of contexts (perhaps you already do this later when you discuss presheaf models).
  Perhaps this fits in the discussion of HOAS below.
  Regarding that discussion, the idea of HOAS and use of presheaf semantics is relatively old (and probably related to so-called logical frameworks).
  Perhaps you can find some standard reference on logical frameworks and their presheaf semantics to cite, in addition to the more recent work you refer to.

* It is not quite clear to me how your convention on naturality of type formers is supposed to be interpreted in Definition 15.
  Clearly, everything is natural in Γ.
  But what about the first context parameter?
  Probably you mean it to really come from the set of contexts as a discrete category rather than a category in the usual way.
  It would be good to clarify the phrase "everything is natural" in Notation 7 by mentioning Γ in some way.

* Definition 15 is a weird type-former for me, but I can accept it (in the weak form) as a necessary evil to bridge the gap between finitely complete categories and cwfs.
  The comment that constant families specify closed record types and the phrase "Δ-many fields" only make sense to me if we already assume that the cwf is contextual so that Δ is a telescope over the empty context.

  I don not understand this:
  > Constant families are convenient when building models, because they let us model non-dependent types as semantic contexts

  When you build a model, you interpret all the type formers.
  How does having to model constant families help with that?
  Why would you want to special-case the interpretation of non-dependent types?

  The strict equality for strict constant families is also interesting.
  It seems you really want to "reflect" contexts into types.

  Maybe you will mention this when you discuss presheaf models.

* Definition 16.
  The use of "shorter" seems to refer to material in the definition that has since been deleted.

* You mention positive and negative type formers, but do not explain what those adjectives mean.
  I only have an informal understanding of these terms.

* After Definition 18, I do not follow the suggested categorical characterization of intensional identity types.
  The initial reflexive relation on A also gives you the extensional identity type.
  Perhaps you mean a weaker notion than initiality (e.g., sections of "dependent reflexive relations")?
  Probably weak initiality is too weak.

* When you say that positive and negative versions of Σ are equivalent, you should perhaps say in which sense (they do not have isomorphic sets of terms).

* I like your discussion of the UIP axiom versus extensional identity types.
  However, if we did not have UIP in the metatheory, then all your coherence equations would have to be amended with higher coherence.

#### Positive types

* In the discussion of η for Nat, you say that conversion checking is undecidable.
  You should provide a reference for that.

* Regarding the comment that canonicity breaks if you add propositional uniqueness for recursion, could you not avoid this using appropriate reductions?
  In your example for Bool, could you not for p : Id(m[b ↦ true], t) and q : Id(m[b ↦ false], t) have r : Id(m, BoolRec B t f b) such that r = p for b = true and r = q for b = false?

* Maybe you can briefly say why (and under what additional type formers) conversion is undecidable for extensional identity types.

#### Universes

* It is probably not a good idea to think of (U, El) as a sub-family of (Ty, Tm) because El is not necessarily injective.

* The discussion of type formers in universes could be more precise.
  It is not really clear to me what an "internal sub-family" is.
  The "type former" of Nat in U is really the specification of a type former in the family (Tm(•, Ty), El) induced by (U, El) with elimination targeting the family (Ty, Tm).

### 3.3.1

* In the discussion of Booleans:
  > In the other direction, we only have constant functions

  I guess you mean: only constant functions are definable.

### 3.3.3

* As far as alternative presentations for 2LTT as used here are concerned, I would personally go for the second of the two alternatives outlined.
  It keeps the inner type formers and outer type formers as separate as possible and allows the specification of the inner fragment without talking about the outer fragment.
  So it is clearer how any given object theory extends to a 2LTT.
  But this is personal preference.

* I like the connection with template coding systems you point out.
  It would be nice if Agda had something like "template Agda", offering a 2LTT-like interface.
  I really want to be able to implement, say, coherence of the smash monoidal product, using a higher categorical argument in the outer layer and then be able to get a pure HoTT-term for coherence at any fixed level.

### 3.4.1

* Side-remark.
  There is a more fundamental model Cat_{disc,fib} of cwf that the presheaf model can be seen as being derived from.
  The contexts are categories and the types are displayed categories with unique backwards transports ("discrete fibrations").
  The presheaf model over ℂ is the fibrant slice of Cat_{disc,fib} over ℂ.

* Side-remark.
  It is possible to define types in the presheaf model so as to obtain Russel universes.
  But I think it is best to avoid strict equality of sets in theories.

* In Definition 35, the stated assumptions of UIP and function extensionality in the ambient metatheory, if to be made explicit, belong to a preliminary section on the metatheory you work in, not here.
  UIP is already used to construct the presheaf cwf.

### 3.4.2

#### Inner type formers

* You say that "by definition" all such type formers transfer from ℂ to (Ty₀, Tm₀), but there is a step missing that you should fill in.
  What you get from the what you write is a section of a certain presheaf X over ℂ.
  However, you have defined type formers for (Ty₀, Tm₀) as structure naturally in a context Γ where Γ now is itself a presheaf over ℂ.
  Or, if you were to apply the HOAS idea also here, it would be a section of a certain presheaf over *Psh(ℂ)*.
  However, the representing object of that presheaf turns out to be X (why?).
  Essentially, there is a Yoneda-step missing.

### 3.4.3

* Martin Hofmann gave the reduced definition of exponentials with representables in the setting of a base category with finite products in one of his publications.
  I cannot find it at the moment, but it would be nice to cite.
  You could also say that this a special case of exponential with a tiny object and relate to that notion in category theory.
  For the general notion, you could mention that Tm₀ over Ty₀ is a "representable morphism" (in the sense of Grothendieck) or "locally representable", which is the property that enables this result, and refer to e.g. Awodey's presentation of cwfs ("natural models") and Paolo's thesis.

### 4.1

* Typo on page 62: "unspeficied"

* If the outer identity type reflects the equality in the metatheory and that metatheory presumably(?) has UIP and function extensionality, then you do not need to specify that for the outer identity type.

* Side-remark.
  The existing type-theoretic terminology for inductive types and their signatures is a bit unfortunate.
  We have a short word for the initial algebra before even talking about the signature and its category of algebras.
  In comparison, for algebraic theories, the terminology is conceptually clearer.
  I do not know what do to about this.
  This is a constant point of confusion for people trying to understand the type-theoretic terminology.

* In Definition 39, I find the name "external function type" confusing.
  There are two namings that make sense to me:
  * It is a type former for products indexed over terms of inner types.
    That is, Ty has products indexed over terms of inner types ("Ty-small external products").
  * It is a dependent function type with domain terms of an inner type.
    That is, Ty has dependent functions with domain an inner type.
    In that reading, the word "dependent" is missing.

* In Definition 39, I do not like "inductive" in "inductive function types".
  By themselves, they are dependent function types with small domain ("U-small products").
  I guess the word "inductive" comes from the intended use case of taking initial objects in a category of algebras because these dependent functions provide the recursive arguments.
  But nothing is forcing us to think only about that use case.
  We might also look at terminal algebras (although they are trivial) or completely different models of the theory of signatures.
  So, to me, the word "inductive" belongs to the stage where you are looking at initial objects, not here.

* The choice of theory of signatures (Definition 39) feels a bit ad hoc to me.
  I guess this is unavoidable.
  For example, you could have also added unit types or Σ-types without essentially changing the specifiable categories of algebras.
  And in implementations, one might want to allow user-defined record types etc.
  You definition is canonical in that you went for a minimal choice.
  I guess you will discuss this variability later.

* Side-remark.
  Regarding Notation 13, maybe this is justification for keeping both versions of application around, the "categorical" one and the usual one.
  Personally, I would reserve app for the usual application app(f, a) ∈ Tm(Γ, B[a]) for f ∈ Tm(Γ, Π(A, B)) and a ∈ Tm(Γ, A).
  I do not know what the call the other one, though (except \overline{...} for transposition of an adjunction).

### 4.2.1

* You write:
  > In contrast, displayed algebras are a derived notion in finitely complete categories, and the induction principles would be only up to isomorphism.

  I guess you mean displayed *objects* in finitely complete categories.
  (The objects are already the algebras, so displayed objects correspond to displayed algebras).
  But I do not see how they are a derived notion.
  They are extra data on top of the finitely complete category, no?
  Like in a cwf.

  Finitely complete categories lack a notion of displayed object.
  Probably you were alluding to the presentation of induction using sections of maps into the "initial" object.
  So you substitute or "define" displayed algebras over X by maps into A.
  Then your comment makes sense (and carries even more weight in the non-UIP setting).

* I do not think you get the induction principle up to isomorphism if you define displayed algebras as maps.
  True displayed algebras over X are only equivalent to maps into X, not isomorphic (unless you have univalence).

* Note that adding a notion of displayed object to finitely complete categories does not immediately give you finitely complete cwfs.
  What you get is, for each object A in ℂ:
  * a type DisplayedObj(A) with a map extension : DisplayedObj(A) → Obj(C ↓ A).
  (Note that there is no action under substitution in A.)

  This notion is probably sufficient to model the induction principle up to isomorphism.
  To get the exact induction principle, we also have to add a type of sections of B : DisplayedObj(A):
  * a type Section(B) with an isomorphism Section(B) ≃ section of extension(B).

  Note that if we add substitutional action in A to the above, this would be isomorphic to finitely complete cwfs (minus a terminal object).

  This seems to be enough for the basic interpretation (am I missing something?).
  To able to have equivalence of initiality and induction, we need to add that extension induces an equivalences between the category of displayed objects over A and C ↓ A.
  This means: for each map into A, a displayed object over it with isomorphic extension.
  So constant families in each slice (also known as "fibrant replacement").

  Perhaps you can comment on how you arrived at finite limit cwfs instead of a more minimal "extension" of finitely complete categories as above.
  In particular, where is the substitution of displayed objects needed?

### 4.2.2

* Thank you for "bundling" things now.
  Personally, I would have preferred the bundled approach from the start.
  The unbundled style is unfortunately encouraged by our current proof assistants.
  (A related pet peeve is always case splitting and splitting on each hole as far as the proof assistant can manage, leading to proofs that are not abstract (β-reduced, ε-expanded, ….)

### 4.2.3

* Why do you include Σ-types, but not unit types?
  Or do you include unit types under Σ-types?

* You should stress that your notion of finite limit cwf is not simplify a cwf with finite limits.

* You say that you do not lose anything by having strict constancy.
  But it makes the statements a bit weaker that assume a flcfw.
  With the weaker notion, some of these get nicer.
  In particular, Theorem 3 could be seen as stating the following.
  If ℂ is a flcwf, then so is every slice of ℂ.

* Note that Theorem 3 says that every slice has constant families.
  Perhaps you could include this construction as the proof.

* With Theorem 3, Theorem 1 is equivalent to its categorical version: in a finitely complete category, an object Γ is initial exactly if the terminal object in the slice over Γ is (weakly) initial.
  If you wanted, you could add the latter condition(s).

* The remark contains *two* examples of univalence.
  One (set-level) to identify the equalities in Set and one (groupoid-level) to turn the equivalence into an equality.
  Perhaps you can more explicitly separate the two.
  (The first instance is needed to have the equivalence between types instead of just categories.)
  Note also that the equality by univalence unfortunately misses the identification of not necessarily invertible morphisms on both sides.
  So it is not a full substitute for the equivalence of categories.

### 4.2.4

* In the remark, instead of "slices in the category of flcwfs", I guess you mean to say "objects in slices of the category of flcwfs".
  I do not think functoriality of substitution is even an issue if one does not use displayed algebras anyway.
  Then it is more natural to just directly use the finite limit category model, which does not require any strictification.

* What do you mean by "direct products" of flcwfs?
  Binary products?

### 4.2.5

* In the discussion of discrete displayed category, a discrete category is characterized by having trivial morphisms.
  The statement that its objects are elements of a set is vacuous.

* In the example of NatSig on page 82, it be helpful to expand on the computation of N ⇒ El N.
  This is the only place in the signature where an "inductive" (still think it is a misnomer) exponential occurs.

### 4.2.6

* The two provided options are only two extremes.
  One could also imagine bundling up certain groups of components.
  Of course, none of this changes the end result.

### 4.2.7

* Are the types in the isomorphisms under Definition 4.6 correct?
  I would expect that the first isomorphism appears in the indices of the second isomorphism.

### 4.3.1

* This regards the discussion of types in the groupoid model in [HS96] as functors Γ → Gpd and the displayed style.
  There is actually an "extended" groupoid model in which the types are displayed (cloven) fibrations, similar to the groupoid model.
  See Shulman's inverse diagram paper for this generalization.
  (Being a cloven fibration just means having lifts of morphisms given a lift of one point.)
  Unfortunately, the only universes in that model are for the cloven split fibrations, i.e. the functors Γ → Gpd.

### 4.3.2

* You say that you get small limits by adding an external dependent function (product) type Π^exp.
  By itself, this just gives you small products.
  Small limits come from the combination of Π^exp and the identity type.
  So does C not need to also have (extensional) identity types?

* (Indexed) small products are a special case of small limits.

* I do not understand the last paragraph, the remark about small limits semantics in a simply typed interpretation.
  Why do you not need a locally cartesian closed ℂ?
  Otherwise, how do you talk about categories internal to ℂ that have small limits?
  This is related to the first comment on this subsubsection. 

### 4.3.3

* In Example 19, you should say that you get an isomorphism of *flcwfs* of models.

* Slightly related to Example 19 is the following point.
  As long as we are considering only property-like structure on categories (such as finite limits) and are only interested in equivalence, not isomorphism, the notions of equivalence of categories and equivalence of categories with structure are equivalent.
  That is a common trick in category theory when building equivalences of structured categories.

### 4.4.1

* [Typo] At the start, you mean countably many universes, i.e. a countable hierarchy, instead of countable universes.

### 4.4.3

* I do not understand the paragraph about cumulativity of algebras.
  The subtyping relation is a judgment, not itself a type. 
  So what do you mean by proving it by internal induction?
  What does propositional resizing have to do with it?

* [Typo] The footnote 4 on page 96 is placed badly.
  Footnotes for a sentence belong after the period.

## 4.6

* I do not understand this paragraph and would like to know more about it:

  > In [AK16, Section 2.2], there is an argument that infinitary quotient inductive
  > types extend the base type theory with constructive choice principles. We conjecture
	> that the magic ingredient would be an infinitary QIT which expresses some
  > kind of generic choice principle. We leave this to future work.

### 4.6.1

* [Typo] "too much shortcuts" should be "too many shortcuts".

### 4.7

* The signature of Id is strange.
  Are the arguments really of type Tm Γ U?

### 4.5.1

* In Definition 55, it is interesting that you do not require naturality of the element of Con_M in M.
  I guess that is how you can get away with not defining morphisms of flcwfs in the bootstrapping.
  With naturality, you could show that bootstrapping signatures correspond to contexts in the theory of signatures, i.e. the initial ToS model.

  Without naturality, you are also forced to to follow the "bundling approach" to define the semantics.
  If you were to unbundle and define algebras, algebra morphisms for the theory of signatures, etc. separately, then naturality would be needed to show that the components "match up", e.g. to define source and target of an algebra morphism.
  Another benefit of the "bundle" that is perhaps worth mentioning.

## 5.1

* You now close U under a bunch of operations whereas is was not closed at all before for finitary quotient-inductive-inductive signatures.
  I guess one can also consider e.g. closure under Ty₀-indexed products separately from closure under identity types.
  Do you justify somewhere why you include exactly the chosen closure operation?
  I guess the name "finitary" makes sense for a finite set of recursive parameters (which then forces U to not essentially not be closed under anything).

* Example 28 does not really seem to describe monads.
  For that, I would expect the category of algebras of this signature to be monads.
  But then:
  - the naturality of return and bind is missing,
  - the laws for return and bind are missing.
  The restriction on the input type of M reminds me of relative monads.

* A question related to Example 28, for the ETT-based semantics.
  Does your term construction justify the free monad on an endofunctor (or pointed endofunctor) on Set_i?
  I have not thought about whether the universe levels match up.

### 5.2.2

* Some bold-face letters around Theorem 7 are easy to mistake with the non-bold versions.
  This is unfortunate because they are completely unrelated.
  But with the amount of notation in the thesis, such problems are probably unavoidable.

* It is clear what naturality in the context is in Theorem 7.
  But since you give an explanation, it could be a bit more precise.
  You reindex both sides by σ (bold) applied to σ (non-bold).

* Why not use the order Σ, Id, K after Id in Theorem 7?
  Personally, I feel Σ and Id belong together and K is its own thing.

* There is standard trick to get rid of some coherence isomorphisms when considering weak cwf morphisms, their composition, etc.
  One can phrase preservation of the empty context and context extension using preservation of universal properties.
  That is, if some context has the universal property of the empty context, then so does its image.
  Similarly for a candidate for context extension (consisting of an extended context, a projection morphism, and a term).
  Then composition of weak cwf morphisms is just given by composition.
  But that still leaves the mess with non-strict preservation of type formers (Σ, Id, K).

* In Chapter 4, it seems the category of flcwfs was itself the category of algebras of a signature.
  This seems to fail with weak morphisms.
  Or can you still recover it?
  Of course, you can describe the weak morphisms themselves by a signature (as you say do in Section 5.3).

* Definition 62 should be called *split* iso-cleaving because you include strict preservation of composition.
  It is not so clear to me why you need the split notion instead of just the cloven notion.
  I do not see where it is needed in the following construction.
  A similar comment holds for Definition 63.
  There, it is more plausible that it is needed.

## 5.5.

* The viewpoint of isofibrancy as a structure identity principle seems a bit far-fetched.
  There is no univalent equality of contexts here.
  Isofibrancy says that the "structured predicate" of types on a context respects isomorphism of context.
  This skips considerations of identity of contexts entirely.

* Thanks for combating the often mispresented constructions of "syntactic models" and "syntactic translations".
  It is not clear to me why some people refuse so hard to see them as (functorial) model constructions (when applicable).

# Other stuff that comes to mind

* When you say QIIT, do you by default mean finitary or infinitary?
  I guess infinitary, but many uses of QII in the thesis are meant to be read local to the respective chapter (which is finitary or infinitary).

* There was the example of an inductively defined operation M on types that has a constructor M (M A) → M A.
  You say this is not covered by your framework.
  Can you imagine an extension that does?

* The design choices for the type formers in the theory of signatures feel a bit ad hoc.
  For example, type formers such as equality types in U seem to allow for more definable substitutions, even if they do not necessarily increase the categories of algebras that can be encoded.

* Contexts in a cwf can be seen as a linearization of (the opposite of) finite direct categories.
  Finite direct categories can be generalized in two orthogonal directions:
  - Allow for an external or internal type of objects at every degree.
    This is covered by types being closed under external and internal dependent function type.
  - Allow for direct categories with transfinite height.
    This would mean infinite contexts, with variables indexed by an ordinal, for example ω.
    This can be reflected into types via ω^op-Reedy limits (record types with components indexed by ω).

  One could imagine extending the theory of signatures in this way.
  The first one is already covered by infinitary signatures, but not the second one.
  For example, this would be needed to define semisimplicial types.
  Can your framework be extended in this direction?

* Categories of algebras of signatures fit a similar role as locally presentable categories in classical category theory.
  This relates to some discussion in Section 4.7 (around Gabriel-Ulmer duality).
  Assuming a classical setting, one should prove:
  - the category of algebras of a signature is a locally presentable category,
  - the functor of categories of algebras induced by a morphism of signatures is an accessible functor (and right adjoint, but you already proved that).

  In the reverse direction, one should examine which every locally presentable category can be realized as the category of algebras of a signature.
  Presumably, in the non-finitary case, one would have to generalize signatures to transfinite signatures as outlined in a comment above.

  I do not expect every accessible right adjoint between categories of algebras of two signatures to lift to a morphism of signatures.
  For that, the language of signatures seems too ad hoc.
  However, it may still be possible to find a class of signature morphisms that should be regarded as invertible (because they induce equivalences of categories of algebras).
  Then one could hope that the bicategorical localization of the category of signatures at those "weak equivalences" is the (2, 1)-category of locally presentable categories.

  In any case, one should start with the finitary case.
  That one can presumably be made constructive (there should be no choice issues).

* It's interesting that you seem to get a reduction to basic type formers or levitation, but not both at the same time.

* It would be interesting to look at a "dual" version of this framework that lets you build signatures to describe categories of "coalgebras".
  Coinductive types would then be terminal objects in those categories.
  I wonder whether there is a dual version of the term construction.
