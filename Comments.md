WGT 2020 Paper #9 Reviews and Comments
===========================================================================
Paper #9 Hypercoercions and a Framework for Equivalence of Cast Calculi


Review #9A
===========================================================================

Overall merit
-------------
A. Accept

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper investigates a new representation (called hypercoercions) for
space-efficient coercions and develops a generic proof scheme for showing
correctness of space-efficient semantics with respect to the original.

Comments for author
-------------------
Hypercoercions can be viewed as space-efficient coercions (Siek, Thiemann, and Wadler 2015), defined via a different BNF (modulo minor differences), but have a merit that the meta-operation to collapse two coercions can be defined by structural recursion.  I like the idea pretty much because, as the authors point out, the new definition is easier to formalize on top of proof assistants.  On the other hand, frankly speaking, I'm not sure only such reformulation deserves a new name of hypercoercions because conceptually it's the same.  (In particular, I don't see what is "hyper" about them...)

The proposed generic proof scheme is intriguing.  As far as I understand, the bisimulation proof is similar to Siek-Thiemann-Wadler 2015 but the definition of bisimulation seems subtly different.  It might be interesting to give a detailed comparison.

Space-efficient coercions are a hot topic and a theoretical framework to compare different kinds of coercions is important.  I'd like to see this work at the workshop.

minor comments:


☐ l.229-230:  It appears that T comes from nowhere.  Maybe case expressions should be annotated with their types?  v2' and v3' should be v_2' and v_3'.

☐ l.234:  A closing parenthesis is missing after "observe(v".

☐ At some point, it should be noted that polarity of blame labels is not treated.

☐ In Figure 9, metavariable p should be h?

☐ l.489: "we introduction [introduce]"

☐ l.890: "... are equivalence [equivalent]"

☐ l.984: "Lemma 4.8" -> "Corollary 4.8"



Review #9B
===========================================================================

Overall merit
-------------
A. Accept

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper presents a new representation for casts, called hypercoercions. The claimed advantage of this representation is that it is both amenable to mechanized metatheory thanks to a structurally recursive composition and to efficient implementation.
In addition to proposing hypercoercions, the paper presents an Agda framework to reason about cast representations, in particular focusing on so-called "Lazy D" semantics.

Comments for author
-------------------
This is very interesting work towards an adequate low-level representation of casts that is both compact and convenient to reason about. The paper is clearly written, and the technique presented here should be of interest to the workshop audience.

I'm curious about the name. The paper alludes to Garcia's supercoercions as an inspiration, but I don't know why supercoercions are called this way, so even less sure why hypercoercions are thus called.

The paper claims (page 2) that hypercoercions have a "more compact representation": it would be good to be explicit, more compact than what?

Having dyn as an observation deserves discussion. I imagine that any two values of dynamic type are seen as such an observation. Other work where "observations" are used (eg. gradual security) relate the values underneath.

The discussion of hypercoercions should relate more explicitly/extensively to the other representations of casts/coercions, in order to highlight the key differences. (in particular wrt λS)

Section 3.3 mentions that the bit-level representation of hypercoercions is compact "for the most common-case coercions". I wonder on what (empirical?) evidence this "common-case" argument is justified. It would be good to explain.

☐ the intro should (briefly) recall what D and UD are

☐ page 3: P1 \approx P2 : should this be \smile instead?

☐ line 229-230: where does T come from?

☐ line 234: unfinished line

☐ figure 5: non-failure cases should be of the form `succ v`

☐ definition 4.3: use a proper symbol for bind, as `>>=` is not nicely displayed

☐ line 580-583: what is H?

☐ line 646: should be "Definition 4.1" not 4.4

☐ line 890: "are equivalence"



Review #9C
===========================================================================

Overall merit
-------------
A. Accept

Reviewer expertise
------------------
Y. Knowledgeable

Paper summary
-------------
This paper presents hypercoercions as a representation of casts in a
cast calculus (intended to serve as an intermediate language for a
gradual typing calculus, giving it a dynamic semantics). Existing
approaches (threesomes, supercoercions, coercions in normal form) use
a compose operator (a sequence of casts to a shorter sequence) which
is suitable for studying the metatheory but rather complex
(threesomes, supercoercions), or not so convenient for metatheory but
easier to understand (normal form). Hypercoercions are basically an
encoding of the normal forms, and they are directly related to a
memory-efficient implementation (in particular, for base-type
coercions). The paper presents existing cast calculi, a CEK machine
semantics, then proceeds to hypercoercions and the associated variant
of their composition and a variant of the CEK machine `S(C)`. Finally,
the paper presents a bisimulation between the prior work `{\cal D}`
and the machine `S(C)` presented here, and state the lemmas and
theorems leading up to a correctness result (`S(C)` is correct
wrt. `{\cal D}`), along with brief proofs, and references to machine
checked proofs in Agda for some results.

Comments for author
-------------------
The main contribution in this paper is the new representation of the
cast operation (the hypercoercions), that allow for a simpler
presentation of the core ideas behind the coercions in normal form
(which is earlier work by an overlapping set of authors), as well as
indicating a memory-efficient implementation where coercions can be
stored in registers in all the base-type related cases (with up to a
24 bit space of blame labels).

The paper is technically convincing, only a number of typos came up
(as mentioned in the detailed comments below).

One criticism could be that this paper presents a rather thin idea: A
new encoding of an existing concept.

However, given that it seems to give rise to a memory-efficient
implementation strategy that might not otherwise have been evident,
this paper does contribute increments to the prior art, and for WGT it
should not be a problem that the maturity of the work can be improved.

Detailed comments:

☐ page 2, 'interested in UD because it plays a prominent role in
.. literature': Is there no reason for your interest that is based on
UD's actual properties?

☐ p3, typo: 'the same [as] that of'

☐ Fig.1, Terms, typo: Second occurrence of `inl` should be `inr`.

☐ Fig.3, typos: `fst \kappa` should probably be `[fst \square]\kappa`,
and similarly for `snd \kappa`, in the product type cast
rules. Missing end-paren in <v, stop> rule.

☐ Fig.3, semantics: I'm surprised that `case e1 e2 e3` is so eager:
The guard `e1` is evaluated first, but even though we then already
know whether it's `inl v` or `inr v` (anything else would presumably
be a soundness violation), we proceed to fully evaluate both `e2` and
`e3`, and only then do we reduce the case to `v2 v` or `v3 v`.

☐ Fig.3: in the case-cast rule (the only one with 'where .. and'), `T`
is free (undefined). I think `T3`, `T1` and `T4`, `T2` have been
swapped by accident (`v2'` should be concerned with the former, not
the latter). Of course, `v2` would have been statically typed as
`T4 -> T` for some `T`, but the terms here arise during execution so
`T` should have been passed along in the configuration (maybe as an
annotation on `case`?).

☐ p3, typo: $P_1 \approx{} P_2$ is $P_1 \smile{} P_2$ in the figure.

☐ Fig.5, typos: Shouldn't all right hand sides have `succ` if not
`fail`?

☐ Fig.8, 'and $\forall l . t \not= \bot^l$': $t$ should be $t_1$ or
$t_2$ in the first two cases, and $t_1$ in the last two cases.

☐ Line 632-633, typo: I think `b` should be `e`.

☐ Fig.11 typos: `inl` --> `inr` line 701-2, `fst e)`; `cont(v', k)`
should probably be `cont(\kappa, v')`, or all the `cont` rules should
be modified, and `\kappa` in all the `cont` rules should be $k$, and
presumably a cast should be added in front in most cases, such that we
have a `\kappa` again as the third component of the configuration.
`cont([fst ..]..)` and `snd` actually do have a $k$ on the rhs, but
that's a free variable. ;-)

☐ Line 804-805, `= \Gamma`: That doesn't seem to make sense, `\Gamma`
should be an environment that maps variable names to types, and I
can't see any definition of `T1 \approx T2` nor of
`{\cal E}_1 \approx {\cal E}_2`.



Review #9D
===========================================================================

Overall merit
-------------
A. Accept

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper presents hypercoercions, a representation for gradual
typing casts that is well-suited to both formal reasoning and
compact, efficient low-level implementation.  In addition, the paper
presents an ADT-based framework for proving that various cast
representations are equivalent.

Comments for author
-------------------
This paper makes nice contributions to both the theory and
implementation of gradually typed languages.  The analysis of
hypercoercion representations at the bit-level is nice.  The
abstract-machine approach to metatheory offers a different structure
that is worth considering.


☐ Introduction: "was chosen in /the/ Grift compiler ..."

☐ Section 4.1:  The Cast ADT is an interesting approach to metatheory,
but it appears to depend on a quite strict notion of term equality
rather than contextual equivalence.  This may limit the applicability
of the framework.

☐ Section 4.2: "We define /continuations/ below,"

☐ References:
A number of the citations refer to "SIGPLAN Notices" rather than the
primary venue of publication.  It would be better to use citations
that reference the venue.
 
