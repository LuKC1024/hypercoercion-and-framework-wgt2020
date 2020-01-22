Hello everyone, I am going to talk about hypercoercions and a framework for equivalence of cast calculi. 
I am Kuang-Chen. He is Jeremy (pointing at Jeremy).
I think everyone in this room know him.
Andre is unfortunately not here.



I will start with Hypercoercions, then Equivalence of Cast Calculi, as our title suggested.



Let's look at a possibly familiar program to illustrate the space-efficiency problem in gradual typing. This program is first presented in the paper Space-efficient gradual typing. I rewrote the program in the Grift programming language.

This program implements the even? and odd? predicate in the usual way. Since these two functions are mutually tail-recursive, we expect them consume constant space. This is expectation, however, is violated if we run the program in a naive implementation.

The problem is that even returns a Dyn but odd returns a boolean. So there are some implicite casts going on aroud the tail calls. If we don't compress those casts, the recursive call would be non-tail resurive any more. And as a consequence, even and odd would consume unbounded space.



Let's restate the space-efficiency problem. The problem is that casts might accumulate on continuations and in values, in the form of proxies.



How to solve this problem? Space-efficient cast representations! There are two lines of research. One goes with coercions in normal form, and the other goes with threesomes. Ron invented supercoercions to demystify the relation between coercions and threesomes.



Are these solution satisfactory? We think there are two criteria for a good cast representations. First, it should be easy to understand by human. Second, it should be easy to work with in proof assistants. 



Is this the case for existing solutions? Well, threesomes are difficult to understand! We can find a story about Philip Wadler and threesome in the paper "Blame and Coercions: Together Again for the First Time". Phlip reported in the paper that "while preparing a lecture on threesomes a few years after the paper was published, he required several hours to puzzle out the meaning of his own notation".

So even the inventor of threesomes find it difficult to understand.



The other approach, coercions in normal form, has another problem -- they are difficult to mechanize. The composition of coercions in normal form include just 10 lines in paper. But they correspond to about a hundred line of Agda Code in Jeremy's formalization.

So even a researcher who has published many papers about coercions in normal form find it difficult to mechanize.



Let's turn to our solution, hypercoercions. I don't know if hypercoercions are simple, but you all can measure it. A hypercoercion either is the identity cast from dyn to dyn, or contains three parts: head, middle, and tail.

A head is either a no-op or a projection. Every kind of middles correspond to a type constructor. And a tail is either a no-op, or an injection, or a failure.

The composition of hypercoercions recurses on the sub-parts of middles. It is morally a structural recursion, thus requires no termination in Agda and possibly other proof assistants.



Of course, cast representations shall be proved correct. But what do we mean by a cast repesentation is correct? Space-efficient cast representations are an optimization in langauge implementations. And an optimization in a program should not change its behavior. So it is natural to expect theorems look like these. If the optimized implementation evaluates an expression e to an observable o, the standard Lazy D semantics should evaluate e to the same o. And vice versa. The other theorem is similar but for Lazy UD.



We proved a theorem of the expected form. We define a language implementatation S parameterized over Cast ADT, which is an abstract data typing defining cast representations. And we prove that suppose C is a Lazy D Cast ADT, then S(C) is a correct optimized semantics.

How does S(C) work? And what is Lazy D Cast ADT?



As I mentioned earlier, the space-efficiency problem arose from the facts that casts might accumulate in continuations and values. We set up a configuration such that in S every continuation has exactly one cast frame at the top and every non-constant value has exactly on proxy.



The Cast ADT includes four operator. Because of the one-cast configuration, we need a constructor for identity cast. Of course we have cast composition and translation. Finally, there should be an operator for cast application.



In order for a Cast ADT to be correct w.r.t Lazy D blame strategy, it must be a Lazy D Cast ADT. This subset of Cast ADT has requirements for all three cast constructors. First, identity should behave like identity. Second, sequencing should behave like sequencing. The wired symbol is monad bind. And finally, translated cast should respect the Lazy D blame strategy. That is, it should behave like the cast application function in the standard Lazy D semantics.



Let's wrap it up. We presented hypercoercions, in the flavors of Lazy D and Lazy UD. And we proved that every Lazy D Cast ADT is correct, including the Lazy D hypercoercions.

The next steps would be defining a Lazy UD Cast ADT and prove its correctness.
Also, we want to prove that existing cast representations, such as coercions in normal form and threesomes, are Lazy D or Lazy UD Cast ADT.











