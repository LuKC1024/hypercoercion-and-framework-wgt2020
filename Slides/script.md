Hello everyone, I am going to talk about hypercoercions and a framework for equivalence of cast calculi. 
I am Kuang-Chen. He is Jeremy (pointing at Jeremy).
I think everyone in this room knows him.
Andre is unfortunately not here.



I will start with Hypercoercions, then Equivalence of Cast Calculi, as our title suggested.



Let's look at a possibly familiar program to illustrate the space-efficiency problem in gradual typing. This program is first presented in the paper Space-efficient gradual typing. I rewrote the program in the Grift programming language.

This program implements even and odd predicates in the usual way. Since these two functions are mutually tail-recursive, we expect them to consume constant space. This expectation, however, is violated if we run the program in a naive implementation.

The problem is that even returns a Dyn but odd returns a boolean. So some implicit casts are going on around the tail calls. If we don't compress those casts, the recursive call would not be tail anymore. And as a consequence, even and odd would consume unbounded space.



Let's restate the space-efficiency problem. The problem is that casts might accumulate on continuations and in values, in the form of proxies.



How to solve this problem? Space-efficient cast representations! There are two lines of research. One goes with coercions in normal form, and the other goes with threesomes. Ron invented supercoercions to demystify the relationship between coercion and threesomes.



Are these solutions satisfactory? We think there are two criteria for a good cast representation. First, it should be easy to understand by humans. Second, it should be easy to formalize in proof assistants. 



Is this the case for existing solutions? Well, threesomes are difficult to understand! We can find a story about Philip Wadler and threesome in the paper "Blame and Coercions: Together Again for the First Time". Philip reported in the paper that "while preparing a lecture on threesomes a few years after the paper was published, he required several hours to puzzle out the meaning of his own notation".

So even the inventor of threesomes finds it difficult to understand.



The other approach, coercions in normal form, has another problem -- they are difficult to mechanize. The composition of Coercions in Normal Form includes just 10 lines in the paper. But they correspond to about a hundred lines of Agda Code in Jeremy's formalization.

So even a researcher who has published many papers about coercions in normal form finds it difficult to mechanize.



Let's turn to our solution, hypercoercions. I don't know if hypercoercions are simple, but you all can measure it. A hypercoercion either is the identity cast from Dyn to Dyn or contains three parts: head, middle, and tail.

A head is either a no-op or a projection. Every kind of middles corresponds to a type constructor. And a tail is either a no-op, or an injection, or a failure.

The composition of hypercoercions recurses on the sub-parts of middles. It is morally a structural recursion, thus requires no termination in Agda and possibly other proof assistants.



Of course, cast representations shall be proved correct. But what do we mean by a cast representation is correct? Space-efficient cast representations are optimization in language implementations. And an optimization in a program should not change its behavior. So it is natural to expect theorems looking like these. If the optimized implementation evaluates an expression e to an observable o, the standard Lazy D semantics should evaluate e to the same o. And vice versa. The other theorem is similar but for Lazy UD.



We proved a theorem of the expected form. We define a language implementation S parameterized over Cast ADT, which is an abstract data typing defining cast representations. And we prove that suppose C is a Lazy D Cast ADT, then S(C) is a correct optimized semantics.

How does S(C) work? And what is Lazy D Cast ADT?



The space-efficiency problem arose from the fact that casts might accumulate in continuations and values. We set up a configuration such that in 
the S implementation, every
 continuation has exactly one cast frame at the top and every non-constant value has exactly one proxy.



The Cast ADT includes four operators. Because of the one-cast configuration, we need a constructor for identity cast. Of course, we have cast composition and translation. Finally, there should be an operator for cast application.



For a Cast ADT to be correct w.r.t Lazy D blame strategy, it must be a Lazy D Cast ADT. This subset of Cast ADT has requirements for all three cast constructors. First, identity should behave like identity. Second, sequencing should behave like sequencing. The wired symbol is the monad bind. And finally, translated casts should respect the Lazy D blame strategy. That is, it should behave like the cast application function in the standard Lazy D semantics.



Let's wrap it up. We presented hypercoercions, in the flavors of Lazy D and Lazy UD. And we proved that every Lazy D Cast ADT is correct, including the Lazy D hypercoercions.

The next steps would be defining a Lazy UD Cast ADT and prove its correctness.
Also, we want to prove that existing cast representations, such as Coercions in Normal Form and Threesomes, are Lazy D or Lazy UD Cast ADT.











