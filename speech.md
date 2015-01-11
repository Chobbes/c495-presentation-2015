Okay, so I am going to be talking a bit about formal verification, and in particular the Coq programming language / proof assistant. There are a few primary goals of this talk:

- Explain why you should be interested.
- Very briefly cover some of the methods. We're mostly going to focus on theorem proving, and dependent types.
- Make Coq more accessible. One of the things that I had problems with was understanding just what this thing was. It's not at all clear how any of the pieces fit together unless you find the right resources.
- Give some rough intuitions about how systems like these work. They're not magic, and in fact if they are magic then that's counterproductive because we can't trust magic.


Alright! So, what is formal verification? Tautologically speaking formal verification is the use of formal methods to verify properties of programs, that is "proving programs correct".

Formal verification is inherently appealing. You want things to be correct, and work as intended. Bugs might not matter too much depending on the application, after all it's not the end of the world if your whoopy-cushion app crashes every so often, but maybe it is if the ICBM has an unexpected integer overflow. In many cases bugs can result in serious harm, death, and large expenses. In a world where pretty much every object is a small embedded system it's not absurd to be too paranoid to use an elevator because it might run Java and somebody doesn't like to check their damn null references.

This can be done several ways, such as:

- Manual labour
- Model checking (essentially boils down to checking every possible state of your program and whether or not it adheres to a possibility -- proof by exhaustion)
- Type checking (in its roughest sense types are supposed to provide guarantees about how values in a program behave)
- Theorem proving (can actually be viewed as extended type checking, as we shall see)

and at many, and even multiple levels of abstraction:

- High level
- Low level
- Both

We're going to focus on higher levels of abstraction for the most part. Proving that your algorithms are correct, and assuming that the underlying systems are working fine (which experience tells us they're probably not, but hey!)

