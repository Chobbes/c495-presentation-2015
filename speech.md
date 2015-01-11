Okay, so I am going to be talking a bit about formal verification, and in particular the Coq programming language / proof assistant. There are a few primary goals of this talk:

- Explain why you should be interested.
- Very briefly cover some of the methods. We're mostly going to focus on theorem proving, and dependent types.
- Make Coq more accessible. One of the things that I had problems with was understanding just what this thing was. It's not at all clear how any of the pieces fit together unless you find the right resources.
- Give some rough intuitions about how systems like these work. They're not magic, and in fact if they are magic then that's counterproductive because we can't trust magic.


Alright! So, what is formal verification? Tautologically speaking formal verification is the use of formal methods to verify properties of programs, that is "proving programs correct".

Formal verification is inherently appealing. You want things to be correct, and work as intended. Bugs might not matter too much depending on the application, after all it's not the end of the world if your whoopy-cushion app crashes every so often, but maybe it is if the ICBM has an unexpected integer overflow. In many cases bugs can result in serious harm, death, and large expenses. In a world where pretty much every object is a small embedded system it's not absurd to be too paranoid to use an elevator because it might run Java and somebody doesn't like to check their damn null references.

This can be done several ways, such as:

- Manual labour (Kidnap mathematicians and make them do your dirty work -- expensive, and error prone)
- Model checking (essentially boils down to checking every possible state of your program and whether or not it adheres to a possibility -- proof by exhaustion)
- Type checking (in its roughest sense types are supposed to provide guarantees about how values in a program behave)
- Theorem proving (can actually be viewed as extended type checking, as we shall see)

and at many, and even multiple levels of abstraction:

- High level
- Low level
- Both

We're going to focus on higher levels of abstraction for the most part. Proving that your algorithms are correct, and assuming that the underlying systems are working fine. Experience tells us they're probably not, but hey! Coq does satisfy the de Bruijn criterion, however. The parts involved in verifying the correctness of proofs are small and simple -- we'll see this shortly.

So, how does Coq work? It actually relies entirely upon type checking. You might think that's insane, after all what does type checking have to do with proving theorems? As it turns out just about everything due to the Curry-Howard isomorphism.

If you're a functional programmer you have probably heard of this before. "Programs are proofs", but what does this mean, and how is this the case?

It's actually a pretty simple idea. Types are propositions, and any program of that type serves as an "existence" proof of that proposition. We'll see an example of how this works in a second. For the purposes of this presentation we will just cover the original Curry-Howard isomorphism, which relates the simply typed lambda calculus and intuitionistic logic. Coq uses something similar, but it actually uses a different typed lambda calculus under the hood called the calculus of inductive constructions, which gives it a bit more power because it has quantifiers and such built in. The simply typed lambda calculus can give you the right intuition, anyway. In this system

- Any type which is inhabited (has a value) represents a provable proposition.
- We represent implication with "->" in types
- Conjunction is a tuple (a, b)
- Disjunction is an Either type. (Either a b)
- False is represented by an uninhabited type. We call this type Void.
- Negation is a -> Void

Of course we have issues with general recursion, so Coq actually requires that all programs terminate. To see why this is an issue, consider if you had a function which loops forever. The type this function returns could be any type whatsoever, which would mean all types are inhabited, so everything becomes inconsistent and horrible. Once you have False = True your system becomes entirely useless.

Let's look at an example of this. Let's say we want to prove `A -> B -> A`. If you were to provide a function with this type, note that `A` and `B` can be ANY type, what must this function be?

    ??? :: a -> b -> a

Well, you might say this type is inhabited by the function `const`, which always returns the first argument.

    const :: a -> b -> a
    const a b = a

Looking at this it makes intuitive sense that this would form a proof of the proposition. Both of the arguments to the function are propositions, and by returning the first proposition, `a`, we show that `b -> a`, since regardless of whether `b` is true or false we can produce `a` when given `a`. Explaining it is confusing, but it actually makes a lot of intuitive sense. If you're given `a` and `b`, then of course you can prove the proposition `a` from it.
