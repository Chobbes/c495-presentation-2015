Introduction
------------

Okay, so I am going to be talking a bit about formal verification. There are a few primary goals of this talk:

- Explain why you should be interested.
- Very briefly cover some of the methods. We're mostly going to focus on theorem proving, and dependent types.
- Make proof assistants more accessible. One of the things that I had problems with was understanding just what this thing was. It's not at all clear how any of the pieces fit together unless you find the right resources.
- Give some rough intuitions about how systems like these work. They're not magic, and in fact if they are magic then that's counterproductive because we can't trust magic.


Preface
-------

Before we begin I'd like to make sure we're all on the same page with respect to a few things.

- Type signatures:

  In this talk I'll be using Haskell-style type signatures, so here's a brief introduction. If "x" is an identifier, then

      x :: A

  Means that "x" has the type A. Note that while Haskell uses two colons, Coq actually uses one. This will be mixed a bit in the talk, but it should be clear from context.

  In languages like these pretty much everything has a type. Even functions. For instance we might say that addition has the type:

      (+) :: Integer -> Integer -> Integer

  This may seem peculiar for some of you, but it literally just means that addition takes these two integers as an argument and produces an integer. The arrows are a common notation in type theory, and there is good reason for it as we shall see.

  Also note that a type may be polymorphic. For instance you can have something like

      id :: a -> a

  What this means is that `id` is a function which takes an argument of some type `a`, which could be `Integer`, `String`, or anything you can possibly imagine, and returns a value of that same type. In this case there is only one function which matches this type signature, and that's the identity function which returns its argument.

      id :: a -> a
      id x = x

- Basic lambda calculus:

  We'll also need to talk a tiny bit about the lambda calculus throughout. More or less you just need to know that lambda calculus consists of lambda terms which can be

  - variables
  - `(\x . t)` where '`t`' is another lambda term (lambda abstraction)
  - `(ts)` (application)

  Aside from that you just need to know one thing: lambda calculus is just substitution. For example the id function could be written in lambda calculus like

      (\x . x)

  No matter what this is applied to we get the same thing back.

      (\x . x)t
      t  -- Substituting the x for the t.


What it is
----------

Alright! So, what is formal verification? Tautologically speaking formal verification is the use of formal methods to verify properties of programs, that is "proving programs correct".

Formal verification is inherently appealing. You want things to be correct, and work as intended. Bugs might not matter too much depending on the application, after all it's not the end of the world if your whoopy-cushion app crashes every so often, but maybe it is if an ICBM has an unexpected integer overflow. In many cases bugs can result in serious harm, death, and large expenses. In this day and age pretty much every device has some form of computer in it. Now if you have ever written a program, or even used any software this should be a terrifying fact. Really you should be afraid to use elevators because it might run Java and somebody doesn't like to check their damn null references. So formal verification is important for these situations. We can't afford for some programs to fail.

A related goal is actually that mathematicians want computers to formally verify proofs as well, particularly since any given theory or paper now consists of pages upon pages worth of proofs which are extremely difficult to check by hand. It'd be nice to have a computer check our logic.

Formal verification can be pursued in a number of ways, such as:

- Manual labour (Kidnap mathematicians and make them do your dirty work -- expensive, and error prone)
- Model checking (essentially boils down to checking every possible state of your program and whether or not it adheres to a given property -- proof by exhaustion)
- Type checking (in its roughest sense types are supposed to provide guarantees about how values in a program behave). This can be really good (Haskell), or done incredibly poorly, like with Java and Python. For instance in Haskell you know that a function which takes an int and returns an int probably isn't going to explode or do anything unexpected, however in Java you can get unexpected null references, and in Python you can get pretty much anything. Unpleasantness all around.
- Theorem proving (Math proofs on your program for great justice. can actually be viewed as extended type checking, as we shall see)

Formal verification can be done at many, and even multiple levels of abstraction:

- High level: Assuming the low level stuff, does this program do what we want? Are the algorithms correct?
- Low level: The aerospace industry actually meticulously checks over the machine code spit out by their compilers. It's what's run, so they need to make sure it's squeeky clean. Otherwise we risk planes falling out of the sky.
- Hardware: Even the design of hardware itself undergoes verification sometimes. For instance Intel is pretty big on this ever since their floating point division bug in one of their processors cost them millions.
- And of course you can mix and match all of these levels.

We're going to focus on higher levels of abstraction for the most part. Proving that your algorithms are correct, and assuming that the underlying systems are working fine. Experience tells us they're probably not, but hey! It's better than nothing. Coq does satisfy the de Bruijn criterion, however. All of the parts involved in verifying the correctness of proofs are small and simple -- we'll see this shortly, but first we're going to go over a few examples.

Coq
---

We're going to look at some examples of a proof assistant in action. The one we'll be using is one of the staples called Coq. So named because of:

- Tradition of naming programming languages after animals (OCaml). Xavier Leroy created OCaml and Coq
- French. Xavier Leroy is from France. Words are different there, I am told
- CoC: Calculus of Constructions. The theory upon which Coq is based
- Thierry Coquand. Creator of the Calculus of Constructions
- The universe is conspiring against us here!

Examples
--------

We're now going to go over some quick examples because if you just look at the code you're going to be very confused at first.

If you're familiar with functional programming in the ML dialects some of this should be fairly familiar to you. This is not terribly different than how you would write a program in Haskell or Ocaml. It's a similar functional style. That said you should be aware that Coq is not Turing complete (as we will discuss later), and as a result you will not be able to express certain programs within it. All Coq programs must terminate. By default all recursion must be structural (think recursing on smaller and smaller subsets of a data structure), however as long as you can show that a recursion is well-founded then you should be able to implement it in Coq, but you will have to prove it.

Beyond the typical functional programming, Coq supports a tactics style of proof. This is what looks weird and confusing until you actually walk through an example. What it boils down to is writing down the steps for a math proof. However, in math proofs you often rewrite things explicitly, constantly reminding the reader of the current state of the proof. The proofs in Coq consist of brief tactics which don't include the proof state, and it's pretty much impossible to read at first -- you really need to step through the proofs in Coq because it will show you the proof state.

We'll be using ProofGeneral, which is an emacs mode for interacting with proof assistance. It has three main buffers. The file you're working with, the current goals and the proof state, and any other responses from the proof assistant.

First let's prove that addition of natural numbers is associative.


    Theorem plus_associative : forall (a b c : nat),
                                 a + (b + c) = (a + b) + c.
    Proof.
      intros a b c. (* Introduce a b and c. *)
      induction a.  (* Perform induction on a. This gives us two goals. One for the base case, and one for the induction hypothesis. *)
      
      simpl.        (* This is the base case. We should be able to simplify this expression some *)
      reflexivity.  (* This got rid of the 0 term, so we can finish the goal with reflexivity. *)
    
      (* Now we're in the second case. Need to show that given the induction hypothesis it's true for the successor to a *)
      simpl.        (* Again we can try to simplify. This does some basic evaluation, and tells us that S a + n is the same as S (a + n) *)
      rewrite IHa.  (* Notice that these aren't quite the same yet. The associativity is different. We can use the induction hypothesis to rewrite one side *)
      reflexivity.  (* And again, reflexivity finishes the goal *)
    Qed.

Being presented with just this code is like a fire-hose. It's much easier to stomach when you can look at the proof state in the proof assistant!

Continuing On...
----------------

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

Looking at this it makes intuitive sense that this would form a proof of the proposition. Both of the arguments to the function are propositions, and by returning the first proposition, `a`, we show that `b -> a`, since regardless of whether `b` is true or false we can produce `a` when given `a`. Explaining it is confusing, but it actually makes a lot of sense. If you're given `a` and `b`, then of course you can prove the proposition `a` from that information.

And of course you can write this as a simple lambda term

    (\x : a, y : b. x)

As we know the lambda calculi are very simple, essentially consisting of one axiom (beta reduction), which just acts like replacement. The typed lambda calculi add a bit more pizzazz, but they're pretty much the same. This is how Coq can allow for complicated proof tactics, while still satisfying the de Bruijn criterion. The tactics are merely a means of manipulating lambda terms in an automated and useful fashion. It doesn't matter what the tactics do, even if they're technically "incorrect", because pretty much all Coq does is type checks the generated lambda term. If this term is correct, then your theorem is proven, and otherwise it is not. How this term was generated is completely irrelevant.

How might you use this / wrapping up
------------------------------------

Now after some learning you can learn this and start proving things about your programs. Coq provides a means for extracting the code into other programming languages, so you can write some pure functions in Coq, and prove properties on them, and then extract them into Haskell, or Ocaml code for use with anything else. It's a bit complicated to pick up, but it can definitely help with mathematical proofs and more as well. While it may be a large burden to fully verify every portion of your program, Coq provides vital tools for proof automation which can significantly narrow down this effort (I did not show this, but Coq provides Ltac which allows you to write your own tactics. You can have very powerful tactics which do a lot of the heavy lifting for you). Further more you can just use it on small portions of your code. You don't have to verify everything, and it can still be useful to have a core piece of your software verified. Beyond that it's useful to just have your code in such a system that can help you reason about it.
