# Monads

Monads are used heavily in Lean, as they are also in Haskell. Monads come from the wonderful world
of Category Theory, see
[https://en.wikipedia.org/wiki/Monad_(category_theory)](https://en.wikipedia.org/wiki/Monad_(category_theory)).

Monads in Lean are so similar to Haskell that this introduction to monads is heavily based on the
similar chapter of the [Monday Morning Haskell](https://mmhaskell.com/monads/). So,
much credit needs to go to the authors of that material.

Monads build on the following more fundamental type classes which you will need to understand
first before fully understanding monads:

![image](../images/monads.png)

This chapter is organized to give you a bottom up introduction to monads, starting with functors and
applicative functors to get an intuition for how these abstract structures work in Lean. Then we’ll
tackle monads and look at some of the most common ones.

## [Part 1: Functors](functors.md)
In [part 1](functors.md), you’ll learn all about functors. A functor is a type class
that provides a `map` function and the map function is something many people are already familiar
with so this should be easy to follow.

## [Part 2: Applicative Functors](applicative.md)
In [part 2](applicative.md), we tackle applicative functors. Applicatives are a little
more difficult to understand than functors, but their functionality can still be summed up in a
couple simple functions.

## [Part 3: Monads Tutorial](monads.md)
In [part 3]((monads.md), we finally approach the topics of monads. Now that you have an intuition
for how abstract structures work, we’ll examine some of the problems that applicative functors and
functors don't help us solve. Then we’ll get into the specifics of how we actually use monads.

## Part 4: Reader Monads
Our introduction to monads examined the built in types that have a monadic structure. It had a focus
on those things that you’ve seen in action, but maybe never thought of monadically. In part 4, we
start exploring some of the common monadic idioms that you’ll need outside of the basics. We’ll
examine the Reader monad, which gives us a global readable state.

## Part 5: State Monad
Part 5 picks up where part 4 left off, and introduces the State monad. This monad allows us to keep
a particular type that we can both read from and write to. It opens the door to fully stateful
programming, allowing us to do many of the things a function programming language supposedely
“can’t” do.

## Part 6: Monad Transformers
By this point, you’ve been exposed to plenty of different monads. But now we need to answer the
question of how we can make them work together. After all, there are definitely times when we need
multiple kinds of monadic behavior. Part 6 introduces the concept of monad transformers, which allow
you to combine multiple monads into one.

## Part 7: Monad Laws
In the seventh and final part of this series, we’ll examine what makes a monad a monad. After all,
can't you just implement these type classes any way you want and write a “monad” instance? Starting back
with functors and applicative functors, you’ll learn that all these structures have “laws” that they
are expected to obey with respect to their behavior. We can make instances that don’t follow these
laws. But we do so at our peril, as other programmers will be very confused by the behavior.