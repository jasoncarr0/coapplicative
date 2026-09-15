# Coapplicative Functors

This library provides a dual of Applicative functors:
covariant functors which can split over Either instances.

Some Comonads have well-behaved CoApplicative instances
that agree with context extension.
Notably this includes NonEmpty lists.

A newtype wrapper for one instance is provided for
any CoApplicative, but this usually
does not commute with duplication, and so different places
in the context may see different values.

# Compatibility with a Comonad

Comonads which agree with their CoApplicative instance
have "good" pattern-matching in which we may examine
the context inside the body of branching code.
This means that any two contexts which are in the
same branch will always see compatible views.

For instance, using NonEmpty, we can define a prev operator on any variable.
Let's suppose we want to take a list of `Maybe Int`s, and sum up each
pair of Just values comonadically.
If we try normally, we'll get stuck:
```haskell
\x -> case extract x of
         Just x' -> x' + ??? {- Can't use prev, search for it? -}
         Nothing -> 0
```
Then we have no way to extend the variable x'.
Instead we can wrap our pattern match to maintain
the context. Now we have access to all previous
values of x'.
```
\x -> case splitMaybe x of
         Just x' -> extract x' + fromMaybe 0 (prev x')
         Nothing -> 0
```
Since this list is finite, we're guaranteed to either
find a previous value of x', or reach the end of
the list.


Another (less useful) instance is given by Traced
when the monoid is actually a cyclic group.
In this case, when we can't find an appropriate value,
we "look ahead" to see the next instance.
