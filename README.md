# Coapplicative Functors

This library provides a dual of Applicative functors:
covariant functors which can split over Either instances.

Some Comonads have well-behaved CoApplicative instances
that agree with context extension.
Notably this includes NonEmpty lists.

Comonads which agree with their CoApplicative instance
have "good" pattern-matching in which we may examine
the context inside the body of branching code.
This means that any two contexts which are in the
same branch will always see compatible views.

A newtype wrapper for one instance is provided for
any CoApplicative, but this usually
does not commute with duplication, and so different places
in the context may see different values.
