# Theory.Instances.Monoid.Sat
satG should be called satTy
# Cubical.Algebra.Theory.Finitary.Free.ClosingElim
we should be able to include an elim that doesn't presuppose a prop, right?
# Bags
I'm not sold on how things are encoded. I don't like the View stuff,
its external and maybe unnecessary for quicksort

Bag.Order also is a bit external
Bag.Partition could be better I think too

Bag.Quicksort looks good I think. Provided that we are using ▷ and
▷-split correctly

Look through Rank, Sequence, and Sorted too here. Remember that the
goal is to provide a DSL for which we can write these intrinsically
verified algorithms. We have to be very deliberate throughout this
entire project to ensure t hat we areworkign in the DSL whenever
possible and that we have clear justification for stepping outside of
it (often when axiomatizing how connectives work)

# Lambda
We should bring in the Lambda scope checker and STLC typechecker from
the theory branch as examples of the DSL at the appropriate
theories. We tie together multiple phases in these tests as well

That is, we should have the lambda tests use the unicode lexer, parse
these into lambda terms, scope check these lambda asts, and then type
check or smth like this

We want to demonstrate a DSL framework of verified front ends and thus
need to have ergonomic and sound plumbing between different
instantiations of the framework at different theories

# comments
agents write a lot of AI slop comments that need to be cut. They read
very amateurish. Further, code should be as self-documenting as
possible. When naming things, including local where-bound helpers, we
need semantically relevant names (not just `go` and the like)

# Tests
concrete test modules should follow this rough skeleton

1. Use the unicode lexer so that the input is human readable
2. Use the uniform testing interface `passes` and `rejects` (does this
   exist?) found in  Theory.Type.SemanticAction.Base. Check that these
   test case helpers aren't duplicated
3. When writing the correct output, be sure to use a semantic action
   to display human-readable output. I think there may be some
   outstanding work on writing "display" semantic actions for each
   type to give a cnanonical ouptut

This forbids test cases that look like
```
badApp-refuted : Ty? [] (App (Lam vx Na (Nm vx)) Tru) → Empty.⊥
badApp-refuted = theNotD (typed? [] (App (Lam vx Na (Nm vx)) Tru)) Eq.refl
```
as this isn't a usable format to read the test

with this uniform strategy ALL of our test cases are readable. Let's also put test cases
in relatively uniform locations. In thedirectory that they're in they
should be in some file called Tests or perhaps <X>Tests (to
disambiguate). This means we shouldmove any tests/examples that are at
the bottom of a definitions file into its own test file for readability

We should also sometimes have stress test files that push the input
size up so that we can test how long typechecking time gets for large inputs

# stuff that's too much to review
There is so much of the automata stuff that it is hard to
review. Please do an pass on this part of the code especially for
review. Likewise, do further passes over the LL/Routed stuff; likewise
the regex stuff. and sequential ambiguity

# While you're at it...
Do a very fine grained audit/review of the entire project with several
subagents in parallel so that we can get a good thorough analysis of
style, internality to the DSL, naming, modularlity, no code
duplication, comments, etc

Measure for all engineering best practices and maintainability as well
