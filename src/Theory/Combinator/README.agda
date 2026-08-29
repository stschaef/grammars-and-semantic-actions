{- WHAT TO READ BEFORE WRITING CLIENT SEVEN.

   `Theory/Combinator/Core` is a framework for syntax-directed judgments
   over an arbitrary finitary algebraic theory, and there are six clients
   of it.  This file is what the six agree on, why they agree on it, and
   where they do not.  It contains no definitions, deliberately: a
   convention that could be enforced by a type would be a type.


   ============================================================
   I.  THE INTERFACE, IN ONE PAGE
   ============================================================

   A GRAMMAR is a proof-relevant predicate on the free model:
   `TheoryTy ℓ s = ↓M s → Type ℓ`.  A map of grammars is `A ⊢ B`, which is
   `∀ m → A m → B m`.  Writing something as a `⊢`-term rather than as an
   Agda function is what "internal" means here, and it is not decoration:
   a `⊢`-term is uniform in the model element, so it cannot secretly
   inspect one.

   Four things make a judgment run.

   1.  A NODE.  `⊗ᴰ o As m` is "`m` is `op o ms`, and each argument `ms a`
       satisfies its slot `As ms a`".  The `ms` in `NodeArgs` is the whole
       point: a later slot's grammar may mention an earlier slot's VALUE.
       `Operation/Base`'s `⊗ᵘ` -- independent slots -- is the constant
       case, and it cannot state a binder, because the scope of `lam n t`
       is `Γ , n` and `n` is slot zero.

   2.  A COVER.  `Cover Y Λ` is `total` (every element is in some cell)
       plus `disjoint` (no element is in two).  `look` is case analysis
       through a cover, and inside branch `y` you additionally HAVE `Λ y`
       as a hypothesis -- which is the fact that makes everything else
       work.  For a free term algebra the cover is `NodeAt`, by head
       operation: `total` is the induction principle and `disjoint` is
       no-confusion, so prediction is always LL(1) and there is no window,
       no lookahead width, and nothing to tune.

   3.  A GUARD.  `Theory/Type/Later/Indexed`'s `▷` over a well-founded
       order.  A recursive call is `callAt`, which demands a proof of
       descent; left recursion is a type error rather than a hang.  `fix`
       is Löb.

   4.  AN ANSWER.  `AnswerFunctor` is what a checker's output is, and it
       is the only thing a client leaves abstract.  Its fields:

         Ans          what an answer about a grammar is
         Ans-map&     relabel, UNDER A HYPOTHESIS.  Divariant, because
                      `Dec` moves a refutation backwards.  The hypothesis
                      is what a cover cell supplies, and it is what makes
                      both directions `⊢`-terms rather than pointwise
                      functions -- a grammar and one of its unfoldings
                      agree only where the head is known.
         Ans-⊕&       alternation.  THIS ONE FIELD is the entire
                      difference between the three backends: `Dec` decides
                      both sides, `Maybe` commits left, `ND` appends.
         Ans-&&       conjunction, which is how a side condition reaches
                      a rule at all (see III.4)
         Ans-ofDec    every answer can read a decision
         Ans-node     answers at the slots give an answer at the node

       Two refinements sit on top.  `CovariantAnswer` adds a plain `fmap`
       and an EMPTY ANSWER; `Dec` has neither, and the second refusal is
       the interesting one -- `⊤Ty ⊢ DecTy A` at arbitrary `A` is a
       decision procedure, not a default.  One cannot decline to decide.
       `CommittingAnswer` adds `Ans-route`, which answers an indexed sum
       by consulting a `Route` rather than every alternative.

   The three backends are `Answer/Decidable`, `Answer/Incomplete` and
   `Answer/NonDet`.  A client mentions none of them.


   ============================================================
   II.  THE RULE OF THUMB: DOES YOUR JUDGMENT FIT?
   ============================================================

   ONE QUESTION.  For each premise of each rule: is its index a FUNCTION
   of the conclusion's index and the node's model values?

   If yes, the judgment fits, and it fits with nothing but `⊗ᴰ`, `look`
   and the guard.  This is a lower bar than it sounds, because `⊗ᴰ`'s
   dependency is generous:

     * `Lambda/Scope` -- the body is checked in `ms theBinder ∷ Γ`, an
       index computed from slot zero's value.
     * `Annotated/Typing` -- `lam` uses the dependency twice, for the
       body's context AND its type.  The annotation on `appOp B` is what
       makes the function's premise index computable; drop it and you owe
       a `Route`.
     * `Annotated/Linear` -- the context SPLIT `Γ₁ ⊎ Γ₂` looks like an
       output and is not.  Which variables `f` consumes is a syntactic
       fact about `f`, so `Γ₁ = keep Γ f` is a function of the
       conclusion's context and slot zero's value.  Worth stating
       generally: `⊗ᴰ`'s dependency IS the leftover/threading discipline,
       the same idea the monoid framework spends a continuation on.
     * `Layout/Offside` -- the state after a token is a function of the
       state before it and the token's own column.  For a one-argument
       operation `⊗ᴰ` degenerates to a state machine's transition
       function, which is why layout -- not context-free by any measure --
       is syntax-directed in this framework's sense.

   If NO, one of two things is true.

   (a) The premise index is an OUTPUT, and the alternatives are known
       EXCLUSIVE.  Then you owe a `Route`: a cover of the model by
       `Maybe Y`, and `Ans-route` asks the answer only where the cover
       points.  The `disjoint` field is not bookkeeping -- it is the real
       side condition of your judgment, wearing a different hat:

         bidirectional typing     `disjoint` = uniqueness of synthesis
         instance resolution      `disjoint` = COHERENCE

       `Class/Resolve` is that second identification, and it is exact:
       `Coherent T` -- no two instances of a class share a head -- is
       verbatim the hypothesis `Routed.route` needs, and verbatim what
       GHC's coherence check verifies.

   (b) The alternatives are NOT known exclusive.  Then you have no
       `Route`, and `Ans-anyFin` -- ask every alternative, keep every
       answer -- is all that is left.  It needs `Ans-empty`, so it is
       available at `Maybe` and `ND` and NEVER at `Dec`.  The split is
       exactly: an answer that can commit routes, and an answer that can
       give up enumerates.  This is why `Class/ResolveTests` can exhibit
       an incoherent instance table at `ND` as the number 2, and cannot
       write a decision procedure for it at all.


   ============================================================
   III.  HOUSE CONVENTIONS
   ============================================================

   Nine.  They are what the six clients have converged on, and a seventh
   that departs from one of them should say why in its header, as the
   two documented exceptions below do.

   1.  DEFINE THE JUDGMENT BY RECURSION ON THE MODEL, not as an indexed
       `data`.  An indexed family gets `SplitError.UnificationStuck` on
       the model's constructors in every branch of the checker, and the
       recursive form additionally makes `isProp` a two-line induction
       rather than a theorem.  All five judgments do this: `Scope`, `Der`,
       `Lin`, `Match`, `Layout`, `ResTy`/`MatchTy`.

   2.  DISPATCH WITH `look nodeCover`, never with a pattern match on the
       model element.  This is the convention everything else hangs off.
       Matching on the term is what forces a POINTWISE relabelling, and a
       pointwise relabelling is what lets a term unroll to one node
       instead of to the cover -- which dodges an obligation rather than
       paying it.  Going through the cover hands you `NodeAt o` as a
       hypothesis, and that hypothesis is what `Ans-map&` wants.

   3.  `Slots o i` IS A LIST OF PREMISES AND NOTHING ELSE -- pure
       recursive calls, one per argument of the operation.  If reading
       `Slots` does not read like the rule's premises, something is in
       the wrong place.

   4.  SIDE CONDITIONS GO AT THE NODE, NOT AT A SLOT.  An operation has
       exactly its arity many slots, so a condition that is not itself an
       argument has nowhere of its own to sit.  State the cover's cell as

           Cell o i = ⊗ᴰSet o (Slots o i) &Set SideSet i

       and collect every rule's condition in one `SideT`.  `Layout` is
       FORCED into this shape -- `nilOp` is nullary and has no slot to
       ride at all -- and `Linear` is merely honest for it: its partition
       check constrains the APPLICATION, not the function, and hanging it
       off the function's slot (which is what `Linear` used to do) both
       misstates the rule and stops `Slots` from being convention 3.

       Index `SideSet` by whatever carries the data the condition reads:
       by the operation when the operation carries it (`Layout`'s
       `consOp (k , c)` carries the column), by the model when the model
       carries it (`Linear`'s `partitions Γ f a` reads two subterms).

       A condition on a NAME argument is not a side condition -- it is a
       slot, and it stays one.  `Typing`'s `ArrSet A B` and `Linear`'s
       `SingSet Γ A` sit at `nm`-sorted arguments and are premises like
       any other.

   5.  EVERY SIDE CONDITION COMES WITH A `Decidable` AND ENTERS VIA
       `Ans-ofDec` -- through `side`, or through `none` for a condition
       that is uniformly false.  Never plumb a decision in by hand.  This
       is the only route by which an answer learns anything it did not
       compute itself, and keeping it single is what lets the same source
       text run at three answers.  Name the decision even when it is
       trivially true (`Scope`'s `dec⊤`); an exception to a convention
       costs more than a line.

   6.  `rollNode` AND `unrollNode` ARE `⊢`-TERMS.  `roll` goes
       `ty (Cell o i) ⊢ J i`; `unroll` goes `J i & NodeAt o ⊢ ty (Cell o i)`
       and NEEDS the cell, for the reason in convention 2.  Twelve lines
       per client, by hand, and see gap 1 for why they are by hand.

   7.  PREMISES CARRY THEIR EVIDENCE.  `InCtx`, `Lookup` and `Close` are
       proof-relevant refinements of boolean tests: a `Bool` says the name
       is bound, a chain of "not here" steps ending in a hit says WHERE,
       and counting the steps is the de Bruijn index.  All three are still
       propositions -- the summands are mutually exclusive -- so
       proof-relevance and unambiguity are not in tension.  The readout
       then READS the derivation instead of recomputing it, which is the
       whole reason to have derivations at all.

   8.  READOUTS ARE `SemanticAction` + `observe`.  A readout is
       `A ⊢ Δ X`, and `observe` is the single place a `⊤Ty`-map is read
       out of the language.  The front end of every client is the same
       three-term composition:

           compile = observe checker (semact-dec action)

       `Lambda/Nameless`, `Annotated/Elaborate`, `Layout/Render`,
       `Match/Bindings` and `Class/ResolveTests` all spell exactly that.
       Do not write a boundary by hand.

   9.  TESTS ARE `refl`, so the typechecker runs the checker, the guarded
       fixpoint and all three answers on concrete input.  A test that
       needs a proof is a test that did not reduce, and a checker that
       does not reduce is a checker nobody can run.

   And a negative convention: NOTHING IN A JUDGMENT MODULE MENTIONS `Dec`,
   `Maybe` OR `ND`.  If it does, the client has picked an answer, and the
   point of the framework was not to.


   ============================================================
   IV.  THE TWO DOCUMENTED EXCEPTIONS
   ============================================================

   Both are in `Match`, and both are arguments rather than lapses.

   `Match/Judgment`'s `pwild` and `pvar n` do NOT go through `look`.  They
   are not syntax-directed on the value at all -- they hold at every head
   -- so they are `side` and never reach the cover.  A rule with no
   premises and no restriction on the scrutinee is a decision, not a node,
   and pretending otherwise means writing the same trivial node once per
   cell.  For the same reason `Match` has no `Cell` and no `SideT`: it has
   no side conditions, and `&Set` with a `Unit` would be noise.  Its
   `clashAt` -- refuting `Match pfalse vtrue`, where `vtrueOp` is nullary
   and has no slot to carry the refutation -- goes through `none`, which
   is `side (dec-no ∘⊢ n)`, so convention 5 holds even there.

   `Match/Bindings`' `observeAll` is a hand-rolled boundary: it maps the
   action over `ndToList` rather than composing with an `observe`.  There
   is no `observe` for a nondeterministic answer, because `observe` reads
   ONE value out of a `⊤Ty`-map and `ND` is a list -- the boundary is
   crossed once per derivation instead of once.  Supplying the missing
   combinator means adding to `Answer/NonDet`, which is a change to the
   backend interface and worth making deliberately.


   ============================================================
   V.  KNOWN GAPS
   ============================================================

   These are `Core`'s, restated.  None of them is a bug; all of them are
   places where the types permit less than the development wants.

   GAP 1 -- `⊗ᴰ` IS NOT A `Functor` CODE.  `Theory/Type/Code/Base` has
   `⊗e`, whose slots are independent, so a grammar that needs the
   dependency cannot be a `μ` and gets its `roll`/`unroll` written by
   hand.  Closing it means adding a `⊗ᴰe` constructor, which every match
   on `Functor` would then have to cover -- around seventeen sites across
   `Code/Base`, `Inductive/HLevels`, `Code/Container` and
   `Guarded/Justification`, all shared with the monoid development.

   Worth knowing before doing it: the dependency is an artefact of NAMED
   syntax.  `lam n t` scopes its body in `Γ , n`, and `n` is a slot value;
   a de Bruijn `lam t` scopes it in `B ∷ Γ`, which mentions no slot at
   all.  Surface-syntax judgments need `⊗ᴰ` and core-syntax ones do not --
   which is one more reason compilers go nameless early.

   GAP 2 -- NULLARY OPERATIONS.  `Ans-node` cannot refute an operation
   with no slots, because a refutation travels through a slot, and a side
   condition attached to one has nowhere to ride.  Two clients hit this
   independently -- `Match` at `vtrueOp`, `Layout` at `nilOp` -- and
   neither needed a change to `Core`: `Ans-map&` will do it, since the
   cover cell is exactly the knowledge that makes the grammar empty, and
   `Ans-&&` will attach the condition at the node.  Convention 4 is the
   second of those, promoted to a rule -- but it is a rule the types
   PERMIT rather than ENFORCE.  Nothing stops client seven from hanging a
   condition off a slot again.

   GAP 3 -- `Dec` HAS NO EMPTY ANSWER, so it has no `Ans-anyFin`, so a
   judgment whose alternatives are not known exclusive has no decision
   procedure in this framework.  That is not an oversight to be patched:
   `⊤Ty ⊢ DecTy A` at arbitrary `A` IS a decision procedure.  An answer
   has to say what it does with the alternatives it did not take, and
   `Dec`'s only honest answer is to refute them.

   GAP 4 -- PRECISION IS WHAT REPLACED "THE ALPHABET IS DISCRETE", AND
   QUOTIENTED THEORIES DO NOT HAVE IT.  `Precise o` -- the decomposition
   of `m` along `o` is unique -- is what lets a refutation at one slot
   refute the whole node.  A free term algebra has it at every operation;
   the free monoid has it only for `literal c ⊗ -`, which is why that
   development has three token rules where this one has `Ans-node`.  For
   a commutative theory the node cover is not disjoint at all -- the bag
   `{a,b}` is a node of two different heads -- so prediction, and with it
   this whole framework, needs a chosen head. -}
module Theory.Combinator.README where
