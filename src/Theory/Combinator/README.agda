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
       rather than a theorem.  `Scope`, `Lin`, `Match`, `Layout` and
       `ResTy`/`MatchTy` do this.  `Annotated/Typing` is the one departure,
       and it is exception 3 below: its judgment is an erasure fibre over
       an intrinsically typed core, so an indexed `data` on purpose.

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
   IV.  THE THREE DOCUMENTED EXCEPTIONS
   ============================================================

   The first two are in `Match`, and all three are arguments rather than
   lapses.

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

   `Annotated/Typing`'s judgment is NOT A RECURSION ON THE MODEL, against
   convention 1.  `Der (Γ , A) t` is `Σ[ c ∈ Core Γ A ] (erase c ≡ t)`: a
   term of an intrinsically typed core syntax, together with the evidence
   that it elaborates the source.  The argument is about which claims get
   checked.  A recursive judgment verifies the checker against itself and
   itself against nothing, and "this predicate is STLC typing" is exactly
   the claim nobody was making good on; carrying the core term collapses
   that layer, since `elab` is `fst`, "the output is well typed" is the
   type of `fst`, and "the output erases to the input" is `snd`.

   The cost is paid in two places and no more.  `isProp` is a retraction
   onto the old recursive judgment -- which survives as `Der⁻`, demoted
   from definition to lemma -- rather than a two-line induction, and
   `unrollNode` recomputes that fibre instead of finding its premises
   already separated.  The `SplitError` convention 1 predicts does NOT
   appear: the core term is matched only against itself, and equations
   between source terms are projected rather than unified, which is the
   trick a `Precise` proof needs anyway.

   Worth generalising, since a seventh client will face the choice.  Make
   the judgment intrinsic when the client HAS an intended semantics its
   judgment could get wrong -- a typing discipline, a scoping discipline,
   an elaboration -- and leave it recursive when the judgment is its own
   specification, as `Layout`'s indentation rule is.  And note what the
   intrinsic form nearly costs: `Core` resolves a variable by a `Lookup`
   and not by a numeral, because with a named source language a numeral
   makes `erase` non-injective under shadowing, the fibre stops being a
   proposition, and `ND` would count two derivations for `λx.λx.x`.  The
   judgment being a proposition is a fact about the SOURCE language, and an
   intrinsic judgment is the place it has to be re-established.


   ============================================================
   V.  KNOWN GAPS
   ============================================================

   These are `Core`'s, restated.  None of them is a bug; all of them are
   places where the types permit less than the development wants.

   GAP 1 -- `⊗ᴰ` IS NOT A `Functor` CODE.  CLOSED, AND THE CLOSING IS THE
   ARGUMENT FOR NOT USING IT.

   `Theory/Type/Code/Base` now has `⊗ᴰe`, whose slots are indexed by the
   whole splitting, beside `⊗e`, whose slots are independent.  The cost
   was seventeen cases across `Code/Base`, `Inductive/HLevels`,
   `Code/Container` and `Guarded/Justification`; every one of them is its
   `⊗e` sibling with `F a` replaced by `F ms a`, including the four that
   are proofs (`reconstructF`, `mapG≡map`, `isSet⟦_⟧`, `map-∘`).  Nothing
   in the monoid development noticed.  So the CODE side of the gap was
   real and is gone.

   What the gap was protecting is the CLIENT side, and `Lambda/Scope` --
   re-expressed as `μ ScopeF` and then read back -- is the measurement:

     * A `μ` costs a universe.  `ℓF ℓ-zero` is `ℓ-suc ℓ-zero`, and
       `NodeArgs` is uniform in its level, so every slot that is NOT
       recursive has to be `Lift`ed to meet the ones that are.  `Scope`'s
       two of four were, and so were their `Decidable`s.
     * `⟦ Var x ⟧` is a `Lift`, so `roll`/`unroll` still do slotwise
       wrapping -- the twelve hand-written lines become fourteen.
     * `⟦ ⊕e ⟧` is a sum over ALL operations, so `unroll` must FIND the
       summand the cover cell names.  That is no-confusion, which is the
       cover's `disjoint` field, spelled out again as nine cases.
     * AND IT BREAKS CONVENTION 1.  A `μ` is an indexed `data`, so the
       judgment stops REDUCING on the term.  `Scope [] (tvar 0)` used to
       BE `⊥`; now a derivation has to be unrolled one node before its
       premise is visible.  One line of `ScopeTests` measures exactly
       that, and it is the only line of thirty-five that changed.

   The recommendation is therefore: use `⊗ᴰe` when you want a code -- a
   `Container`, a `Guard`, an `isSetμ` -- for a grammar with a binder, and
   do NOT use it to define a judgment.  Convention 1 is still right, and
   `rollNode`/`unrollNode` by hand are still cheaper than the `μ` that
   would generate them.

   Worth knowing either way: the dependency is an artefact of NAMED
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
   this whole framework, needs a chosen head.

   `Instances/Bag` is that paragraph, proved.  `Bag/Failure` refutes
   `Precise _⊙_`, refutes `Disjoint NodeAt`, and refutes the cover by
   chosen head as well -- so the gap is not a missing lemma.  `Precise ε·`
   survives, which is exactly the wrong half: a client over the
   commutative theory can reach `Ans-node` only at the operation with no
   slots.

   `Bag/Chosen` is the repair and its price: precision comes back only by
   CHANGING THE THEORY to one whose free model is `List El`, since
   `Precise o` quantifies over every element of the result sort and so is
   a property of the signature that no later side condition can restore.
   `Bag/Chosen/Quotient` then measures the loss -- `Sorted` is provably
   not the pullback of ANY predicate on bags, while `Occurs` is, because
   it is a fold.  The verdict the two modules support is that the
   framework extends to the NORMAL FORMS of a quotiented theory and not to
   the theory, and that a client over the normal forms says something
   about the quotient exactly when its judgment is a homomorphism.

   ============================================================
   VI.  ADDENDUM: `Ans-re`, AND A THIRD KIND OF OUTCOME
   ============================================================

   Written after `Unify` landed, which is why it sits at the end rather
   than in section I.

   `Ans-re` REINDEXES AN ANSWER ALONG A MAP OF MODEL ELEMENTS.  Every
   judgment before `Unify` had its premises at SUBTERMS, and `Ans-node` is
   already the reindexing for those -- a slot's projection out of its node
   is the one map a signature hands you.  A judgment that is a MACHINE has
   a premise at a state COMPUTED from the conclusion's, and no operation of
   any signature produces that state.  Hence the field.

   It is deliberately WEAKER than a monadic bind: `f` maps model elements
   and is fixed before any answer is asked, so a later premise still cannot
   read an earlier premise's derivation.  The prediction that unification
   would need bind was wrong; it needs reindexing.

   AND A CORRECTION TO SECTION II.  It is tempting to read the `Route`
   obligations as LOCATING an algorithm's uniqueness theorem -- `disjoint`
   IS coherence, `disjoint` IS uniqueness of synthesis.  Three clients now
   say otherwise, in three different ways:

     * `Class/Resolve` -- `disjoint` is coherence, verbatim.
     * `Bidir/Typing` -- the same theorem, but the content sits in `into`
       (`soundInfer`), because the cells were chosen as the fibres of a
       candidate function.  `disjoint ∘ into` is uniqueness; how it splits
       between the two is a design choice.
     * `Unify/Check` -- NO ROUTE ARISES AT ALL.  The existential collapses
       at the definition of the judgment, so uniqueness is `isPropSol`,
       definitional, and the framework never gets to ask for it.

   So the obligation is CONSERVED, not LOCATED, and a judgment can be
   arranged so that it is discharged before the framework ever sees it.
   That is the useful form of the observation; the sharper one is false.

   ============================================================
   VII.  ADDENDUM: TWO CLIENTS, JOINED AT A SIDE CONDITION
   ============================================================

   Written after `Instances/Infer` landed, which is the first client whose
   premises are discharged by ANOTHER client.  Type inference for
   unannotated terms is a judgment over the term theory whose type
   equations are solved by `Unify`, a judgment over the stack theory.

   THE JOIN IS THE SIDE-CONDITION MECHANISM, AND IT NEEDED NOTHING NEW.
   `Unify/Check` at `Answer/Decidable` is a `Decidable`; `side`/`Ans-ofDec`
   takes a `Decidable`; `decSolv` is the two lines that put them together.
   No change to `Core`, no change to `Unify`, and the outer client stays
   polymorphic in its own answer.  Three consequences are worth recording.

   1.  THE JOIN IS ONE-WAY.  `Ans-ofDec` consumes a DECISION, so the inner
       client is pinned to `Dec` however the outer one is instantiated: an
       inference checker at `ND` still calls a unifier at `Dec`.  There is
       no `Ans A ⊢ Ans B` in the interface and there should not be -- it
       would be a bind, which section VI records the framework as declining.
       So clients compose along `Decidable` and not along `Ans`.

   2.  A SIDE CONDITION IS LOCAL AND UNIFICATION IS GLOBAL, SO THE JOIN
       LANDS AT A MODE CHANGE.  Threading a substitution between sibling
       premises is a premise index that is a previous premise's OUTPUT,
       which nothing provides; and solving at every node is degenerate,
       since a node's constraint set contains its children's, so the
       premises would say nothing the condition had not already said.  What
       is left is to split the judgment: the syntax-directed part generates
       constraints and postpones every equation, and ONE conjunction with
       the other client's judgment discharges them.  `Bidir`'s two-mode
       family is the shape that fits, with `&` where `Bidir` has `⊕ᴰ`.

       The general rule this suggests: a client composes with another
       exactly when the other's judgment can be stated at a SINGLE index
       computed from the first's -- and the price of computing that index
       up front is that the first judgment loses everything the second was
       going to decide.  `Infer`'s `Gen` is scope checking and nothing more.

   3.  COMPLETENESS SPLITS ALONG THE SAME LINE, AND THAT IS THE REAL
       FINDING.  A judgment refuted NODE BY NODE inherits completeness from
       the cover's `total` for free; `Infer` proves exactly that for its
       shape mode, over infinitely many types, in twelve lines.  A judgment
       whose refutation is an existential over SUBSTITUTIONS inherits
       nothing, because no cover of the term model splits by solvability --
       and `Ans-ofDec` asks for a decision, not for a characterisation, so
       the framework never demands the missing half either.  Both facts are
       structural.  The lesson for client eight is that the side-condition
       mechanism buys composition at the cost of the refutation's meaning,
       and that a client using it owes an explicit statement of what its
       `no` says.  `Infer`'s header is that statement.


   ============================================================
   VIII.  ADDENDUM: COMPLETENESS AS A COVER, AND ITS ASYMMETRY
   ============================================================

   `Theory/Type/Decidable/Base` had `decisionCover`/`coverDecidable`/
   `dec-cover` from the start and no client ever used them.  A decision IS
   a cover of `Bool`, and under that identification the cover's two laws
   are the two halves a checker owes:

     `total`     an `A` or a refutation of `A` -- soundness AND completeness
     `disjoint`  never both -- consistency

   `Combinator/Complete` surfaces this and exports `decideCell`: a cover
   over ANY discrete index makes EVERY cell decidable, since `total` names
   the cell an element is in and `disjoint` refutes the others.  So the
   discipline is: exhibit the judgment as a CELL of a cover.
   `Match/Exhaustive`'s `decClause` is the worked example, and it decides
   each clause without going near `fix`, `look` or an `AnswerFunctor` --
   that cover had been paying for a checker nobody collected.

   THE IDENTIFICATION IS ASYMMETRIC, and this is the part to know before
   reaching for it:

     * it pays as "EXHIBIT A MAP INTO A CELL" whenever the specification
       IMPLIES the judgment.  `Infer`'s `Gen` is this case: `genCell`,
       `refuteCor`, `shapeVerdict`.
     * it pays as "`total` IS COMPLETENESS" only when the judgment and the
       specification COINCIDE.  `Unify`'s `Solvable` is this case.

   `Infer`'s `Gen` cannot be the second.  The cover one wants has cells
   `Gen` and `¬ Cor`, so `disjoint` would be `Gen → Cor` -- and `noCorXX`
   refutes it at `x x`, which is well scoped while no intrinsically typed
   core term erases to it at any types over any scope.  `Gen` is strictly
   weaker than typability; the only cover it inhabits is `DecCover Gen`,
   whose `total` is decidability, not completeness.  The 28-line induction
   stands and any packaging is additive.

   AND A CORRECTION TO SECTION VI's PESSIMISM.  That section recorded the
   `AList` restriction as blocking completeness for unification.  It does
   not.  The obstruction is about the CARRIED ANSWER, not about
   solvability: restriction along `thin x` is not an operation on `AList`s
   -- the `n = 1` counterexample stands -- but it IS composition for a
   plain substitution.  `Unify/Solvable` quantifies over `Fin n → Tm m`
   and proves `complete : Solvable n ps → Sol n ps`; `Unify/Cover`
   packages it.  `mgu` still returns a chain and the tests still compare
   chains.  Only the specification changed.

   The cover is NOT structural -- `stackCover` splits by the head
   equation and solvability is not a head property, so no amount of
   no-confusion yields it; what yields it is the checker's own recursion
   plus three lemmas.  It is NOT circular -- the transported decision is
   for `Sol`, and `dec-retract`'s backward map IS the missing
   completeness.

   ============================================================
   IX.  A PRACTICAL TRAP: `--lossy-unification` ACROSS ANSWERS
   ============================================================

   `PatComp/Tests` did not finish in 25 minutes.  One word fixed it:
   `--lossy-unification` → `--no-lossy-unification`, after which the file
   checks in 11 s.

   The mechanism generalises to any client that asserts two backends
   agree.  `compile` and `compileFirst` are the SAME term at
   `𝒯 := DecAnswer` and `𝒯 := MaybeAnswer`, so both sides present the same
   head at every step, the first-order approximation fires every time, and
   each firing attempts `DecAnswer =?= MaybeAnswer` -- a seven-field
   dependent record quantified over every level, sort and grammar.  Always
   fails, always expensively, retried per subtree.  Roughly 3.5x time and
   3x heap per level of tree depth.

   Against a LITERAL it is free, because the heads differ and the
   approximation never fires.  So a cross-answer equality is the thing to
   avoid, not `--lossy-unification` as such.

   AND A MEASUREMENT WARNING.  At a small `-M` every one of these looks
   like non-termination: the same file ran 90 s without finishing at
   `-M2G` and 10 s at `-M6G`.  "Does not terminate" and "wants more heap
   than you gave it" are indistinguishable from outside.  Raise the heap
   before diagnosing a hang. -}
module Theory.Combinator.README where
