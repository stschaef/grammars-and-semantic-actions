# Bottom-up and derivative parsing in the DSL

`src/Theory/Instances/Monoid/Combinator/`.  Three separate lines live here, in
`Ascent/`, `LeftCorner/` and `Derivative/`.  They were all filed under `LR/`
for most of the investigation and that name was wrong for every one of them:
`Ascent/*` and `LeftCorner/*` reach LC(k), not LR(k), and `Derivative/*` is
strictly more general than LR.  See "What is and is not LR" below.

## Line 1: recursive ascent — `Ascent/*`

`Combinator/Core`'s parser is polymorphic in the *continuation*.
`Ascent/Base`'s is polymorphic in the *stack*, as the residual it owes the goal:

    Parser ℓK a c A = &[ K ] ( ▷?a (Ans K)          ⇒ ▷?c (Ans (A ⊗ K)) )
    Asc    ℓB a c A = &[ B ] ( ▷?a (Ans (B ⊸ Goal)) ⇒ ▷?c (Ans ((B ⟜ A) ⊸ Goal)) )

`⊗ K` becomes `B ⟜ -`; the answer is taken at `- ⊸ Goal`.  Every LR action is
then one of `Core`'s combinators read in the mirror, and each is a `⊢`-term
already in `Residual.agda`, which says so in its own comments:

| LR      | `Ascent/Base`  | is `Core`'s | built from                          |
|---------|-----------|-------------|-------------------------------------|
| shift   | `shift`   | `tok`       | `Ans-lit` then `⊸⟜-swap`            |
| reduce  | `reduce`  | `mapP`      | `⟜-precomp` at the production term  |
| goto    | `goto`    | `seq`       | `⟜-curry`, the tower reassociating  |
| accept  | `runA`    | `runP`      | `⊸-unitl` at `⟜-intro ⊗ε-unit-l`     |
| predict | `chooseA` | `choose`    | `Λ-total` observes, `π o` commits   |

The stack is the `⟜`-tower.  No stack of states, no pop count, no goto table;
a production is the term `β ⊢ A` itself, and `start : (Goal ⟜ Goal) ⊸ Goal ⊢
Goal` is the whole soundness statement, because the states are grammars.

* `Ascent/Balanced` — `S → ( ) | ( S )`, the minimal example, *before*
  lookahead: it chooses with `pick`, which runs both branches and keeps the
  first that worked.  Kept for the smaller fixpoint and as the before-picture.
* `Ascent/Expr` — `E → E + T | T`, `T → ( E ) | x`, with `Predict.chooseA`.
  Non-regular, left-recursive, mutually recursive.  Observes the class once
  and commits; nothing is attempted speculatively.  `x + x + x` yields
  `add (add (emb var) var) var` — left-associated, i.e. a parse of the
  *original* left-recursive grammar, built by the reductions.  The LR
  condition is exported as a checked term (`E-noConflict` etc.), out of
  `Predict.altDisjoint`: two branches at different classes cannot both match.

One backtrack point survives deliberately: `sR` is nullable and ε cannot claim
a class, so the ε-branch sits outside the committed choice under `<|>` —
exactly as `Productions.step` does it.  It costs one O(1) probe.

## Arbitrary lookahead width — `Ascent/Lookahead`, `Ascent/LookaheadDemo`

`Predict` in `Ascent/Base` is fixed at width 1: it takes `Λ₁`/`M₁` directly.
`Ascent/Lookahead.WidePredict` is the same module with the cover abstracted --
it takes the class type, its discreteness, the fibre family, a `Cover`,
and the per-class guard `lead`, and nothing else changes.  `WidthPredict`
instantiates it at `Lookahead/Window`'s `Λw`/`windowCover n`, so the width
is a parameter of the *instantiation*, not of the combinators.

`Ascent/LookaheadDemo` is the smallest grammar that needs width > 1:
`a b c` versus `a b d`, which no width-1 table separates.  `branchesSeparate`
is `altDisjoint` at the two 3-windows, checked.

This buys LC(k), not LR(k).  The lookahead is consulted at a *choice*;
an LR item set is a set of live productions and the commitment happens at
the reduction.  `S → A b | B c`, `A → a A | a`, `B → a B | a` is SLR(1)
and outside LC(k) for every k: the deciding token comes after arbitrarily
many `a`s, and by then the choice was already forced.

## Not choosing at all — `Derivative/OneStep`

The way out of LC is to stop *eliminating* the `⊕` at a choice and start
*differentiating* it: carry the whole alternation forward and let the input
narrow it.  This was recorded here as "the LC→LR move", which was wrong -- it
overshoots LR rather than reaching it, since it removes commitment entirely
instead of deferring it behind a table and a lookahead.  See "What is and is
not LR".  `Derivative/OneStep` does this on a code language `CF X`
(`lit`, `ε̂`, `⊥̂`, `var`, `dv`, `⊕̂`, `⊗̂`), with

    ν  : nullability, a `Bool` fold
    δ  : the Brzozowski derivative, `δ (F ⊗̂ G) c = (δ F c ⊗̂ G) ⊕̂ nullOf (ν F) (δ G c)`

and proves both sound against the interpretation: `ν-sound` gives
`εTy ⊢ Int A A' F` when `ν F` is `true`, and `δ-sound` gives
`Int A A' (δ F c) ⊢ Dl c (Int A A' F)`.  `dv x` is the deferred
derivative of a variable, which is what keeps `δ` structural under
recursion.

The gap -- `CF` duplicates a fragment of the repo's `Functor` code type, so
`δ` does not apply to the `μ F` families `Decidable/Productions` and `Ascent/Expr` use
-- is closed by `Derivative/Parser` below, which redoes all of this at `Functor`
directly.  This file is kept as the smaller statement: it is where the `⊗`
rule and its soundness proof are legible without the fixed point on top.

## Line 3: parsing with derivatives — `Derivative/Parser`

`Derivative/OneStep` is one *step* of Might-Darais-Spiewak, not the
algorithm: `δ (var x) = dv x` hands the recursion back, `δ-sound` assumes
a `step` per nonterminal, and nullability is an oracle `X → Bool`.
`Derivative/Parser` ties the knot, at the repo's own grammar codes rather than a
bespoke `CF`.

Given `F : (x : X) → Functor _ X xs tt` with `A = μ F`, the derivative
grammar is another `μ` over the *same* nonterminals, `D = μ (δ ∘ F)`.
`δ` sends `Var x` to `Var x` -- now naming the derivative nonterminal --
and freezes the occurrences that must not be differentiated as constants
`k ⟦ G ⟧`, which is legal precisely because `μ F` already exists.  That
freezing is what `Derivative/OneStep` needed the second constructor `dv`
for, and it is why this `δ` can be iterated where that one cannot
(`δ (dv x) = ⊥̂` after one step).

Three things follow that the `Bool` version cannot state.

* **Nullability is a grammar.**  `Nu A = A & εTy` is *every* null parse.
  `Regex/Derivative`'s `Dl-⊗-in-r` takes a section `εTy ⊢ A` and so
  commits to one; `Dl-⊗-out` forgets it entirely.  The new
  `Dl-⊗-out⁺`/`Dl-⊗-in-r⁺` keep `A & εTy`, so an ambiguous left factor
  contributes all of its derivations.  That is the difference between a
  recogniser and a parser here.
* **Completeness, not just soundness.**  `Dl c (A x) ⊢ D x` is not of the
  shape `μ F x ⊢ _` that `rec` eliminates -- the derivative shifts the
  index -- so the fold cannot see it.  `Derivative/General`'s adjunction
  `∂[ ⌈ c ⌉ ] ⊣ √[ ⌈ c ⌉ ]`, with `∂[ ⌈ w ⌉ ] ≅ Dl-string w`, moves the
  derivative to the other side: `A x ⊢ √[ ⌈ c ⌉ ] (D x)` *is* a fold.
  This is the one place the right adjoint earns its keep.
* **No `step`, no `νv`.**  Both hypotheses are gone; the recursive
  occurrence is `Var x` and the motive supplies it.

The completeness fold carries the original parse alongside the
derivative one (`Mot x = A x & √[ ⌈ c ⌉ ] (D x)`), because `δ` freezes at
`μ F` while the fold has replaced `μ F` by the motive; `forget` projects
back.

`Derivative/ParserDemo` instantiates this at `S → x S | ε` and pushes a real parse
of `x` through `complete`, so neither theorem is vacuous.

**Iteration, and the parser.**  One letter is not a parser.  Because `δ`
freezes at `μ F`, the next derivative freezes at `μ (δ ∘ F)` -- which is
just `δ` of the already-differentiated system, so `δ*` is iteration and
nothing more.  This is exactly what `Derivative/OneStep` cannot do:
`δ (dv x) = ⊥̂`, so a second derivative annihilates every recursive
occurrence.  The level grows by one `ℓF` per letter, so `δ*` is indexed
by the word (`levOf`).

    δ* : (w : String) (F : (x : X) → Functor ℓ X xs tt)
       → (x : X) → Functor (levOf ℓ w) X xs tt
    sound*    : D* w F x ⊢ Dl-string w (μ F x)
    complete* : Dl-string w (μ F x) ⊢ D* w F x

and then the statement that makes it a parser -- consume the input by
differentiating, read the answer off the empty word:

    fromNull : εTy ⊢ D* w F x → ⌈ w ⌉ ⊢ μ F x
    toNull   : ⌈ w ⌉ ⊢ μ F x → εTy ⊢ D* w F x

Both are `sound*`/`complete*` moved across `∂[ ⌈ w ⌉ ] ≅ Dl-string w` and
out to the residual, where `⌈ w ⌉` makes them statements about the *word*
rather than about a derivative.  `Derivative/ParserDemo` runs both on `x x`, which is
the first word that exercises iteration: `DSxx`s frozen constants point
at `μ (δ ∘ Sbody)`, not at `S`.

**At the real grammar — `Derivative/ParserExpr`.**  `ExprGrammar` already presents
`E → E + T | T`, `T → ( E ) | x` as a `Functor` system `G`, which is
exactly the shape `Derivative/Parser` takes, so the derivative construction applies to
it with *no transformation at all*: no left-corner transform, no
left-factoring, no lookahead table.  This is the same left-recursive,
mutually recursive grammar `Ascent/Expr` parses by ascent and
`LeftCorner/Expr` parses by left-factoring, so the three techniques can be
compared on one grammar.

`treeX-computes` checks that the *value* survives, not just the types:
a parse of `x` goes through `toNull`, two derivative constructions, and
back out through `fromNull` and the grammar's own algebra as `emb var`,
by `Eq.refl`.  It needs an `unfolding` block, because `∂[_]_`/`√[_]_`
are `opaque` in `Derivative/General` -- a deliberate boundary there, not
a stuck transport.

**Still missing for an implementation: compaction.**  Adams-Hollenbeck-
Might's complexity result depends on simplifying `⊥ ⊗ x`, `ε ⊗ x` and
degenerate nodes away as the derivative graph is built.  `δ` here builds
the graph faithfully and normalises nothing, so this is the
specification a real implementation optimises, not the optimisation.
Also unproved: the round trip `sound ∘⊢ complete ≡ id⊢` as a *term*
equation.  `Derivative/ParserExpr.treeX-computes` checks one instance of it by
computation, which is evidence but not the theorem.  The theorem needs
β/η for the derivative split (`Dl-⊗-out⁺` against the two intros), and
those bottom out on `two-η` reshuffling -- `Fin 2` has no definitional
η, so reassembling a splitting is a path, and the equation component
then needs a `PathP` along it.  On top of that sits an induction over
codes.  `Dl-⊗-in-l` was rewritten to compute (`Eq.ap` rather than
`Eq.pathToEq`) as the first step; the rest is not done.

## Line 2: left-factor and fold — `LeftCorner/*`

A different technique, and **not** recursive ascent: transform the grammar so
`Core`'s existing LL machinery decides it, then rebuild the original grammar's
value with a `⊸`-fold.  `⊸` accumulates on the left, which is what makes the
tree lean left.

* `LeftCorner/LeftRec` — `E → E + a | a` over `a (+ a)*`.
* `LeftCorner/Defer` — `S → A b | B c`, `A → a A | a`, `B → a B | a`.  LL(k)
  for no k: `aaaaac` yields `viaB 5`, five tokens after the last chance to
  commit early.
* `LeftCorner/Expr` — the expression grammar, recognised by
  `Decidable/Productions` *unchanged* applied to the left-corner transform.

These are decidable, which the ascent line is not.  They are also strictly
weaker than LR: left-corner parsing is LC(k), and LL(k) ⊊ LC(k) ⊊ LR(k).

`ExprGrammar` holds the grammar both `Ascent/Expr` and `LeftCorner/Expr` parse,
so the two can be compared line for line.

## The decidability boundary — `Ascent/Decidability`

Checked in both directions rather than argued.

`Dec` is excluded from the ascent line, and **not** by anything about the
answer functor.  Of the nine uses of covariance in `Ascent/Base`, seven have a
converse and want only `DivariantAnswer`, which `Dec` has — the file proves
this by giving `⟜-curry⁻`, `⟜-unitr⁻`, and `reduce±` over `DivariantAnswer`,
instantiated at `DecAnswer`.

Two do not, and `noShiftConverse` is a machine-checked counterexample for why:
with the stack `⊥Ty`, `⊥Ty ⟜ literal c` is empty, so `(⊥Ty ⟜ literal c) ⊸ ⊥Ty`
holds *vacuously* at the empty word while `literal c ⊗ (⊥Ty ⊸ ⊥Ty)` does not.
`Owes B = B ⊸ Goal` is a universal over stacks, and a vacuous universal has
nothing to refute.  `runA`'s `idOwes` fails identically.

`shiftD`/`shiftD⁻` show the derivative does have both directions.  That is
suggestive, not a plan: `Dl w Goal` at the empty remaining input is `Goal w`,
so deciding it restates the original problem, and a reduction does not change
the consumed prefix, so at a pure-derivative state `reduce` has nothing to do.

## What is and is not LR

LR(k) is a *determinism condition on grammars* — the table has no conflicts —
not a parsing technique.  Measured against it:

| line           | states         | commits?          | class    |
|----------------|----------------|-------------------|----------|
| `Ascent/*`     | chosen by hand | yes, on lookahead | LC(k)    |
| `LeftCorner/*` | chosen by hand | yes, after the LC transform | LC(k) |
| `Derivative/*` | derived (`δ`)  | never             | all CFGs |

The reason the derivative line kept getting called LR is real but partial: an
LR(0) state is the item set live after a prefix `u`, and as a language that
*is* the derivative by `u`.  The dot-advance and closure rules are `δ`'s two
clauses —

    δ (F ⊗̂ G) c = (δ F c ⊗̂ G)  ⊕  (Nu F ⊗̂ δ G c)
    --             dot advances     ε-closure past a nullable prefix
    δ (⊕e Y G)  = ⊕e Y (δ ∘ G)      -- every live item advances, none dropped
    D = μ (δ ∘ F)                   -- the fixpoint is closure on nonterminals

— so `Derivative/*` really does supply LR's *states*.  What it does not supply
is everything else LR consists of.

* **No finiteness, so no automaton and no table.**  Nothing identifies `D* w`
  with `D* w'` when they denote the same language; `levOf` raises the universe
  level once per letter.  Dead items are never dropped either — `δ` emits
  `k (Dl c (literal d))` for `d ≠ c`, an empty grammar that nothing marks as
  empty — so the item set only ever grows.  "No automaton" and "no compaction"
  are the same gap, not two.
* **No determinism.**  With no table there is nothing to conflict, so ambiguous
  grammars are parsed into forests rather than rejected.  On power
  `Derivative/*` ⊋ LR; on mechanism it is Earley/GLR.
* **No lookahead.**  The `k` in LR(k) resolves reduce decisions.  This never
  decides.

So the two halves of LR are split across the tree and neither line has both.
`Ascent/*` has the commitment discipline — a stack, one live configuration,
`Predict.altDisjoint` as a machine-checked no-conflict certificate — but picks
its states by hand.  `Derivative/*` has the right states but no finiteness and
no determinism.  Actual LR would be: quotient the derivative states to a finite
set (that *is* the item-set construction), then impose `Ascent/*`'s no-conflict
condition on the result, with lookahead resolving the reduces.

## Internality

`Residual.agda`'s rule is that nothing downstream of it binds a model
element -- no matching on a splitting `(ms , e , _)`, no `↓M` in a
pattern.  The LR tree keeps it.  Terms that must match a splitting were
moved down to the tier that owns the connective:

| term                      | now lives in | as                        |
|---------------------------|--------------|---------------------------|
| `Ascent.⊗ε-unit-lM`       | `Residual`   | `⊗ε-unit-l`               |
| `Decidability.shiftD(⁻)`  | `Precise`    | `Dl-absorb`/`Dl-absorb⁻`  |
| `CodeDerivative.litSound` | `Precise`    | `Dl-lit-ε`                |
| `LeftCorner/*.toε` (×2)   | `KleeneStar` | `NIL-elim`                |

Three things in the tree still see elements, deliberately:

* algebra readouts (`algG`, the `br` clauses) -- these are the *semantic
  actions*, defined on a fold's branch, which is where they belong;
* h-level proofs (`λ m → isSetΠ …`), which are about the carrier;
* `Decidability.noStack`/`notThere`, which are metatheory -- a
  counterexample *about* the calculus, not a term in it.

## Corrections worth keeping

* **`Eq.transport` is not the problem; paths are.**  `Eq.transport C refl b =
  b` computes.  What blocks is `Eq.pathToEq`, which is `JPath` and does not
  reduce to `refl` even on `reflPath`.  `Strings.⊗-unit-l` builds its equation
  as a path and converts, so a parser built on it recognises but will not
  compute its *value*; `Residual.⊗ε-unit-l` matches the two `Eq` equations
  instead.  `Residual.agda`'s `castEq` comment claimed the opposite and has
  been corrected.
* An earlier note here blamed non-computation on residual-valued output.  That
  was wrong for the same reason — it was a path transport — and the claim has
  been removed rather than left standing.

## Open

* **Decidable ascent.**  Blocked as above.  The residual carries the value;
  the decision wants a positive carrier.  Whether one type can do both is
  untested.
* **No construction.**  Every grammar transform here is hand-written; nothing
  derives a table or a skeleton from a grammar.  That is the whole of
  "generator".
* **Soundness only, on the factored line.**  `toOriginal : S sE ⊢ E` is one
  direction; completeness needs `E ⊢ S sE`, which is the correctness of the
  left-corner transform.
* **One backend exercised.**  `Ascent/Base` is parametric over `AnswerFunctor` +
  `CovariantAnswer`, so `Maybe` and `ND` both should work, but only `Maybe`
  has been run.
