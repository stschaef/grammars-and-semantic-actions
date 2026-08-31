# `theory-core` review: internality, duplication, and a landing plan

Measured against `origin/main` @ `d744b57`, at `theory-core` @ `cc608ff`.
Every number below was computed from the tree, not estimated. Where a claim
comes from reading rather than from a script, it says so.

    85 commits, 239 files, +41,521 / −3

| area | files | lines |
|---|---|---|
| `src/Theory/` | 225 | 36,297 |
| `src/Cubical/` | 6 | 536 |
| `docs/` (generator + generated HTML) | 3 | 3,028 |
| `notes/` | 4 | 1,657 |
| `flake.lock` (ccl pin `b90862d` → `82334ff`) | 1 | 3 |

The branch is **purely additive**: `−3` lines total, all in `flake.lock`. It
is 0 commits behind `origin/main` and merges clean.

---

## 0. Build health — the one blocker

`make check` **fails, twice, at both parallelism settings**:

    agda: Heap exhausted;
    agda: Current maximum heap size is 17179869184 bytes (16384 MB).
    make: *** [Makefile:16: check] Error 251

* `-j8`, cold cache: died at 881/887 after 7m40s wall / 18m42s CPU.
* `-j4` (the CI setting), warm cache with only 8 modules left to check:
  died again, after 4m53s.

It is **one module**, and it is an 88-line demo. Measured individually with
`+RTS -s` against `-M16G`:

| module | max residency | total in use |
|---|---|---|
| **`Combinator/MachineDyck` (88 lines, this branch)** | **12.36 GB** | **16,632 MiB** |
| `Automaton/Implicit/Soundness` (1,214 lines, this branch) | 1.00 GB | 1,957 MiB |
| `Examples/RegexParser` (on `main`) | 0.45 GB | 539 MiB |
| `Automata/Implicit/RegExp/WeakEquivalences` (on `main`) | 0.35 GB | 551 MiB |

`MachineDyck` alone consumes the entire budget. It was started at 755/887 in
the `-j8` run and never finished; it was still unfinished in the `-j4` run.
`agda --build-library` is a single process, so a module holding 12 GB for
minutes while a hundred others typecheck around it is what tips the process
over.

Bisecting the file:

| checked through | max residency |
|---|---|
| `:40` `dyckParser = P.fix step` | 0.52 GB |
| `:48` `dyckByCut = R1.cut ∘⊢ (dyckParser ,& R1.initial)` | 0.54 GB |
| `:71` all definitions, **tests deleted** | 12.58 GB |
| whole file | 12.36 GB |

So it is **not** the six `Eq.refl` normalisation tests at the bottom —
deleting them changes nothing. The cost is in the definitions at `:50-66`,
and the prime suspect is the one-liner

    dyckByCut≡dyck : dyckByCut ≡ dyck
    dyckByCut≡dyck = refl

which asks the conversion checker to normalise two whole guarded-fixpoint
parsers against each other. It is a *decorative* proof — the header
describes it as showing "`runP` was already a cut" — and it costs more than
the rest of the library combined.

**Actions.** (a) Replace `dyckByCut≡dyck = refl` with a stated-but-not-
checked remark, or prove it structurally rather than by conversion. (b)
`MachineDyck` and `MachineDemo` are both orphans (no importer), so nothing
depends on the fix. (c) Independently: `src/Makefile:1` defaults to
`AGDA_FLAGS=-j10` while CI overrides to `-j4` — the default is the one
nobody tests; make them agree, and reconsider `-M16G` given GitHub runners
have 16 GB total.

The wider lesson for the tree: **280 definitions in `Theory/` are proved by
bare `refl`**. Most are cheap, but conversion-checking DSL terms is the one
operation here with no cost model, and there is no guard against another
`MachineDyck`. A CI step that reports per-module time or peak residency
would have caught this at the commit that introduced it.

Otherwise the tree is in good shape:

* 0 postulates in `src/Theory/` (the only one in the repo is
  `String/Unicode.agda`, pre-existing).
* 0 `REWRITE` pragmas anywhere — yet `src/grammar.agda-lib` enables
  `--rewriting` library-wide. That is a metatheoretic weakening bought for
  nothing; drop the flag.
* 8 `{-# TERMINATING #-}` pragmas — see §3.

---

## 1. Is it internal to the DSL?

**Mostly yes, and the generic layer is clean.** Three things check out:

* `Theory/Type/` and `Theory/Free/` mention `MonSig`, `MonEqns`,
  `Alphabet` or `String` **exactly zero times**. The only `Cubical.Data.List`
  imports in that layer (`Type/Later/Tabulated`, `Type/SemanticAction/Base`)
  are metalanguage lists — a table of positions, a list of test cases — not
  the free monoid. The genericity claim holds.
* `Theory/` imports nothing from the legacy `Grammar/`/`Automata/`/`Thompson/`
  tree, and nothing in the legacy tree imports `Theory/`. The two are
  disjoint, so this branch cannot break `main`.
* `Theory/Type/{Free,Combinator}` never import `Theory/Instances/` — no
  layering inversion at the generic/instance boundary.

The `⊗`-element destructuring pattern `(ms , Eq.refl , xs)` — the tell-tale
of writing a term by matching on a model element instead of composing
`⊗ᵘ-intro`/`⊗ᵘ-elim` — appears in only 24 files. Most are the designated
boundary (`Type/Operation/Base`, `Type/Residual/Base`, `Monoid/Strings`,
`Monoid/Residual`, `Monoid/Extension`) or test/demo leaves. The genuine
leaks are short and citable:

| site | what it does externally | should be |
|---|---|---|
| `Theory/Combinator/Core.agda:140,150` | `node-mk`/`node-elim` re-derive `⊗ᵘ-intro`/`⊗ᵘ-elim` by hand, at the *generic* layer | call `Type/Operation/Base` |
| `Monoid/KleeneStar.agda:112` | `readChars : ⊤Ty ⊢ char *` by recursion on `[]`/`c ∷ w` | `char *` is a proposition (`KleeneStar/Read`), so this is derivable, not definable-by-matching |
| `Monoid/Automaton/TokenStream.agda:107` | `char⁺-cons`, comment says "built rather than derived" | derive |
| `Monoid/Backreference/Base.agda:61,75` | `⊗ᴰ-assoc`/`⊗ᴰ-assoc⁻` by destructuring | see §2.1 — it is `Strings.⊗-assoc` copied |
| `Monoid/Lookahead/Base.agda:62` | `Λ-total` by recursion on the input | — |
| `Monoid/Regex/Sat.agda:44` | `sat⊗-precise` binds `m`, uses `L.cons-inj₂` | belongs in `Monoid/Precise` beside `lit⊗-precise`; the file already imports `Precise` |
| `Monoid/Combinator/Ascent/ShiftConverse.agda:268` | `litc-ends` by destructuring | — |

### The real internality problem is not leakage, it's that the boundary is undeclared

There is a substantial **metalanguage tier** — plain Agda over inductive
syntax, producing DSL terms at elaboration time — and it is documented in
prose but not in structure. Files with zero `⊢` occurrences and >150 lines:

    Regex/Parse                     285   POSIX source → RE, "explicitly not verified"
    Automaton/Implicit/Analysis     383   first/follow, RE → DetReg
    Automaton/Implicit/Compile      349   DetReg → implicit automaton
    Phase/Display                   323   pretty-printing by instance resolution
    Combinator/Decidable/STLC      2013   passes 1–3 are plain functions over Tree/ATm
    Regex/{Notation,Unicode}        223   surface syntax tables
    Instances/{STLC,Lambda}/…       ~380  signature/presentation definitions

Each of these has an honest header — `Regex/Parse` says outright "this is
the bootstrap and it is *not* verified" — but `Regex/Parse.agda` sits in the
same directory as `Regex/Derivative.agda`, which is a theorem, and CI treats
them identically. A reader has no structural signal.

**Recommendation.** Give the tier a name and a home: `Theory/Elaborate/…`
or a `Surface/` sibling per instance, so that "verified DSL term" and
"unverified metalanguage that produces one" are distinguishable without
reading the header. That is a rename, not a rewrite, and it makes the
internality property checkable by a grep in CI rather than by reviewer
discipline.

A second, smaller class: **properties proved by element induction rather
than internally**. `Automaton/Unambiguous` (131 lines, 0 `⊢`) and
`KleeneStar/Unambiguous` (157, 0 `⊢`) prove `isProp`-style facts by
matching on traces and splittings. Both headers explain why (a `Fin 2 →
String` splitting has no η, so a retraction's algebra squares need explicit
`PathP`s). That reason is sound; it is worth recording as a **gap in
`Type/Subgrammar`/`Type/Unambiguity`** rather than as a local choice,
because it will recur at every new inductive family.

---

## 2. Duplication

### 2.1 Verified byte-level duplicates

**`⊗ᴰ-assoc⁻` is `⊗-assoc⁻`.** `Backreference/Base.agda:72-81` and
`Strings.agda:149-158` have identical bodies *and* identical `where split`
clauses. `⊗ᴰ-assoc` differs only by one `castEq` on `c`. The file's own
comment at `:52` says so: "These are `⊗-assoc` of `Strings.agda` with the
`C` slot re-indexed; the splits are identical." It also proves
`⊗ᴰ-const : ⊗ᴰ A (λ _ _ → B) ≡ A ⊗ B` by `refl` (`:47`) — so `⊗ᴰ`
*generalises* `⊗` definitionally, and `Strings.⊗-assoc⁻` should be
`⊗ᴰ-assoc⁻` at the constant family. Net: delete two proofs, move `⊗ᴰ` down
beside `⊗`.

**`Decidable/ListLit` vs `Incomplete/ListLit`** — 78 lines, 5 changed hunks,
and 3 of those exist only because `Incomplete` spells out inferred types
where `Decidable` writes `_`. ~94% identical.

**`Decidable/Dyck` vs `Incomplete/Dyck`** — same shape; the shared parser is
already `Combinator/Grammars/Dyck` "written once for every answer", so only
the answer choice and the tests differ.

**`{Decidable,Incomplete,NonDet}/Star.agda`** — three 19-line files that are
character-identical except for one token (`DecAnswer` / `MaybeAnswer` /
`NDAnswer`). Each is just `Base public` + `Syntax public`.

**`Thompson/Construction/Literal` vs `Sat`** — 13 shared normalised 6-line
blocks. `literalNFA c` is `satNFA` at a decidable singleton.

### 2.2 The big one: two combinator libraries

There are **two independent `AnswerFunctor` records** and **two sets of
`{Dec,Maybe,ND}Answer` instances**:

| | generic | monoid |
|---|---|---|
| core | `Theory/Combinator/Core.agda:157` | `…/Monoid/Combinator/Core.agda:204` |
| instances | `Theory/Combinator/Answer/{Decidable,Incomplete,NonDet}` (295 lines) | `…/Monoid/Combinator/{Decidable,Incomplete,NonDet}/Base` (474 lines) |
| clients | 2 (`Instances/Lambda/Guard`, `Instances/Annotated/Guard`) + tests | ~56 files |

The split is **deliberate and well argued** — the generic `Core` header
explains that without a monoid there is no continuation passing, so
`Ans-lit`/`Ans-any`/`Ans-ε` collapse to a single `Ans-node`. But two fields
are literally identical (`ℓAns`, `Ans-⊕&`), `Ans` differs only in `s` vs
`tt`, and the relabelling field is the same concept spelled three ways
(`Ans-map&` generically; `Ans-≅` plus a separate `DivariantAnswer.Ans-dimap`
at the monoid). The generic header itself says the monoid's three token
rules *are* `Ans-node` at `_⊙_` and `ε·` under `Precise`.

**Recommendation.** Factor the part that mentions neither `⊗` nor
continuations — `ℓAns`, `Ans`, `Ans-⊕&`, one relabelling field — into a
single `Theory/Type/Answer/Base.agda`, and have both cores extend it. That
also deletes three of the six answer-instance modules. Do this *before* the
monoid combinator layer lands, or the duplication becomes API.

### 2.3 Boilerplate

* The 7-line generic-theory parameter preamble is repeated in **53** files;
  `open SortedSig` / `open SortedEqns` in **171**; the
  `(Alphabet)(isSetAlphabet)` preamble in **56**; the `(_≟_)` decidable
  alphabet preamble in **38**. Agda cannot abstract module parameters, so
  most of this is irreducible — but a `Theory/Type/Prelude.agda` and a
  `Monoid/Prelude.agda` that re-export the common opens would remove the
  `open`-wall half of it.
* `_≟T_` is declared in **10** files with the type spelled out inline, even
  though `Type/Decidable/Route.DiscreteEq` exists. `Decidable/STLC.agda:33-993`
  is a hand-written 31×31 decision table — 961 lines, 48% of that file,
  ~2.6% of the whole branch — derivable in ~4 lines from `Tok ≅ Fin 31` and
  `discreteFin`.
* `{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}` appears
  166 times, `-WnoUnsupportedIndexedMatch` alone 16 times,
  `--lossy-unification` alone 3 times. 43 of 225 files have neither — is
  that deliberate? Both belong in the `flags:` field of
  `src/grammar.agda-lib` (which already carries four flags), unless applying
  `--lossy-unification` to the legacy tree is a problem, in which case say so
  once in a README.

---

## 3. The one correctness item

Eight `{-# TERMINATING #-}` pragmas, on the initial-algebra recursor and its
uniqueness proof:

    Type/Inductive/Base.agda:41,51        rec, μ-η'
    Type/Inductive/HLevels.agda:154,169
    Type/Coinductive/Base.agda:44,54      corecHomo, ν-η'

`rec x m (roll ._ z) = α x m (map (F x) rec m z)` — the recursion *is*
structural, but it descends through `map (F x)`, which Agda cannot see
through. Every `μ`-based parser in the branch inherits the assertion.

Two mitigating facts, both worth stating rather than hiding: (a) four of the
eight are ported, not new — `Grammar/Inductive/{Indexed,HLevels}` on `main`
carry the identical pragmas at the identical definitions, so `Type/Inductive/*`
inherits existing debt; (b) the two in `Coinductive/Base` *are* new.

The repair is to fuse `rec` and `map` into a mutual definition recursing on
the `Functor` code, so the descent is visible. This deserves its own PR with
its own justification, because it is load-bearing for everything above it.

---

## 4. Structure and naming

**`Instances/Monoid/` conflates three tiers.** `Monoid/Base.agda` defines
`MonSig`/`MonEqns` — the *theory* of monoids, no alphabet, no strings.
`Monoid/Extension.agda` and `Monoid/GuardedSplit.agda` are generic over any
`MonSig`-shaped theory. Everything else is the free monoid on an alphabet.
The proof: `Instances/Bags/*` — a *commutative* monoid, not the free one —
imports `Monoid.Base`, `Monoid.Extension` and `Monoid.GuardedSplit`, in 7
files. Suggested split:

    Theory/Theories/Monoid/{Signature,Extension,GuardedSplit}   -- signature tier
    Theory/Instances/Strings/…                                  -- free monoid on Alphabet
    Theory/Instances/Bags/…                                     -- commutative extension

**`Examples` and `Grammars` are backwards.** `Monoid/Examples.agda` holds
the alphabet-*generic* library (`LiteralStar`, `dyckBranch`, `DyckCode`);
`Monoid/Grammars/Dyck.agda` — its only importer — holds the concrete
instantiation. Rename so the reusable one is not called "Examples".

**Layer inversion at regex.** `Regex/Base.agda:26` opens
`Combinator/Decidable/Star … public`, and `Regex/Sat.agda:33` opens
`Combinator/Decidable/Base … public`. So the regex *datatype* re-exports an
entire parser backend, and a client who wants only `RE` gets the Dec
combinator library. Same re-export-wall pattern as `Monoid/Types.agda`.

**Five test-suffix conventions**: `Tests.agda` (13), `Examples.agda` (10),
`Demo.agda` (4), `StressTests.agda`, `ScratchPerf.agda` — plus the
in-name variants (`GuardedTests.agda`, `GreedyExamples.agda`,
`RegExpExamples.agda`) alongside the in-directory ones. And
`Combinator/Grammars/` has `Arith`+`ArithGrammar`+`ArithTests` next to
`Polynomial`+`PolyGrammar`+`PolynomialTests` — the same three-file split
under two different names, with a fourth `Arith` in `Combinator/Decidable/`.

**Leftovers.**
* `Combinator/Scratch/{ResidualParser,Wall}` — 385 lines, a closed
  two-file cluster with no external importer, named "Scratch".
* `Automaton/ScratchPerf.agda` (63 lines) — a perf scratchpad in the build.
* 8 files ship `-- TODO how much of this actually used?` as their **first
  line** (`Type/Monad/Base`, `Type/Code/Container`, `Type/Decidable/Base`,
  `Type/Later/{Derivative,Tabulated,Lex,Poset,Indexed}`). The existing
  `notes/theory-core-cleanup.md` §3 answers all eight; the answers should
  replace the headers.
* The same 4-line `WARNING for now I have been treating this as a place to
  sequester…` banner is copy-pasted into 5 `Type/Later/*` files.
* 61 `Theory/` modules have zero importers (9,573 lines). Most are
  legitimate build roots (`*Tests`, `*Examples`, `*Demo`). The ones that are
  not obviously roots and deserve a decision: `Decidable/STLC` (2,013),
  `Determinization/WeakEquivalence` (496), `Decidable/Arrow` (328),
  `Phase/Display` (323), `Ascent/{Expr,ShiftConverse}` (604),
  `LeftCorner/{Expr,Defer,LeftRec}` (581), `Derivative/OneStep` (187),
  `Thompson/Equivalence` (82 — the *theorem* the 1,521-line
  `Construction/*` builds toward, and nothing consumes it).

**Nearly half the generic layer is not load-bearing.** For every top-level
name exported by `Theory/{Type,Free,Combinator}/`, I checked whether it is
mentioned *textually anywhere* in another `Theory/` file — a deliberately
generous test, since a mention in a comment counts. Result: **317 of 728
exported names (44%) never appear outside their defining module.** Worst
offenders:

| module | defs | never used elsewhere |
|---|---|---|
| `Type/Unambiguity/Disjoint` | 23 | 21 (91%) |
| `Type/Residual/Base` | 27 | 24 (89%) |
| `Type/PropositionalTruncation/Base` | 13 | 11 (85%) |
| `Type/Coinductive/Base` | 15 | 12 (80%) |
| `Type/Inductive/HLevels` | 17 | 13 (76%) |
| `Type/Top/Properties` | 16 | 12 (75%) |
| `Type/Subgrammar/Base` | 25 | 15 (60%) |
| `Type/Guarded/Justification` | 27 | 15 (56%) |
| `Type/{Category, Distributivity, Subgrammar/Equalizer}` | 4/4/6 | all of them |

Some of this is deliberate — a connective library states its full API before
anything uses it — but 44% is high enough that the layer should be triaged
before it becomes `main`'s public surface. `Type/Category` has no importer
at all (42 lines); `Type/Distributivity` is opened `public` by
`Strings.agda:51` but not one of its four names is referenced anywhere.
`Type/Guarded/Justification` is 320 lines of which six names are used
(`löbMemo`, `löbFrom`, `löbMemo≡löbFrom`, `löbBySuffix`, `löbByMeasure`,
`decSuffix`); `hylosFromGuard`, `löbByLex`, `löbByFuel`, `löbF`, `mapG`,
`uniqAux`, `unf`, `nextF`, `▷F`, `isSetFn` and five more are dead.

**`docs/combinators.html` is a generated artifact, and it is already
stale.** Re-running `docs/build.sh` on the branch tip produces an 80-line
diff against the committed file. CI runs only `make -C src check`, so
nothing catches the drift. Either gitignore it and publish from CI, or add
a CI step that regenerates and fails on diff. As committed it is 2,482
lines that embed source files verbatim — double maintenance.

---

## 5. Landing plan: ten PRs, verified independent

Each layer's full import closure was computed. With **three file
reassignments** — `Greedy/Base` into C, `Machine{Demo,Dyck}` into H,
`KleeneStar/GuardedTests` into D — every layer's closure lies inside itself
and its predecessors, so each PR typechecks standalone under
`agda --build-library`. **Zero forward dependencies.** No code motion
beyond those three files is needed to land the branch in this order.

| PR | contents | files | lines |
|---|---|---|---|
| **A** | `src/Cubical/*` — `Algebra/Theory/Finitary{,/Free/Closing,/Free/ClosingElim}`, `Data/{FinData/More,Nat/WFOrder}`, `WildCat/LocallySmall/Base` | 6 new | 536 |
| **B** | `Theory/{Base,Free/,Type/}` — the theory-generic DSL | 50 | 5,296 |
| **C** | `Monoid/{Base,Extension,GuardedSplit,ListPresentation,Strings,Types,Precise,Unitor,Convolution,Residual,Suffix,KleeneStar,Derivative,SemanticAction,Lookahead,SequentialUnambiguity,Greedy/Base,Grammars,Examples,Unicode}` | 31 | ~4,958 |
| **D** | `Theory/Combinator/*` + `Monoid/Combinator/{Core,Syntax,Machine,Grammars/Regex,{Dec,Inc,ND}/{Base,Star}}` | 14 | ~1,936 |
| **E** | `Monoid/{Regex/*,Lex/*,Greedy/Examples}` | 13 | ~1,944 |
| **F** | `Monoid/{Automaton/*,Automata/*,Phase}` | 28 | 6,209 |
| **G** | `Monoid/{Thompson/*,Determinization/*}` | 11 | 2,527 |
| **H** | `Monoid/Combinator/{Decidable,Incomplete,Ascent,LeftCorner,Derivative,Grammars,Scratch}` — the LL work | 46 | 9,110 |
| **I** | `Instances/{Bags,Lambda,STLC,Annotated}` | 23 | 2,914 |
| **J** | `Monoid/{Backreference,Phase/Display,Pipeline}` | 8 | 1,351 |

A–D (≈12.7k lines) is the reviewable core and the part worth real scrutiny.
E–G is the parsing/automata story. H–J are applications and can land last
or not at all.

### Ordering notes

* **A is upstream work, not repo work.** `Cubical/Algebra/Theory/Finitary`
  has 83 importers on this branch — it is the foundation of the whole
  design — and `WildCat/LocallySmall/Base.agda:1` still says
  `TODO put in ccl`. This branch already bumps the ccl pin. Landing these
  in `cubical-categorical-logic` first and importing them would shrink PR A
  to nothing and remove the biggest "why is this vendored?" question a
  reviewer will have.
* **Do §2.2 (unify `AnswerFunctor`) between B and D**, not after. Once the
  monoid combinator layer is on `main` with its own record, the duplication
  is public API.
* **Do §3 (`TERMINATING`) inside B**, as its own commit, so the fix is
  reviewable against the `Inductive/Base` diff rather than buried.
* **Split G's decision out.** `notes/theory-port-audit.md` §6 argues that
  Thompson's `Construction/*` (2,000+ lines here) is dead under the
  derivative route, and `Thompson/Equivalence` has no importer. Decide
  whether the goal is *parsing* (drop G) or *finite-state theory* (keep it,
  restate against `DerivAutomaton`) before opening the PR — not during
  review.
* **`docs/` and `notes/` are their own PR**, orthogonal to all ten, and
  should carry the gitignore/CI-regeneration decision for `combinators.html`.

### Cheap wins to fold into whichever PR carries the file

1. Delete `--rewriting` from `src/grammar.agda-lib` (0 uses).
2. Move `--lossy-unification -WnoUnsupportedIndexedMatch` into the `.agda-lib`
   flags; delete 185 pragma lines.
3. Replace the 8 TODO-as-header lines with the answers already in
   `notes/theory-core-cleanup.md` §3.
4. One `Later/README` instead of the banner in 5 `Type/Later/*` files.
5. Delete `Combinator/Scratch/*` (385 lines, closed cluster) and
   `Automaton/ScratchPerf` (63).
6. Collapse `{Dec,Inc,ND}/Star.agda` into one parameterised module.
7. Move `Regex/Sat.sat⊗-precise` into `Monoid/Precise`.
8. Derive `Decidable/STLC`'s `_≟T_` from `Fin 31` (−961 lines).
9. Make `{Decidable,Incomplete}/{Dyck,ListLit}` one module parameterised by
   the answer (−~130 lines).
10. Stop `Regex/{Base,Sat}` re-exporting the Dec combinator stack `public`.

---

## 6. Fixes applied

Everything below was typechecked. Where a fix was attempted and abandoned,
the measurement that killed it is recorded — two of §1–§2's findings did not
survive contact.

### Landed

| what | where | effect |
|---|---|---|
| **Build blocker.** `dyckByCut≡dyck = refl` disabled, with a FIXME giving the numbers and what a real proof would need | `Combinator/MachineDyck` | 12.36 GB / never finished → **535 MB / 2.97 s** |
| **Three precision proofs → one.** `lit⊗-precise`, `char⊗-precise` and `sat⊗-precise` were the same argument at three maps into `char`; factored as `tok⊗-precise` | `Monoid/Precise` | −24 lines; `Regex/Sat` drops to **zero** model-element bindings |
| **`sat⊗-precise` rehomed** from `Regex/Sat` to `Precise`, beside its two siblings | `Monoid/{Precise,Regex/Sat}` | the leak in §1's table, closed |
| **`DiscreteEq` rehomed.** It was declared in `Type/Decidable/Route` — nothing to do with routing — and the bridge to `isSet` was written **five** times, twice unavoidably (`Monoid/Types` and `Decidable/Productions` are imported *by* the module holding the shared copy). Neither notion mentions a theory, so both now live parameter-free | new `Cubical/Relation/Nullary/DiscreteEq` | 5 copies → 1 |
| **Dependent tensor rehomed** to `Strings`, beside the `_⊗_` it generalises | `Strings`, `Backreference/Base` | `Backreference/Base` 159 → 135 lines |
| **`readChars` is now internal.** Was a second recursion on the word, duplicating `Strings.read`; now a fold over `String*` composed with `read`. `starBranch char b` and `kleeneBranch b` are the same functor at each `b` — only the two `Bool → Functor` functions differ, which is why they never unified | `Monoid/KleeneStar` | one recursion on a word, not two |
| **`ListLit` written once.** The grammar was duplicated to pick two answers; migrated to the `Grammars/Dyck` arrangement the codebase already had | new `Grammars/ListLit`, `Combinator/Grammars/ListLit`, two leaves | 161 → 115 lines, grammar and token table each written once |
| **`SetTheoryTy`** was `TheorySet` character for character, in a module already importing HLevels | `Type/Category` | 1 copy removed |

### Attempted, measured, reverted — and why

**`Combinator/Core`'s `node-mk`/`node-elim` are not a leak.** §1 listed them as
re-deriving `⊗ᵘ-intro`/`⊗ᵘ-elim` by hand. They cannot: `NodeArgs` lets the
slots depend on the splitting `ms` and `⊗ᵘ`'s do not, so `⊗ᴰ` is a strict
generalisation and this is its connective-introduction boundary — the same
licence `Operation/Base` takes. Unifying them would mean moving the dependent
tensor into `Operation/Base`, which is blocked today: `⊗ᴰ` is `TheorySet`-valued
and `Type/HLevels` already imports `Operation/Base` (`HLevels.agda:35`), so the
dependency inverts. The boundary is now stated in the file instead.

**The `⊗ᴰ-assoc⁻` / `⊗-assoc⁻` duplication is only half-removable.** The bodies
really are identical, `where` clause included, and `⊗ᴰ-const` really is `refl` —
but defining `⊗-assoc⁻ = ⊗ᴰ-assoc⁻ {B = λ _ → B} {C = λ _ → C}` makes it stop
reducing when passed *unapplied*, which the pentagon does (`⊗-map ⊗-assoc⁻ id⊢`):
the families become metas nothing solves, so the general lemma never gets to
match, and the pentagon fails with unsolved constraints. Eta-expanding does not
help. The general lemma now lives next to the specific one in `Strings` with
that reason recorded; the two bodies stay.

**The 961-line STLC table is load-bearing, not duplication.** §2.3 called it
derivable and put it at ~2.4% of the branch. Deriving it —
`sectionDiscrete uncode code uncode-code discreteℕ`, 125 lines including a
`code`, a list-based `uncode` (numeral patterns are refused past 20) and 31
`refl`s — typechecks the *definition*, but `sectionDiscrete`'s `yes` branch
builds `sym (sect x) ∙∙ cong f p ∙∙ sect y`, a path composition **per token
comparison**. The parser dispatches on `_≟T_` at every step and the tests
normalise it, so the module went from checking in the ordinary build to 6 GB
resident and still climbing after five minutes; it was killed, not finished.
The table stays, and the file now says why. A cheaper derivation would have to
reduce to `inl Eq.refl` / `inr _` in one step — deciding on `code a ≡ᵇ code b`
and rebuilding the `Eq.≡` directly — rather than going through `Discrete`.

### Not attempted

`char⁺-cons` (`Automaton/TokenStream:107`), `Λ-total` (`Lookahead/Base:62`) and
`litc-ends` (`Ascent/ShiftConverse:268`) still build an element by hand. All
three *construct* rather than destructure, and all three are indexed by
metalanguage data, so they are weaker instances of the pattern than the ones
above; they want `⊗-intro` rather than a raw tuple.

The `AnswerFunctor` unification (§2.2) is untouched: it is a design change
across two combinator libraries with ~56 dependent files, not a cleanup, and it
should land as its own PR between B and D of §5.
