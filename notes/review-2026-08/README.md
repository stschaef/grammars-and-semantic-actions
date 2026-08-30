# Review response, 2026-08-28

Answers to `review.md`, plus a nine-way parallel audit of the whole tree.
The per-area reports in this directory are the evidence; this file is the
index and the summary of what changed.

## What was changed in the tree

| Item | Where | Status |
|---|---|---|
| `satG` → `satTy` | `Monoid/Sat.agda` + 11 files | done |
| Restored the `OPTIONS` pragma a comment sweep had deleted | `Monoid/Sat.agda:1` | done |
| Restored the `OPTIONS` pragma a comment block had swallowed | `Automaton/GreedyExamples.agda:1` | done |
| General dependent eliminator for the closing HIT; `elimProp` derived from it | `Finitary/Free/ClosingElim.agda` | done |
| `rejects` and `accepts` added to the test interface | `Type/SemanticAction/Suite.agda` | done |
| Test harness split out of the theory-parameterised core | `Type/SemanticAction/Suite.agda` (new) | done |
| `semact-sat`: the one non-DSL clause of the lexer readback, made internal | `Monoid/Sat.agda`, `Lex/Regex.agda`, `Regex/UnicodeTests.agda` | done |
| `DiscreteEq` / `decEqRetract` / `decEqEnum` / `decℕEq` / `dec⊎Eq` extracted | `Type/Decidable/DiscreteEq.agda` (new) | done |
| 962 lines of hand-written token equality replaced by an enumeration retract | `Decidable/STLC.agda` | done |
| STLC definitions split from STLC tests | `Decidable/STLC.agda`, `Decidable/STLCTests.agda` (new) | done |
| Unicode-lexed, four-phase STLC front end | `Pipeline/STLC.agda` (new) | done |
| Readable end-to-end STLC suite in the target skeleton | `Pipeline/STLCTests.agda` (new) | done |
| `accepts`/`rejects` test names that shadowed the harness renamed | both `ListLit.agda`, `Implicit/{Analysis,RegExp}Examples.agda` (→ `endsAccepting`) | done |
| `∉First-⊕ᴰ`: raw λ over the model → `⊕ᴰ-elim h ∘⊢ &⊕ᴰ-distR` | `SequentialUnambiguity/First.agda:70` | done |
| `STEP-branch`: raw λ over the model → the file's own `step-in` | `Automaton/Deterministic.agda:122` | done |

### Round two

| Item | Where | Status |
|---|---|---|
| 308-entry AI-slop comment sweep, five agents over disjoint file sets | 135 files | done |
| ~130 `go`/`go2`/`go3`/`go4`/`helper` local helpers given semantic names | 28 files | done |
| Why the library uses `Eq.≡` and not `_≡_`, written down for the first time | `Theory/Base.agda` | done |
| A comment at each of the six `{-# TERMINATING #-}` sites saying why it is safe | `Type/{Inductive,Coinductive}/**` | done |
| Two provably stale comments deleted (documented code that no longer exists) | `Bags/Order.agda`, `Bags/Rank.agda` | done |
| `subgrammar` → `subTy`, `Subgrammar` → `SubTy`, `Type/Subgrammar/` → `Type/Subtype/` | 3 files | done |
| `Phase.Gr` → `Phase.Ty` | `Phase.agda` + 3 call sites | done |
| `Suite.Case` → `Suite.Row` (it is an (actual, expected) pair, not a case) | `SemanticAction/Suite.agda` | done |
| `…R` → `…r` across the regex layer, 21 names | `Regex/Unicode.agda` | done |
| Half-finished refactor removed: a helper ignoring both its arguments | `Regex/Parse.agda` | done |
| Tests moved out of 9 definitions files into sibling `*Tests.agda` | `Combinator/**`, `Pipeline/Dyck`, `Phase/Display` | done |
| `showDyck`/`report`/`check` display action, so Dyck tests compare text | `Pipeline/Dyck.agda` | done |
| Quicksort tests converted to three named `passes` suites | `Bags/Quicksort/Tests.agda` | done |
| Binary distribution law `⊗ₑ⊕-dist` added; `Partition`'s `Bool`-indexed family removed | `Monoid/Extension.agda`, `Bags/Partition.agda` | done |
| Stress-test infrastructure: generators, a suite, and a `make stress` target | `Monoid/Stress/**`, `src/Makefile` | done |
| README build instructions fixed (they named a file and a target that do not exist) | `README.md` | done |

### Round three — Bags made internal to the DSL

| Item | Where | Status |
|---|---|---|
| `recSeqg`: `Seq`'s recursor by guarded recursion (`löb`), replacing the `TERMINATING` `rec` | `Bags/Sequence/Fold.agda` (new) | done |
| `recSortedg` / `elementsg`: the same for `Sorted` | `Bags/Sorted/Fold.agda` (new) | done |
| `partSeq` moved onto `recSeqg`; `isSetHalves` supplied as the motive's set-ness | `Bags/Partition.agda` | done |
| The `View` machinery deleted; `Generation` rewritten to produce arrangements | `Bags/Generation.agda` | done |
| `arrange` + `sortBag : (m : Bag) → ∥ Sorted m ∥₁` — the bridge finding 3 named as missing | `Bags/Quicksort/Base.agda:66` | done |
| `appendSeq` / `_++ᵍ_`, and a `concatenation` suite for it | `Bags/Sequence/Fold.agda` | done |
| **`appendSeq`'s nil case did not compute** — `⊎B-unitL` is `subst` at a μ payload (pitfall 1). Fixed by `unitLSeq`, which pushes the ε down to the leaf | `Bags/Sequence/Fold.agda:55` | done |

The last one is worth its own line, because it is the failure mode the
`Quicksort/Tests` header warns about, reintroduced by the very change that
removed the pragmas. `⊎B-unitL` is `subst A path a`; at `A = Seq` the index
lives in the free model, so the transported arrangement goes neutral and no
fold over it fires. It is data-dependent — an empty right half transports
fine — so `(3) ++ nil` passed and `nil ++ (3)` did not terminate. The
remedy is `Join.nilJ`'s: keep the ε a code and push it to the leaf, where
`⊎B-unitL⌈⌉` is a path in `Bag` rather than a transport. The arrangement is
rebuilt cons by cons instead of moved, which costs a traversal and computes.
`Quicksort/Tests.agda` checks in 28s; before the fix it did not finish.

Net across both rounds: **~3900 lines deleted, ~1500 added**, plus 15 new files.
`agda --build-library` is green over the whole tree after every change.

## Answers to the specific questions in `review.md`

**"we should be able to include an elim that doesn't presuppose a prop,
right?"** — Yes, and the right generality is a **set**-valued motive:
`FreeModel` is set-truncated by `trunc`, so `isSet (P m)` is exactly the
hypothesis the `trunc` clause needs and nothing weaker will do. At a set
motive none of the three path constructors is automatic, so `elim` takes
six methods: `pvar`, `pnode`, `pclo`, and one `PathP` per path
constructor (`pcloVar`, `pcloNode`, `peqn`). `elimProp` is now three lines
on top of it. Not yet done: `Closing.rec` is `elim` at a constant motive
(`pcloVar`/`pcloNode` are `refl`, since `TmRec` computes on `var`/`node`;
`peqn` is `sat`) and `recUniq` is `elimProp` at `P m = f _ m ≡ rec ρ m`;
deriving them would delete ~22 lines and leave one eliminator with three
corollaries. `FreePresentation` has no `elim` field, so the eliminator is
unreachable through the presentation abstraction — `Bags/Order.agda:143`
has to import `ClosingElim` directly.

**"the uniform testing interface `passes` and `rejects` … does this
exist?"** — `passes`, `_at_`, `_↦_` existed; `rejects` did **not**. Both
`rejects` and `accepts` are now in `Suite`, which has also been moved out
of the theory-parameterised `SemanticAction/Base.agda` into its own
theory-independent module, so a test file imports one copy rather than an
instantiation.

**"Check that these test case helpers aren't duplicated"** — they are.
Five hand-rolled regex harnesses (`Regex/Tests`, `Regex/UnicodeTests`,
`Regex/ParseTests`, `Backreference/RegexTests`, `Backreference/Stress/Common`),
`ℓr` in 8 copies, `rep`/`repText` in 8, a two-letter `UChar` sub-alphabet in
6, a finite-token `_≟_` in 8. See `tests.md` §C.

## The headline findings

1. **The old tree is 37% of the codebase and is dead.** 169 files, 18,871
   lines, **zero** imports crossing to or from `src/Theory`, yet
   `agda --build-library` typechecks all of it: ~40% of every build, and
   44% of the interface cache. It also owns the repo's only `postulate`
   and only `NO_POSITIVITY_CHECK`. Blocked on porting 457 lines
   (`Automata/Turing/**`, `String/ASCII/**`, `String/SubAlphabet`) and a
   README rewrite. — `architecture.md`
2. **`quicksort` evaluated through a `{-# TERMINATING #-}` recursor**, via
   `partSeq`/`recSeq` and `elements`/`recSorted`, while three separate file
   headers framed the design around avoiding that pragma. *Fixed in round
   three*: `recSeqg`/`recSortedg` are guarded (`löb`) folds in the shape of
   `KleeneStar/Guarded.agda:105` `fold*g`, and the Bags path now asserts no
   termination. — `bags.md`
3. **`Bags/Generation.agda` — the `View` machinery — was entirely dead.**
   90 lines, zero importers; quicksort consumed `Seq` and never touched it,
   so there was no `(m : Bag) → ∥ Seq m ∥₁` bridge and `quicksort` sorted
   *arrangements*, not bags. *Fixed in round three*: `View` is gone,
   `Generation` produces arrangements, and `Quicksort/Base.agda:66`
   `sortBag : (m : Bag) → ∥ Sorted m ∥₁` is the bridge. — `bags.md`
4. **`--lossy-unification` is in 137 of 371 files, all of them in
   `src/Theory`**, and the boundary is exactly `Monoid/Types.agda`, where
   the generic theory modules get applied and opened `public` twelve times.
   Fixing it there would clear 113 files at once. — `architecture.md`
5. **The sequential-unambiguity subsystem is complete and unused.** ~300 of
   434 lines of `SequentialUnambiguity/Base.agda` have no consumer; the
   automaton side (`Soundness.agda:1159`) proves the same closure. Worse,
   `unambiguous` means *subterminal* in the old tree and *element-level
   `isProp`* in the new one, and both are live. — `ambiguity.md`
6. **`Automaton/Greedy` is superseded by `GreedyMax` in every respect** —
   both files' own headers say so — and ~60 lines are duplicated verbatim
   between them, and again between `Unambiguous.agda` and `GreedyMax.agda`.
   — `automata.md`
7. **`src/Lex/Det/Base.agda` carries `--allow-unsolved-metas`**, the only
   such pragma in the repo, and `--build-library` goes green over its
   holes. — `regex-lex-thompson.md`
8. **308 comments to delete, 117 `go`-class helpers to rename, 31
   vocabulary renames** (`Phase.Gr` → `Ty`, `subgrammar` → `subTy` in 14
   sites, `ℓG` → `ℓK` in ~40, `Type/Subgrammar/` → `Type/Subtype/`), and 14
   actively misleading names — `Combinator/Grammars/` holds mostly parsers;
   `Type/Later/Lex` is *lexicographic* while `Monoid/Lex` is *lexer*.
   — `comments-naming.md`
9. **`Lean/` is 1.5 GB, untracked and unignored**, containing only `.lake/`
   build output with no lakefile, toolchain, or sources. — `architecture.md`

## The reports

| File | Covers |
|---|---|
| `architecture.md` | old tree vs new, file sizes, build health, module organisation, repo hygiene |
| `automata.md` | `Automata/**`, `Automaton/**`, determinisation |
| `bags.md` | the six Bags complaints, answered one by one |
| `combinators-ll-routed.md` | `Combinator/**`, LL/Routed, `Decidable/Route` |
| `regex-lex-thompson.md` | regex, lexing, Thompson, backreferences |
| `ambiguity.md` | unambiguity, disjointness, First/FollowLast, `Precise` |
| `theory-core.md` | `Theory/Type/**`, connective API coherence, `ClosingElim` |
| `tests.md` | census of all 37 test-bearing files, migration plan |
| `comments-naming.md` | the comment deletion list, the rename list |

## Still open — deliberately not done

These are all evidenced in the reports; each is a decision rather than a
mechanical fix, so none was taken unilaterally.

1. **Delete the old tree** (`src/Grammar`, `src/Automata`, `src/Thompson`,
   `src/Lex`, `src/Determinization`, `src/Parser`, `src/Term`, `src/String`,
   `src/Examples`) — 18,850 lines, ~40% of every build, zero imports crossing
   either way. Blocked on porting 457 lines (`Automata/Turing/**`,
   `String/ASCII/**`, `String/SubAlphabet`). Tag the repo first; it has no
   git tags.
2. **Delete `Automaton/Greedy.agda`** — superseded by `GreedyMax` in every
   respect, per both files' own headers, with ~60 duplicated lines.
   `GreedyExamples.agda` goes with it.
3. **Fix `--lossy-unification` at `Monoid/Types.agda`** rather than in 140
   copy-pasted pragmas.
4. **Decide between the two unambiguity developments** — ~300 lines of
   `SequentialUnambiguity/Base.agda` have no consumer because the automaton
   side proves the same closure; and `unambiguous` means two different
   things in the two trees.
5. **Stop re-exporting `Suite` from `SemanticAction/Base.agda`.** The
   `public` there is why a test file that also imports `Suite` directly gets
   an ambiguity (hit once in `Phase/DisplayTests.agda`), and why
   `Monoid/Types.agda` needs `hiding (at)`.
6. **`Lean/`** — 1.5 GB, untracked and unignored, containing only `.lake/`
   build output with no sources.
7. **`src/Lex/Det/Base.agda` carries `--allow-unsolved-metas`**, the only
   such pragma in the repo; `--build-library` goes green over its holes.
8. **Raise the stress suites' size numerals.** `make stress` now prints a
   baseline first: at their current sizes all three suites cost less than
   the ~13s of interface loading, so they do not yet measure anything.
