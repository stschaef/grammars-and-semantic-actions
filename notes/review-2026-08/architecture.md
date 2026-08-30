# Architecture & hygiene review — `grammars-and-semantic-actions`

Branch `theory-core` @ `bc4d6a4`. All measurements taken by `find`/`grep`/`wc`
on `2026-08-28`; `src/_build/**` excluded everywhere. No `agda` was run.

## 0. Baseline numbers

| scope | files | lines |
|---|---:|---:|
| `src/**/*.agda` (excl. `_build`) | 371 | 50,741 |
| OLD tree (see §1) | **169** | **18,871** |
| NEW tree (`src/Theory/**` + `src/Cubical/**`) | 202 | 31,870 |

NEW tree breakdown:

| dir | files | lines |
|---|---:|---:|
| `src/Theory/Type` | 46 | 4,877 |
| `src/Theory/Instances/Monoid` | 126 | 23,689 |
| `src/Theory/Instances/Bags` | 11 | 1,024 |
| `src/Theory/Instances/Lambda` | 3 | 302 |
| `src/Theory/Instances/STLC` | 1 | 167 |
| `src/Theory/Free` | 3 | 223 |
| `src/Cubical` | 11 | 1,477 |

OLD tree breakdown (`src/Grammar` 10,441 · `src/Examples` 2,634 · `src/Automata`
2,417 · `src/Thompson` 1,666 · `src/String` 648 · `src/Determinization` 490 ·
`src/Lex` 217 · `src/Term` 205 · `src/Parser` 132 · the three top-level
`src/{Grammar,Parser,Term}.agda` 21).

---

## 1. The two generations

### 1.1 Reachability: the trees are completely disjoint

```
grep -rnE '^\s*(open\s+)?import\s+(Grammar|Automata|Thompson|Lex|Determinization|Parser|Term|String|Examples)\b' src/Theory src/Cubical
  → 0 hits
grep -rnE 'import\s+(Theory|Cubical\.Algebra\.Theory)' src/{Grammar,Automata,Thompson,Lex,Determinization,Parser,Term,String,Examples} src/*.agda
  → 0 hits
```

Nothing in the new tree imports the old tree; nothing in the old tree imports the
new tree. There is no shared module, no adapter, no bridging file. The only
name collisions are coincidental (`Theory/Instances/Monoid/Thompson/…` shares a
leaf name with `src/Thompson/…` but is a distinct module path).

`src/Grammar.agda`, `src/Parser.agda`, `src/Term.agda` (21 lines total) are
`open import … public` façades over the old tree only.

### 1.2 …but the old tree is fully typechecked on every build

`src/grammar.agda-lib`:

```
name: grammar
include: .
depend: cubical cubical-categorical-logic
flags: --cubical --guardedness --guarded --rewriting
```

`src/Makefile:19` — `check: $(AGDA) --build-library`. `--build-library`
typechecks **every** `.agda` file reachable from the library's `include: .`,
i.e. all 371 files. There is no `Everything.agda` allowlist and no per-target
filtering, so the 169 old-tree files are typechecked by `make check`, by
`nix build` (`flake.nix:50` — `buildPhase = "make check"`), and by CI
(`.github/workflows/main.yml`, last step `make -C src check`).

**Cost, measured.** Interface bytes in `src/_build/2.9.0/agda/`:

| tree | `.agdai` bytes | share |
|---|---:|---:|
| old tree (Grammar/Automata/Examples/Thompson/String/Determinization/Lex/Parser/Term + 3 façades) | 25,307,618 | **44.3 %** |
| `Theory` + `Cubical` | 31,860,333 | 55.7 % |
| total | 57,167,951 | |

The old tree is 37.2 % of the source lines but 44.3 % of the elaborated
interface bytes — i.e. it is *denser* than average, and a conservative reading
is that it accounts for **~40 % of a full `make check`**. (I could not time the
build directly; all old-tree `.agdai` share a 48-second mtime window
2026-08-27 17:15:48–17:16:36, which is a cache restore, not an elaboration.)

Two corroborating facts:

* `src/_build/` also holds a **2.9 MB `2.7.0.1/` generation** whose newest
  `.agdai` is dated 2025-04-27 — a stale interface directory for an Agda
  version the flake no longer pins. Pure garbage.
* **103 of the 202 new-tree files have no `.agdai` at all** (list in §4.6),
  while **0 of the 169 old-tree files** are missing one. The cache is dominated
  by a tree nobody imports and is stale for half the tree under active
  development.

### 1.3 Correspondence table

The repo already contains two hand-written port notes —
`notes/theory-port-audit.md` (241 lines, written at `b97897d`) and
`notes/theory-port-status.md` (227 lines). Both are now **partially stale**:
`theory-port-audit.md` §3–§6 lists `Subgrammar`, `PropositionalTruncation`,
`SequentialUnambiguity`, NFA/DFA, Thompson and `Determinization` as unported,
but all of them have since landed (they are in the file listing, and
`theory-port-status.md` records them). What follows is verified against the
files that exist today.

| OLD | NEW | status |
|---|---|---|
| `Grammar.agda`, `Grammar/Base`, `Grammar/Core`, `Term/{Base,Category,Nullary}`, `Term.agda` | `Theory/Base` (`TheoryTy`, `_⊢_`, `THEORYTY`), `Theory/Type/Category` | superseded |
| `Grammar/Equivalence{,/Base}` | `Theory/Type/Equivalence/Base` + `Theory/Base._≅_` | superseded |
| `Grammar/Top{,/Base,/Properties}`, `Grammar/Bottom/*` | `Theory/Type/Top/{Base,Properties}`, `Theory/Type/Bottom/Base` | superseded |
| `Grammar/Sum/*` (10 files), `Grammar/Product/*` (7 files) | `Theory/Type/Sum/{Base,Binary/Base}`, `Theory/Type/Product/{Base,Binary/Base}` | superseded; the `AsPrimitive`/`AsIndexed` split was deliberately collapsed |
| `Grammar/Function/*`, `Grammar/BinopsAs{Primitive,Indexed}` | `Theory/Type/Function/Base` | superseded |
| `Grammar/Lift/*`, `Grammar/HLevels/*`, `Grammar/Distributivity` | `Theory/Type/Lift/Base`, `Theory/Type/HLevels`, `Theory/Type/Distributivity` | superseded |
| `Grammar/Equalizer{,/Base}` | `Theory/Type/Equalizer/Base` | superseded |
| `Grammar/Inductive/{Indexed,Functor,HLevels,Properties}` | `Theory/Type/Code/{Base,Container}`, `Theory/Type/Inductive/{Base,HLevels}` | superseded |
| `Grammar/Unfold` | `Theory/Type/Coinductive/Base` | superseded |
| `Grammar/Later/{Base,Properties}` | `Theory/Type/Later/{Poset,Indexed,Tabulated,Tag,Derivative,Lex}`, `Theory/Type/Guarded/{Base,Justification}` | superseded (expanded 2 → 8 files) |
| `Grammar/Maybe{,/Base}` | `Theory/Type/Monad/Maybe` (+ `Cont`, `Except`, `NonDet`) | superseded |
| `Grammar/Negation{,/Base}` | `Theory/Type/Decidable/Base.¬Ty` | superseded |
| `Grammar/Properties{,/Base}` | `Theory/Type/Unambiguity/{Base,Disjoint}` | superseded |
| `Grammar/SemanticAction/{Base,Monadic}`, `Grammar/SemanticAction.agda` | `Theory/Type/SemanticAction/{Base,Pipeline}`, `Theory/Instances/Monoid/SemanticAction` | superseded |
| `Grammar/LinearProduct/*` (8 files, incl. `AsPath`/`AsEquality`) | `Theory/Type/Operation/Base` (⊗ as *any* signature operation) + `Theory/Instances/Monoid/{Unitor,Convolution}` | superseded, generalised |
| `Grammar/LinearFunction{,/Base}` | `Theory/Type/Residual/Base`, `Theory/Instances/Monoid/{Residual,Residual/Laws}` | superseded |
| `Grammar/Reify{,/Base}` | `Theory/Type/Reify/Base`, `Theory/Type/Representable/Base` | superseded |
| `Grammar/Subgrammar/{Base,Equalizer}` | `Theory/Type/Subgrammar/{Base,Equalizer}` | superseded |
| `Grammar/PropositionalTruncation/Base` | `Theory/Type/PropositionalTruncation/Base` | superseded |
| `Grammar/String/*` (5), `String/Base`, `Grammar/Epsilon/*` (6), `Grammar/Literal/*` (7) | `Theory/Instances/Monoid/{Base,ListPresentation,Strings,Types}` | superseded |
| `Grammar/KleeneStar/Inductive/*` (3) | `Theory/Instances/Monoid/KleeneStar{,/Guarded,/Map,/Read,/Unambiguous}` | superseded |
| `Grammar/Derivative/{Base,String}` | `Theory/Instances/Monoid/Derivative{,/General}` | superseded |
| `Grammar/Greedy/{Base,Automata}` | `Theory/Instances/Monoid/Greedy/{Base,Examples}`, `Automaton/{Greedy,GreedyMax}` | superseded |
| `Grammar/RegularExpression/{Base,Deterministic}` | `Theory/Instances/Monoid/Regex/*` (11 files) | superseded |
| `Grammar/SequentialUnambiguity/*` (5) | `Theory/Instances/Monoid/SequentialUnambiguity/{Base,First,FollowLast,Nullable}` | superseded |
| `Grammar/Coherence` (73) | — | **deliberately cut** (`theory-port-status.md`); content is `Monoid/Unitor` |
| `Automata/NFA/{Base,Properties}`, `Automata/NFA.agda` | `Theory/Instances/Monoid/Automata/NFA/{Base,Properties}` | superseded |
| `Automata/DFA/Base`, `Automata/DFA.agda` | `Theory/Instances/Monoid/Automata/DFA/Base` | superseded |
| `Automata/Deterministic` | `Theory/Instances/Monoid/Automaton/{Deterministic,Print,Unambiguous,Disjoint}` | superseded (records merged) |
| `Automata/Implicit`, `Automata/Implicit/{AsDeterministic,RegExp,RegExp/StrongEquivalences,RegExp/WeakEquivalences}` | `Theory/Instances/Monoid/Automaton/Implicit{,/Analysis,/Compile,/Disjointness,/RegExp,/Soundness}` | superseded |
| `Thompson/*` (9) | `Theory/Instances/Monoid/Thompson/*` (10, incl. new `Construction/Sat`) | superseded |
| `Determinization/WeakEquivalence` | `Theory/Instances/Monoid/Determinization/WeakEquivalence` | superseded |
| `Parser/{Base,RecursiveDescent}`, `Parser.agda` | `Theory/Instances/Monoid/Combinator/**` (35 files) | superseded, vastly expanded |
| `Lex/Det/{Base,Eval}` | `Theory/Instances/Monoid/Lex/{Base,Regex}`, `Automaton/{Lexicon,TokenStream}` | superseded |
| `String/Unicode` | `Theory/Instances/Monoid/Unicode/Base`, `Regex/Unicode` | superseded — **and the postulate is gone** (see §4.1) |
| `Examples/Dyck`, `Examples/Benchmark/Dyck` | `Theory/Instances/Monoid/Grammars/Dyck`, `Combinator/{Decidable,Incomplete}/Dyck`, `Pipeline/Dyck` | superseded |
| `Examples/BinOp`, `Examples/RecursiveDescent/BinOp` | partially — `Combinator/{Grammars/Arith,Decidable/Arith}` | **partial** |
| `Examples/RegexParser` (35) | `Theory/Instances/Monoid/Regex/{Parse,ParseTests}` | superseded |

### 1.4 OLD modules with NO new counterpart

Verified by name-grep against `src/Theory` and `src/Cubical`:

| module | lines | note |
|---|---:|---|
| `src/Automata/Turing.agda` + `src/Automata/Turing/OneSided/Base.agda` | 129 | `grep -rli turing src/Theory src/Cubical` → **0 hits**. `theory-port-status.md` lists this as "landed, 133 lines" — **that is wrong; the file does not exist.** Only genuinely-lost *theory* content. |
| `src/String/ASCII.agda`, `src/String/ASCII/Base.agda`, `src/String/ASCII/NoWhitespace.agda` | 271 | `grep -rli ascii src/Theory` → 0 hits. `Theory` has Unicode only. `ASCII/Base.agda:31` carries `-- TODO : go back and make this the whole table`, so it is incomplete anyway. |
| `src/String/SubAlphabet.agda` | 57 | 0 hits in `Theory`. The sub-alphabet embedding; would be wanted by any two-phase lexer. |
| `src/Grammar/External/**` (8 files) | 1,439 | **deliberately not portable.** States grammar facts in `Set` rather than internally; `Monoid/Precise` is the internal replacement. `theory-port-audit.md` §5. |
| `src/Grammar/Coherence.agda` | 73 | **deliberately cut.** Superseded by `Monoid/Unitor`. |
| `src/Examples/Section2/{Alphabet,Figure1,Figure3,Figure4,Figure5}.agda` | 394 | paper figures, cited by `README.md`; no new counterpart |
| `src/Examples/BinOp.agda` + `src/Examples/RecursiveDescent/BinOp.agda` | 963 | only *partially* covered by `Combinator/Grammars/Arith` |
| `src/Grammar/{Epsilon,Literal,LinearProduct}/As{Path,Equality}/**` + `{Sum,Product}/Binary/As{Primitive,Indexed}/**` (30 files) | 2,669 | **deliberately dropped duplication**; `Theory` picked one presentation of each |

**Total that must be ported before deletion: 457 lines**
(`Automata/Turing/*` 129 + `String/ASCII*` 271 + `String/SubAlphabet` 57), plus
a decision on the 1,357 lines of paper-figure examples. Everything else in the
old tree is either superseded, deliberately cut, or deliberately not portable.

---

## 2. Recommendation on the old tree

**Verdict: delete it, after porting 457 lines and rewriting `README.md`.**

Evidence for deletion:

1. **Zero reachability** (§1.1). Not one import crosses the boundary.
2. **Zero maintenance.** Last commit touching the old tree is `8a050a4`
   (2026-08-03, "Performance Improvements, Odds and Ends (#50)"), 25 days and
   4-of-the-last-100 commits ago. All 4 predate the `theory-core` branch work.
3. **~40 % of the build** (§1.2) for content that is dead.
4. **`--lossy-unification` asymmetry** (§4.5): 0 of 169 old files use it, 137 of
   202 new ones do. The old tree is not even a useful performance canary.
5. The repo already has a written, verified port plan (`notes/theory-port-*.md`)
   whose conclusion is the same.

Blockers, in order:

* **B1 — port `Automata/Turing/OneSided/Base.agda` (123 lines).** The only
  module whose *theory* has no replacement, and `README.md:171` advertises it as
  a contribution. `theory-port-status.md` claims it landed; it did not. Either
  port it to `Theory/Type/Automaton/Turing` (its `Trace` is a `Code`, per the
  audit's §6(b) argument) or explicitly retract the claim.
* **B2 — decide on `String/{ASCII/*,SubAlphabet}` (328 lines).** Cheap and
  mechanical; `Theory/Instances/Monoid/Unicode/Base` is the model.
* **B3 — `README.md` is a 438-line guide to the *old* tree.** It names
  `Grammar.Equivalence.Base`, `Grammar.Properties.Base`,
  `Grammar.Sum.Binary.AsPrimitive.Properties`, `Automata.DFA.Base`,
  `Automata.Deterministic`, `Determinization.WeakEquivalence`,
  `Thompson.Construction.Literal`, `Automata.Turing.OneSided.Base`,
  `Examples.Dyck`… and mentions `Theory` **once**. It also instructs the reader
  to build `README.agda` and run `make litmus` — **neither exists**
  (`ls src/README.agda` → absent; `src/Makefile` has no `litmus` target). The
  README is stale independently of this decision.

**Do not use an `attic/`.** An `attic/` under `src/` stays inside
`include: .` and keeps being typechecked — it buys nothing. An `attic/` outside
`src/` is a directory of code nobody can build, which is what `git` is for.
Tag the current commit (`git tag artifact-popl` — the repo currently has **no
tags at all**) and `git rm -r` the old tree; the paper artifact then points at
the tag.

If B1–B3 cannot be done now, the interim measure that recovers most of the
build cost without losing the code is to move the old tree out of the library
include path (e.g. `src/legacy/` plus `include: .` → an explicit list, or a
second `.agda-lib`), so `--build-library` stops walking it.

---

## 3. Module organisation in the NEW tree

### 3.1 Files over 400 lines (`wc -l`, sorted)

Only **12** new-tree files exceed 400 lines. Top 15 shown:

| # | lines | file | verdict |
|---:|---:|---|---|
| 1 | 2,008 | `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda` | **split — 4 files' worth.** Lines 1–996 grammar + LL table; 996–1,224 raw token syntax and 101 `Eq.refl` parse tests; 1,225–1,500 three elaboration passes (concrete→AST, scope check, type inference) plus their tests; 1,501–2,008 the *decided* versions of passes 2 and 3. This is a whole front end in one module, and it is the only file in the tree that puts grammar, parser, tests and semantics together — the sibling convention is exactly the opposite (`Combinator/Grammars/PolyGrammar` + `Grammars/Polynomial` + `Grammars/PolynomialTests` + `Decidable/Polynomial`). Suggested: `STLC/{Grammar,Parser,Tests,Elaborate,Scope,Typecheck}.agda`. |
| 2 | 1,214 | `src/Theory/Instances/Monoid/Automaton/Implicit/Soundness.agda` | **split — mirrors an existing shape.** 9 top-level declarations, but the body is per-connective: base cases 90–221, alternation 222–468, concatenation 469–773, star 774–1,054, then the two maps and the theorem 1,097–1,214. `Thompson/Construction/` already splits exactly this way (`Sum`, `LinearProduct`, `KleeneStar`). Suggested `Soundness/{Base,Sum,LinearProduct,KleeneStar}.agda` + `Soundness.agda` assembling `compile-sound`. |
| 3 | 636 | `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda` | **justified.** One grammar (`μ polyCode`), 3 codes, 62 declarations, all about the same production set; the header explains the left-factoring. Tests already live in `Grammars/PolynomialTests`. |
| 4 | 547 | `src/Theory/Instances/Monoid/Combinator/Core.agda` | **justified.** 6 records (`AnswerFunctor`, `CovariantAnswer`, `LawfulAnswer`, `CommittingAnswer`, …) that only make sense together — the header documents deliberately collapsing three copies into one. Borderline: `LawfulAnswer` + its consequences could move to `Core/Laws.agda`. |
| 5 | 545 | `src/Theory/Instances/Monoid/Strings.agda` | **split.** 50 top-level declarations covering three distinct things: (a) the `List`-presentation of the free monoid and `↓M tt` reductions, (b) the connectives `εTy`/`literal`/`char` and 12 `open import … public` re-exports of the whole `Theory/Type` tier, (c) `String*`, `readChars`, `readSq'` and `⊤Ty ≅ String*`. (b) is an index module wearing a content module's clothes (§3.4). Suggested `Strings/{Base,Connectives,Star}.agda`. |
| 6 | 544 | `.../Thompson/Construction/LinearProduct.agda` | **justified.** One theorem (`Parse (⊗NFA N N') ≅ Parse N ⊗ Parse N'`); the length is the splitting bookkeeping. |
| 7 | 512 | `.../Thompson/Construction/KleeneStar.agda` | **justified.** Same, for `*`. |
| 8 | 512 | `src/Theory/Instances/Monoid/Automaton/GreedyMax.agda` | **borderline.** 0 top-level declarations and 1 record — everything is nested inside `module _ (…)`. The `GreedyMax→Greedy` transport and `cancel` are a separable second half. |
| 9 | 496 | `.../Determinization/WeakEquivalence.agda` | **justified.** ε-closure + subset construction + `NFA≈DFA`; the three are one argument. |
| 10 | 474 | `src/Theory/Instances/Monoid/Automaton/TokenStream.agda` | **borderline.** Highest import count in the tree (37, §3.5) — a fan-in that size usually means the module is doing two jobs. |
| 11 | 434 | `.../SequentialUnambiguity/Base.agda` | **split.** 21 declarations across 5 nested `module _` blocks: `_⊛_` and its closure; `⊛→must-split`; `⊗&-distL`; the four `∉FollowLast-*` congruences. `FollowLast.agda` (73 lines) exists next to it and holds only the definition, so the split boundary is already wrong (§3.3). |
| 12 | 412 | `src/Cubical/Relation/Nullary/DecidablePropositions/More.agda` | **justified but misplaced.** This is upstream material for `cubical`; `src/Cubical/WildCat/LocallySmall/Base.agda:1` even says `-- TODO put in ccl`. |
| 13 | 389 | `.../Combinator/Decidable/Bracket.agda` | justified |
| 14 | 383 | `src/Theory/Instances/Monoid/Residual.agda` | justified |
| 15 | 383 | `.../Automaton/Implicit/Analysis.agda` | justified |

### 3.2 `Base.agda` grab-bags

48 `Base.agda` files in the new tree. Sorted by size, with top-level
declaration counts:

| lines | decls | data/rec | nested modules | file |
|---:|---:|---:|---:|---|
| 434 | 21 | 0 | 5 | `.../SequentialUnambiguity/Base.agda` |
| 299 | 18 | 0 | 2 | `Theory/Type/Residual/Base.agda` |
| 266 | 27 | 0 | 1 | `Theory/Type/Operation/Base.agda` |
| 265 | 27 | 0 | 3 | `.../Monoid/Suffix/Base.agda` |
| 221 | 25 | 2 | 2 | `Theory/Type/Decidable/Base.agda` |
| 188 | 1 | 3 | 5 | `.../Automata/NFA/Base.agda` |

Assessment — most are **not** grab-bags: `Decidable/Base` (25 decls) is entirely
about `¬Ty`/`DecTy`/`Decidable`; `Operation/Base` is entirely about the lifted
signature operation. The genuine offenders are:

1. **`src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda`** (434) — see
   §3.1 #11. It is `Base` only in the sense of "whatever did not fit in
   `Nullable`/`First`/`FollowLast`".
2. **`src/Theory/Instances/Monoid/Types.agda`** (120) — not a `Base.agda` but
   the same failure mode inverted: it is the tree's *index* module (12
   `open import … public`) and it also contains six `isSet…` lemmas, the
   `⊗⊕-distL⁻` inverse plus both round-trip proofs, five `TheorySet` bundles,
   and `_≟M_`. An index module that carries proofs cannot be re-exported
   selectively. Move the content to `Strings/HLevels.agda`.
3. **`src/Theory/Instances/Monoid/Base.agda`** (54) — *correctly* scoped (the
   monoid signature + equations) but **misleadingly named**: a reader looking
   for "the Monoid instance index" opens this and finds `MonSig`/`MonEqns`. It
   should be `Monoid/Signature.agda`, freeing `Monoid/Base.agda` (or better,
   `Monoid.agda`) to be the index.

### 3.3 `X.agda` vs `X/Base.agda`

Both conventions are in use, split 7 / 48.

**Group A — parent module `Foo.agda` beside directory `Foo/`** (7):

```
src/Theory/Instances/Monoid/Residual.agda            + Residual/
src/Theory/Instances/Monoid/Derivative.agda          + Derivative/
src/Theory/Instances/Monoid/Phase.agda               + Phase/
src/Theory/Instances/Monoid/KleeneStar.agda          + KleeneStar/
src/Theory/Instances/Monoid/Thompson/Construction.agda + Construction/
src/Theory/Instances/Monoid/Automaton/Implicit.agda  + Implicit/
src/Cubical/Algebra/Theory/Finitary.agda             + Finitary/
```

Of these, only `Thompson/Construction.agda` is a pure re-export (6
`open import … public` of its children); the other six carry content *and* have
children — the exact shape `Foo/Base.agda` exists to avoid.

**Group B — `Foo/Base.agda` with no `Foo.agda`** (48): everything under
`Theory/Type/*` (`Bottom`, `Code`, `Coinductive`, `Cover`, `Decidable`,
`Equalizer`, `Equivalence`, `Function`, `Guarded`, `Inductive`, `Lift`, `Monad`,
`Operation`, `Product`, `Product/Binary`, `PropositionalTruncation`, `Reify`,
`Representable`, `Residual`, `SemanticAction`, `Subgrammar`, `Sum`,
`Sum/Binary`, `Top`, `Unambiguity`), plus `Theory/{Base,Free/Base}`,
`Theory/Instances/{Monoid,Bags,Lambda,STLC}/Base.agda`, and 15 more.

**Group C — directories with neither** (25): `Theory/Type/Later`,
`Theory/Instances/Monoid/{Automaton,Automata,Combinator,Combinator/Grammars,Determinization,Grammars,Pipeline}`,
`Theory/Instances/Monoid/Backreference/Stress`, and the `Cubical/*` namespace
dirs. A client wanting the automaton layer has no single entry point at all.

**Recommendation: standardise on `Foo/Base.agda`.** It is already the 87 %
majority, it is the `cubical`/`agda-stdlib` convention the rest of the file tree
imitates, and it removes the ambiguity of whether `Foo.agda` is content or
index. The 6 content-bearing Group-A files become `Foo/Base.agda`;
`Thompson/Construction.agda` (a genuine re-export) is the one case where a
parent module is right — but then it should be spelled the same way as any
other index (§3.4), i.e. `Thompson/Construction/Everything.agda` or, better,
folded into `Thompson/Base.agda`.

### 3.4 Index / re-export modules

**There is one, and it is unadvertised.** The chain is

```
Theory/Instances/Monoid/Strings.agda   (12 × open import … public)   ← the connectives
  ↳ Theory/Instances/Monoid/Types.agda (12 × open import … public)   ← + HLevels, SemanticAction, Lookahead, Cover, Monad, Decidable
      ↳ Theory/Instances/Monoid/Combinator/Core.agda (2 × public)    ← + Suffix
          ↳ Combinator/Decidable/Base.agda (2 × public)              ← + Precise
```

so a client of the LL parser combinators imports **one** module
(`Combinator/Decidable/Base` with `(Alphabet, _≟_, ℓ)`) and gets the DSL. That
is good — but nothing says so. Specifically:

* **`src/Theory/Base.agda` is not an index** (112 lines). It defines `TheoryTy`,
  `_⊢_`, `id⊢`, `_∘⊢_`, `_⋆⊢_` and the `THEORYTY` locally-small wildcat. It has
  **zero** `open import … public`.
* **`src/Theory/Instances/Monoid/Base.agda` is not an index** (54 lines). It
  defines `MonSig`/`MonEqns`; its only `public` is
  `open import Cubical.Data.FinData.More public` (line 10), which re-exports a
  *stdlib supplement*, not any part of the DSL.
* There is no `src/Theory.agda`, no `src/Theory/Type.agda`, no
  `src/Theory/Instances/Monoid.agda`, and no `Everything.agda` anywhere.

Import counts confirm the cost where the chain does not reach: mean **12.7**
imports per file across the 191 `Theory` files (2,431 total). The worst are
`Automaton/TokenStream.agda` (37), `Strings.agda` (36),
`Determinization/WeakEquivalence.agda` (34), `Implicit/Soundness.agda` (29),
`Automaton/GreedyMax.agda` (29), `Suffix/Base.agda` (28). Every one of those is
in the automaton layer, which is exactly the layer with no index.

**Propose these index modules:**

| new module | re-exports |
|---|---|
| `src/Theory/Type/Everything.agda` | all 46 `Theory/Type/**`, parameterised by `(σeq, V, vs, 𝒫)` — the generic tier, once |
| `src/Theory/Instances/Monoid.agda` (or `Monoid/Everything.agda`) | `Types` + `Precise` + `Suffix/Base` + `KleeneStar` + `SequentialUnambiguity/*` — "the grammar DSL at a discrete alphabet" |
| `src/Theory/Instances/Monoid/Automaton.agda` | `Deterministic`, `Print`, `Unambiguous`, `Disjoint`, `Greedy`, `GreedyMax`, `Implicit/*` — the layer that currently has none (Group C) |
| `src/Theory/Instances/Monoid/Combinator.agda` | `Core`, `Decidable/Base`, `Incomplete/Base`, `NonDet/Base`, `Syntax` |
| `src/Theory/Instances/Monoid/Regex.agda` | the 11 `Regex/*` modules |
| `src/Everything.agda` | every module — replaces the deleted `README.agda` the README still tells users to build, and makes `make check` scope explicit instead of "whatever is under `src/`" |

### 3.5 Import hygiene

**`open import … public` chains.** 72 in the new tree. They are *mostly*
disciplined: 61 are index-shaped (re-exporting a module the client genuinely
needs, with `hiding (…)` where names clash — see `Types.agda:36,44`). Three are
smells:

* `src/Theory/Instances/Monoid/Base.agda:10` —
  `open import Cubical.Data.FinData.More public`. Re-exporting a *stdlib
  supplement* from a signature module means `Fin`-manipulation names leak into
  every module that transitively opens the DSL, with no clue where they came
  from. Same at `src/Theory/Instances/STLC/Base.agda`.
* `src/Theory/Instances/Monoid/Backreference/Stress/Common.agda` — four
  `open import Cubical.Data.{List,FinData,Nat,Unit} using (…) public`. A test
  helper re-exporting the standard library.
* `src/Theory/Instances/Monoid/Suffix/Base.agda` —
  `open import Theory.Type.Later.Tag public` (unparameterised, so it crosses the
  generic/instance boundary silently).

The 4-deep chain `Strings → Types → Combinator/Core → Decidable/Base` is the
real "where does this name come from?" hazard: by the time a client writes
`_⊗_` it has passed through four `public` hops and 26 re-exported modules. The
fix is not fewer hops but *naming the hops* — an explicit `Everything`-style
index whose job is re-export, so that content modules stop doing it (§3.4).

**Convention `open` vs `open … using`.** There is a real, deliberate convention
in the new tree, and it is roughly two-thirds followed:

| | bare `open import X` | `open import X using (…)` | `import X as Y` |
|---|---:|---:|---:|
| new tree (`Theory` + `Cubical`) | 1,373 (66 %) | 620 (30 %) | 481 |
| old tree | 1,420 (98 %) | 24 (2 %) | — |

The pattern is: **external** imports (`Cubical.Data.*`) get `using (…)` or an
alias; **internal** imports (`Theory.*`, which are parameterised and applied) are
bare. That is a defensible rule and it is worth writing down, because the 1,373
bare imports currently give no way to tell which ones are internal-by-design and
which are just unqualified stdlib.

**Likely unused imports** (grep heuristic; operator names excluded because
mixfix use is invisible to a literal grep).

*22 unused qualified aliases* — high confidence, the alias never appears as
`Alias.`:

```
src/Cubical/WildCat/LocallySmall/Base.agda                       Eq
src/Theory/Instances/Bags/Base.agda                              Eq
src/Theory/Instances/Bags/Generation.agda                        Eq
src/Theory/Instances/Monoid/Automaton/Deterministic.agda         L
src/Theory/Instances/Monoid/Automaton/Implicit/Disjointness.agda L, Sum
src/Theory/Instances/Monoid/Combinator/Decidable/Arrow.agda      Empty
src/Theory/Instances/Monoid/Combinator/Incomplete/Dyck.agda      Eq
src/Theory/Instances/Monoid/Determinization/WeakEquivalence.agda PTMonad
src/Theory/Instances/Monoid/Greedy/Examples.agda                 AS
src/Theory/Instances/Monoid/Phase.agda                           Eq
src/Theory/Instances/Monoid/Phase/Display.agda                   DecBase, KS, Ph, RSat, RU, SA, Str   ← 7 of its 20 imports
src/Theory/Instances/Monoid/SequentialUnambiguity/FollowLast.agda Sum
src/Theory/Instances/Monoid/Thompson/Construction/Bottom.agda    Eq
src/Theory/Instances/STLC/Base.agda                              Eq
src/Theory/Type/Later/Tabulated.agda                             SD
```

`src/Theory/Instances/Monoid/Phase/Display.agda` (323 lines) alone has **7
dead aliases out of 20 imports** — worth a look, it may be a module whose
content moved out from under it.

*~120 unused names in `using (…)` lists* — medium confidence. Common shapes:
`tt*`, `Unit*`, `suc`, `zero`, `true`, `false`, `[]`, `ℕ`, `⊥`, `isSetBool`,
`fst`, `snd` imported and never mentioned. (`fst`/`snd` may be used as record
projections `.fst`, so those are low confidence; the rest are solid.) Examples:
`src/Theory/Instances/Monoid/Strings.agda` (`isSetBool`, `Unit*`),
`src/Theory/Instances/Monoid/Base.agda` (`ℕ`, `⊥`),
`src/Theory/Type/Later/Indexed.agda` (`true`, `false`),
`src/Theory/Instances/Monoid/Automaton/ScratchPerf.agda` (`true`, `false`,
`length`, `toℕ`).

---

## 4. Build health

Every pattern the brief listed, over `src/**` minus `_build`.

| pattern | hits |
|---|---:|
| `postulate` | **1** |
| `TERMINATING` | **7** (+6 mentions in comments) |
| `NON_TERMINATING` | 0 |
| `trustMe` / `primTrustMe` | 0 |
| `--no-positivity-check` | 0 |
| `NO_POSITIVITY_CHECK` | **1** |
| `NO_UNIVERSE_CHECK` | 0 |
| `unsafe` (any case) | 0 |
| `{-# REWRITE` | 0 |
| `TODO` | **17** |
| `FIXME` / `XXX` / `HACK` / `???` | 0 |
| holes `{!` | **2** (both inside comments) |
| `--lossy-unification` | **137 files** |

This is a clean bill of health for the *new* tree. Every single unsafe-pragma
hit is either in the old tree or is one of two structural `TERMINATING` sites.

### 4.1 `postulate` — 1 hit, old tree only

```
src/String/Unicode.agda:34   postulate
  mkUnicodeCharPath-yes : (c c' : UnicodeChar) → primCharEquality c c' ≡ true → c ≡ c'
  mkUnicodeCharPath-no  : (c c' : UnicodeChar) → primCharEquality c c' ≡ false → ¬ (c ≡ c')
```

**Load-bearing in the old tree, and already fixed in the new one.** These two
axioms internalise a JavaScript-computed character-equality oracle. The new
tree's replacement, `src/Theory/Instances/Monoid/Unicode/Base.agda:4`, opens by
naming exactly this problem — *"`String.Unicode` decides character equality
through a **postulated** path"* — and `src/Theory/Instances/Monoid/Regex/
Examples.agda:11` records the consequence: *"`String.Unicode`'s postulated
oracle would leave every branch stuck."* **`src/Theory` contains zero
postulates.** This is a strong argument for §2: deleting the old tree removes
the repo's only axiom.

### 4.2 `TERMINATING` — 7 pragmas

| location | judgement |
|---|---|
| `src/Theory/Type/Inductive/Base.agda:41,51` | **load-bearing.** The recursor for the `Code` fixpoint; Agda cannot see through the indexed functor. `src/Theory/Type/Guarded/Base.agda:81` documents it: *"matching on `roll`. `Inductive/Base`'s `rec` needs `TERMINATING`"*, and `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:2` records the escape route taken for the star — *"The Kleene fold by guarded recursion, so no `TERMINATING` is asserted."* So this is a known cost with a known alternative already applied where it mattered. |
| `src/Theory/Type/Coinductive/Base.agda:44,54` | **load-bearing**, same shape for the greatest fixpoint. |
| `src/Theory/Type/Inductive/HLevels.agda:154,169` | **load-bearing**, deriving set-ness by the same recursion. |
| `src/Grammar/Inductive/Indexed.agda:38,49` | old tree; the predecessor of the above. Dies with the tree. |
| `src/Grammar/Inductive/HLevels.agda:152,165` | old tree; ditto. |
| `src/Examples/Benchmark/Dyck.agda:42` | old tree; **smell** — a benchmark asserting termination. Dies with the tree. |

Net: after deleting the old tree, the repo has **6 `TERMINATING` pragmas in 3
files**, all in `Theory/Type/{Inductive,Coinductive}`, all for the same reason,
all documented, and with a guarded-recursion alternative already demonstrated in
`KleeneStar/Guarded`. That is the single highest-value soundness cleanup left.

### 4.3 `NO_POSITIVITY_CHECK` — 1 hit, old tree only

```
src/Grammar/Inductive/Indexed.agda:29   {-# NO_POSITIVITY_CHECK #-}
```

**Smell, and already resolved.** The successor
`src/Theory/Type/Code/Base.agda` + `Theory/Type/Inductive/Base.agda` carry no
positivity escape. Dies with the old tree.

### 4.4 `TODO` — 17, and holes — 2

Holes (both **inside comments**, so not real holes):

```
src/Grammar/Derivative/Base.agda:50   -- starts-with-repr : ∀ c w → (p : (literal c ⊗ ⊤) w) → w ≡ c ∷ {!p!}
src/Grammar/Derivative/Base.agda:51   -- starts-with-repr c w = {!!}
```

**Zero unfilled goals anywhere in `src/`.**

TODOs, by kind:

*Dead-code questions — 8, all in the new tree, all the same question:*
```
src/Theory/Type/Later/Lex.agda:1          -- TODO how much of this actually used?
src/Theory/Type/Later/Poset.agda:1        -- TODO how much of this actually used?
src/Theory/Type/Later/Indexed.agda:1      -- TODO how much of this actually used?
src/Theory/Type/Later/Derivative.agda:1   -- TODO how much of this actually used?
src/Theory/Type/Later/Tabulated.agda:1    -- TODO how much of this actually used?
src/Theory/Type/Guarded/Justification.agda:2 -- TODO how much of this is actually used?
src/Theory/Type/Monad/Base.agda:1         -- TODO how much of this Monad/ dir is actually used?
src/Theory/Type/Decidable/Base.agda:1     -- TODO how much of this is actually used?
src/Theory/Type/Code/Container.agda:1     -- TODO is this actually used?
```
That is **1,436 lines** (`Later/*` 826 + `Guarded/Justification` 320 +
`Monad/*` ~180 + `Decidable/Base` 221 + `Code/Container` ~90, overlapping) under
an unanswered dead-code question — a second, smaller version of the old-tree
problem, inside the new tree. `notes/theory-core-cleanup.md` §3 already answers
several of these per-module ("zero importers", "`Later/Base` no, the rest yes");
the answers should be applied and the TODOs deleted.

*Upstreaming — 1:*
```
src/Cubical/WildCat/LocallySmall/Base.agda:1  -- TODO put in ccl
```
Applies equally to the other 10 files under `src/Cubical/` (1,477 lines), which
are supplements to `cubical`/`cubical-categorical-logic` living in this repo.

*Design notes — 5 (old tree, dies with it):* `Automata/Implicit/RegExp/
WeakEquivalences.agda:43,50`, `String/ASCII/Base.agda:31`,
`Grammar/Derivative/Base.agda:89`, `Grammar/Later/Base.agda:37`.

*Real work items — 3:* `Theory/Type/Monad/Base.agda:19`
(*"use an upstream interface for defining Monads"*),
`Grammar/Greedy/Automata.agda:44`, `String/ASCII/Base.agda:31`.

### 4.5 `--lossy-unification` — 137 files

**All 137 are in `src/Theory`. Zero are in the old tree.** Pragma text is
uniform: 133 × `{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}`,
3 × `{-# OPTIONS --lossy-unification #-}`, 1 not on line 1
(`Combinator/Core.agda:3`, after a citation comment — harmless, but the file
starts with two comment lines before its `OPTIONS`, which is fragile).

Distribution, and this is the diagnostic:

| tier | with lossy | total | share |
|---|---:|---:|---:|
| `Theory/Type` (generic) | 13 | 46 | 28 % |
| `Theory/Instances/Monoid` | 113 | 126 | **90 %** |
| `Theory/Instances/Bags` | 10 | 11 | 91 % |
| `Theory/Free`, `Theory/Instances/{Lambda,STLC}`, `Cubical` | 1 | 19 | 5 % |

**Does the spread suggest one slow definition? Yes, and it is locatable.** The
boundary is sharp and it is not at `Theory/Base.agda` (no pragma), not at
`Theory/Type/Operation/Base.agda` (the `⊗` definition — no pragma), and not at
`Theory/Instances/Monoid/Strings.agda` (no pragma). It is at
**`src/Theory/Instances/Monoid/Types.agda`**, which *has* the pragma, and every
one of the 113 `Monoid` files below it inherits the need.

What changes at `Types.agda` is that the generic four-parameter application
`Theory.Type.X MonEqns Alphabet (λ _ → tt) listPresentation` gets fixed and
opened `public` twelve times over (lines 34–46), so every downstream goal is
stated in terms of a twelve-fold-composed module application whose head is a
`FreePresentation` record projection. That is precisely the shape lossy
unification exists to paper over.

The 13 `Theory/Type` files that need it independently are also informative:
`Code/{Base,Container}`, `Coinductive/Base`, `Guarded/{Base,Justification}`,
`Inductive/{Base,HLevels}`, `Later/Tabulated`, `Monad/NonDet`,
`PropositionalTruncation/Base`, `Subgrammar/{Base,Equalizer}`,
`Unambiguity/Disjoint` — i.e. **the fixpoint machinery**, which is the same
`Functor`/`Code` elaboration that also carries the 6 `TERMINATING` pragmas.

Two candidate causes, both worth a measurement:
1. `Pres.P P` / `↓M s` in `src/Theory/Base.agda:29,32` not reducing, so every
   `TheoryTy` goal drags the presentation record through unification;
2. the `Functor`/`Code` datatype in `Theory/Type/Code/Base.agda` being an
   indexed family whose indices mention `Alphabet` (this is also why
   `-WnoUnsupportedIndexedMatch` travels with the pragma in 133 of 137 files —
   the two are always applied together, which says they have one cause).

Recommendation: make `↓M`/`M` reduce (or `abstract`-seal them behind a clean
interface) and re-measure; a fix at `Types.agda` would remove the pragma from
113 files at once. Until then, the pragma should at minimum be **stated once**
— e.g. in a `Monoid/Types.agda` header comment naming the cause — rather than
copy-pasted 137 times with no explanation.

### 4.6 Build cache is stale for half the new tree

103 of 202 new-tree files have **no `.agdai`** in `src/_build/2.9.0/agda/`,
while 0 of 169 old-tree files are missing one. The unbuilt set is exactly the
recent work: all 10 `Theory/Instances/Bags/*` (bar `Base`), all 10
`Thompson/*`, all 4 `SequentialUnambiguity/*`, `Type/Subgrammar/*`,
`Type/PropositionalTruncation/Base`, `Type/Unambiguity/Disjoint`,
`Determinization/WeakEquivalence`, the whole `Automaton/` directory, most of
`Combinator/`. So the current cache spends 44 % of its bytes on a tree nobody
imports and does not cover the tree under development.

Also present: `src/_build/2.7.0.1/` — 2.9 MB, newest artifact 2025-04-27, for an
Agda version the flake no longer uses. Safe to delete.

---

## 5. Repo hygiene outside `src/`

`git ls-files` → 391 tracked files. `git status --porcelain` → 8 modified
(all under `src/Theory` and `src/Cubical/Algebra/Theory`), 2 untracked:
`Lean/` and `review.md`.

| path | what it is | belongs? | gitignored? |
|---|---|---|---|
| **`Lean/`** | **1.5 GB.** Contains *only* `Lean/.lake/` — `build/lib/lean/` plus downloaded `packages/{mathlib,batteries,aesop,Qq,Cli,plausible,proofwidgets,importGraph,LeanSearchClient}`. **No `lakefile.toml`, no `lakefile.lean`, no `lean-toolchain`, and zero `.lean` files outside `packages/`.** It is orphaned Lean 4 + mathlib build output for a project whose sources are not here. | **No — delete it.** | **No.** Shows as `?? Lean/`. |
| `review.md` | 45 lines of hand-written review notes at repo root (naming nits, Bags encoding doubts, a Lambda-example plan, "agents write a lot of AI slop comments"). Untracked. | Either commit it under `notes/` alongside the other three, or ignore it. Not at root. | No. Shows as `?? review.md`. |
| `kleenecat/` | 48 K — `kleenecat.tex` (847 lines) + `quiver.sty`. Tracked. A second LaTeX document. | Yes, but it duplicates `paper/`'s role with no shared build. Consider `papers/{main,kleenecat}/`. | n/a (tracked) |
| `notes/` | 76 K — `theory-core-cleanup.md` (815), `theory-port-audit.md` (241), `theory-port-status.md` (227). Tracked. | **Yes** — these are the most valuable non-code artifacts in the repo. But `theory-port-audit.md` is stale (§1.3): its §3–§6 "not ported" lists are now wrong, and `theory-port-status.md` claims `Automata/Turing/OneSided/Base` landed when it did not (§1.4). Add a "verified at commit X" line and re-verify. | n/a |
| `paper/` | 184 K — `paper.tex` (3,457), `refs.bib`, `Makefile`, `logo-agda.pdf`. Tracked. `.gitignore` has `!logo-agda.pdf` to survive the blanket `*.pdf`. | Yes. | build products covered by the LaTeX rules |
| `src/result` | symlink → `/nix/store/b7rzq…-grammars-and-semantic-actions-0.1`. | Build output. | **Yes** — `.gitignore` `result` / `result-*` (unanchored, matches at any depth). |
| `src/_build/` | 59 MB, two Agda generations (§4.6). | Build cache. | **Yes** — `.gitignore` line `_build`. |
| `.direnv/` | direnv/nix cache. | | **Yes.** |

**`.gitignore` assessment.** 3,125 bytes, ~230 lines, of which roughly **200 are
a stock LaTeX template** (`*.acn`, `*.gaux`, `*.eledsec[1-9][0-9][0-9]R`,
`sympy-plots-for-*.tex/`, `*.pytxcode`, …) that this repo will never produce. Of
the actually-relevant rules, several are **dead paths** from a previous layout:

```
/code/cubical/KleeneCategory/SilvaExercises.agda
/code/cubical/_build/
/code/cubical/Everything.agda
/code/Cubical/env/
/code/Cubical/Automaton/Everything.agda
/dist-newstyle/
CubicalDockerfile
Agda2.7.0.1Dockerfile
CubicalCategoricalLogicDockerfile
paper-difforigin/*
/paper/paper-oldtmp-*.tex
```

There is no `code/` directory in this repo.

Missing rules, in priority order:

1. `Lean/` — **the whole 1.5 GB directory is untracked and unignored.**
   Even after deleting it, add `Lean/` (or `.lake/`) so a stray `lake build`
   cannot re-create the situation.
2. `/review.md`, or move it to `notes/`.
3. A caution on `flake.nix:38` — `lib.cleanSource ./src` does **not** filter
   `_build`, so `nix build` copies the 59 MB build cache into the nix store on
   every evaluation. Add `_build` to the `filter` predicate beside the existing
   `.nix`/`flake.lock`/`.envrc` exclusions.

Also worth noting: **the repo has no git tags** (`git tag` → empty). Before
deleting the old tree (§2), tag the current state so the paper artifact has a
stable reference.

---

## 6. Top modularity recommendations

Ranked by (lines recovered or clarified) ÷ (risk).

1. **Delete the old tree — 18,871 lines, 169 files, ~40 % of every build.**
   Blocked only on porting 457 lines (`Automata/Turing/OneSided/Base` 123,
   `String/ASCII/*` 271, `String/SubAlphabet` 57), deciding the fate of ~1,357
   lines of paper figures, and rewriting `README.md`. Tag first — the repo has
   no tags. Deleting it also removes the repo's **only `postulate`**, its only
   `NO_POSITIVITY_CHECK`, and 5 of its 13 `TERMINATING` pragmas. (§1, §2, §4)

2. **Fix `--lossy-unification` at its source: `Theory/Instances/Monoid/
   Types.agda`.** 137 files carry the pragma, 113 of them below `Types.agda`;
   zero old-tree files need it. The boundary is exactly where the generic
   four-parameter `Theory.Type.*` applications get fixed and opened `public`
   twelve times. Make `↓M`/`M` (`src/Theory/Base.agda:29,32`) reduce, or seal
   them, and re-measure — a fix here removes the pragma from 113 files at once.
   Whatever the outcome, replace 137 copy-pasted pragmas with **one documented
   explanation** at the boundary. (§4.5)

3. **Add the six index modules of §3.4**, and rename
   `Theory/Instances/Monoid/Base.agda` → `Monoid/Signature.agda` so that
   `Monoid/Base.agda` can *be* the index. Today the DSL's entry point is the
   undocumented 4-hop `public` chain `Strings → Types → Combinator/Core →
   Decidable/Base`, and the automaton layer (mean 12.7 imports/file, worst 37)
   has no entry point at all. (§3.2, §3.4)

4. **Split `Combinator/Decidable/STLC.agda` (2,008 lines) into 5–6 files.**
   It is a whole verified front end — grammar, LL table, 101 parse tests, three
   elaboration passes, two decision procedures — in one module, and it is the
   only file in the tree that violates the sibling convention
   (`Grammars/X` + `Grammars/XTests` + `Decidable/X`). It is 2.4× the next
   largest file. (§3.1)

5. **Split `Automaton/Implicit/Soundness.agda` (1,214 lines) per connective**,
   mirroring `Thompson/Construction/{Sum,LinearProduct,KleeneStar}` — the
   internal section boundaries (lines 90/222/469/774/1097) already are that
   split. Same for `SequentialUnambiguity/Base.agda` (434 lines, 21 declarations
   across 5 unrelated `module _` blocks, with a 73-line `FollowLast.agda` next
   to it holding only a definition). (§3.1)

6. **Standardise on `Foo/Base.agda`** (already 48 files vs 7). Convert the six
   content-bearing `Foo.agda`-beside-`Foo/` modules — `Monoid/{Residual,
   Derivative,Phase,KleeneStar}.agda`, `Automaton/Implicit.agda`,
   `Cubical/Algebra/Theory/Finitary.agda` — and give the 25 index-less
   directories (`Automaton/`, `Automata/`, `Combinator/`, `Determinization/`,
   `Grammars/`, `Pipeline/`, `Type/Later/`, …) either a `Base.agda` or an
   `Everything.agda`. (§3.3)

7. **Answer the 9 `-- TODO how much of this actually used?` markers** on
   `Theory/Type/{Later/*, Guarded/Justification, Monad/*, Decidable/Base,
   Code/Container}` — ~1,400 lines under an open dead-code question inside the
   *new* tree, i.e. the old-tree problem in miniature. `notes/theory-core-
   cleanup.md` §3 already answers several per-module ("zero importers"); apply
   the answers and delete the markers. Then clean the 22 confirmed dead import
   aliases (7 of them in `Phase/Display.agda` alone) and write the
   internal-bare / external-`using` import convention down. (§3.5, §4.4)

8. **Repo hygiene: delete `Lean/` (1.5 GB of orphaned mathlib build output with
   no Lean sources, untracked *and* unignored), delete `src/_build/2.7.0.1/`
   (stale April-2025 interfaces), add `_build` to `flake.nix:38`'s
   `cleanSourceWith` filter so `nix build` stops copying 59 MB into the store,
   move `review.md` into `notes/`, and prune ~200 lines of stock-LaTeX and
   dead-`/code/` rules from `.gitignore`.** Then bring
   `notes/theory-port-audit.md` up to date — its "not ported" lists are stale,
   and `notes/theory-port-status.md` claims `Automata/Turing/OneSided/Base`
   landed when no such file exists. (§1.4, §4.6, §5)
