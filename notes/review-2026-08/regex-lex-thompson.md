# Audit: regex / lexing / Thompson subsystem

Scope: `src/Theory/Instances/Monoid/{Regex,Lex,Thompson,Backreference,Unicode}/**`,
`Sat.agda`, `Derivative.agda`, `Derivative/General.agda`; plus a skim of the older
`src/Thompson/**` and `src/Lex/**`.

Read-only review. Nothing was edited. `agda` was not run.

Findings are ranked by severity. Section headings map to the requested categories.

---

## S1 — Critical

### S1.1 `yield (satr P)` is a raw λ over the model — the one hole in an otherwise internal fold

`src/Theory/Instances/Monoid/Lex/Regex.agda:63-75`

```agda
yield : ∀ {n} (r : RE n) → SemanticAction (ty ⟦ r ⟧) (List Alphabet)
yield εr = semact-pure []
yield ⊥r = ⊥Ty-elim
yield ⟨ c ⟩r = semact-pure (c ∷ [])
yield (satr P) = λ m x → (x .fst .fst ∷ []) , tt          -- ← line 67
yield (r ⊗r r') = semact-map … (semact-⊗₂ (yield r) (yield r'))
```

Every other clause is a combinator term. The `satr` clause binds the word `m`
and the model element `x`, then projects twice. This is **unjustified**: `satG P`
is *by definition* `⊕[ x ∈ Sat P ] literal (x .fst)` (`Sat.agda:26`), so the
clause is exactly `semact-⊕ᴰ' λ x → semact-pure (x .fst)` — one `⊕ᴰ-elim`, no
escape at all. `Phase/Display.agda:185-187` already writes precisely that term
for `Display-satG`, so the DSL-internal version is known to typecheck.

**Fix.** Add to `Regex/Sat.agda` (next to `satTok`):

```agda
semact-sat : {P : Alphabet → Bool} → SemanticAction (satG P) Alphabet
semact-sat = semact-⊕ᴰ' λ x → semact-pure (x .fst)
```

then `yield (satr P) = semact-map (_∷ []) semact-sat`.

### S1.2 The same escape, copy-pasted into a test module

`src/Theory/Instances/Monoid/Regex/UnicodeTests.agda:61-63`

```agda
-- the letter a `satr` matched, read back out
satChar : {P : UChar → Bool} → SemanticAction (satG P) UChar
satChar m (x , _) = x .fst , tt
```

Byte-for-byte the same escape as S1.1, in a *test* file, where a display action
should have been imported instead. Fixed for free by S1.1's `semact-sat`.

Note the ancestor: `src/Theory/Instances/Monoid/SemanticAction.agda:25`
`semact-char m (c , p) = c , tt` is the same shape (it too is `semact-⊕ᴰ'`).
That definition appears to be the template all three copies were derived from;
fixing it internally would remove the precedent. (Strictly outside scope, but it
is the root.)

### S1.3 Every test module in scope ignores the `Suite` skeleton and hand-rolls its own harness

The target skeleton — unicode-lexer input, `Suite`'s `passes`/`_at_`/`_↦_`, a
*display* semantic action for the expected output — is implemented exactly once,
in `src/Theory/Instances/Monoid/Regex/Examples.agda:58-151`. Nothing else in
scope follows it. Five modules, each with its own harness:

| module | harness | violation |
| --- | --- | --- |
| `Regex/Tests.agda:28-29` | `matches r = observe (decide-r r ℓr) (semact-dec (semact-pure tt))` | (a) input is `a ∷ b ∷ []` over a bespoke two-letter `L`, not text; (b) local `matches`, not `passes`; (c) result is `Maybe Unit` — no output at all, so a test can only say "it matched", never *what* |
| `Regex/UnicodeTests.agda:26-38` | local `Yes`/`No`/`yes`/`no` refutation lemmas | (b) ad-hoc refutation lemmas, exactly what `Suite` exists to replace; (c) only `readIdent` (line 69) reports content, and via a hand-written action |
| `Regex/ParseTests.agda:24-36` | local `Yes`/`No`/`yes`/`no`, verbatim re-derivation of the UnicodeTests four | (b) duplicated harness; (c) no output at all — 22 assertions of the form `_ : Yes "ab" "ab"` |
| `Backreference/RegexTests.agda:29-30` | local `matches`, `Maybe Unit` | (a),(b),(c) |
| `Backreference/Stress/Common.agda:33-34` | a *third* copy of the same `matches` | (a),(b),(c) |

`passes`, `_at_`, `_↦_` are already in scope in all five (they come through
`Theory.Type.SemanticAction.Base`'s `open Suite public`, re-exported down the
`Regex.Notation → Regex.Base → Combinator.Decidable.Star` chain — this is how
`Examples.agda` gets them without an explicit import). So the rewrite needs no
new imports.

**Fix.**
1. Delete the local `matches`/`yes`/`no`/`Yes`/`No` in all five and export **one**
   pair from a new `src/Theory/Instances/Monoid/Regex/Harness.agda`:
   `decides : ∀ {n} (r : RE n) → AS.String → M.Maybe AS.String` built on
   `displayDec` from `Phase/Display.agda:~285`, plus the backreference twin on
   `decide-b`.
2. Restate every assertion as a single `passes (… at (… ↦ … ∷ …))` block per regex,
   as `Examples.agda:58-64` does.
3. `Regex/Tests.agda` and `Backreference/RegexTests.agda` should move to `UChar`
   and `text "…"`; the bespoke `data L = a | b` alphabet exists only to make the
   input writable, and the unicode lexer already solves that.

Concretely, `Regex/Tests.agda:36-43` becomes

```agda
_ : passes (decides ab at ("ab" ↦ M.just "ab" ∷ "a" ↦ M.nothing ∷ "ba" ↦ M.nothing ∷ []))
_ = refl
```

which is one assertion instead of three, and *says what was matched*.

### S1.4 `Thompson/Construction/Sat.agda` is a near-verbatim clone of `Construction/Literal.agda`

`src/Theory/Instances/Monoid/Thompson/Construction/Sat.agda:55-135` vs
`src/Theory/Instances/Monoid/Thompson/Construction/Literal.agda:36-137`.

`diff` shows the whole development is the same modulo `Unit ↦ Sat P`,
`literal c ↦ satG P`, `c-st ↦ lift c-st`: `STATE`, `STATE≅Fin2`, `⟦_⟧st`,
`satAlg`/`litAlg`, `fromNFA`, `toNFA`, `pre`, `post`, the local `roll↑`, and
`toNFA-homo` are all structurally identical. The Sat file's own header
(`Sat.agda:5`) admits it: *"This is `literalNFA` with `Unit` replaced by
`Sat P`"*. ~120 lines duplicated, including the delicate `⊗-unit-r⁻∘r` /
`map-step` cancellation argument, which now has to be maintained twice.

**Fix.** One shared `Thompson/Construction/OneStep.agda`, parameterised by a
`FinSet` `T` of transitions and a labelling `lbl : ⟨ T ⟩ → Alphabet`, whose state
language at `c-st` is `⊕[ t ∈ ⟨ T ⟩ ] literal (lbl t)`. Then

* `literalNFA c = oneStepNFA (Unit , isFinSetUnit) (λ _ → c)`, with
  `litNFA≅` the shared iso post-composed with `⊕ᴰ`-over-`Unit` ≅ identity;
* `satNFA P = oneStepNFA (Sat P , isFinSetSat P) fst`, with `satNFA≅` the shared
  iso directly (its target *is* `satG P`).

`Thompson/Base.agda:87-92` and `:105-106` then collapse to one clause each.

---

## S2 — High

### S2.1 `Backreference/Regex.agda` copies `Nullability` and its algebra out of `Regex/Base.agda`

`src/Theory/Instances/Monoid/Backreference/Regex.agda:37-55` reproduces
`src/Theory/Instances/Monoid/Regex/Base.agda:39-58` line for line:

```agda
-- Nullability (copied from `Regex.Base`)
data Nullability : Type ℓ-zero where
  nullable notNullable : Nullability
ν≢ν̸ : nullable ≡ notNullable → Empty.⊥
…
_·ν_ : Nullability → Nullability → Nullability
_+ν_ : Nullability → Nullability → Nullability
```

The stated reason — *"so this file stays independent of the regex parser"* — does
not hold: `Nullability` lives in `Regex/Base.agda`, which does not import the
parser (`Regex/Parse.agda` imports *it*). The two `Nullability` types are now
distinct, so an `RE`-indexed lemma cannot be reused at `REB` and vice versa.

**Fix.** Extract `Nullability`, `ν≢ν̸`, `_·ν_`, `_+ν_` into a new parameterless
`src/Theory/Instances/Monoid/Regex/Nullability.agda` and import it from both
`Regex/Base.agda` and `Backreference/Regex.agda`. The whole file is 20 lines and
takes no module parameters, so nothing is pulled in transitively.

The duplication runs deeper: `Backreference/Regex.agda:114-155` (`parseD` /
`parseD▷`) is the `D`-suffixed twin of `Regex/Base.agda:100-128`
(`parse` / `parse▷`), clause for clause, with `grpr`/`brefr` added. Since
`toParser` (`Backreference/Parser.agda:86`) shows `Parser` is a retract of
`ParserD`, `Regex/Base`'s `parse` should be *derived* — define `parse` on `RE`
as `toParser ∘ parseD` on the `n = 0` fragment of `REB`, or factor the shared
clauses through a common signature. As it stands, a fix to the nullability
side-condition handling has to be applied twice.

### S2.2 Three copies of `Dl`-across-the-connectives, which the adjoint pair already gives

`src/Theory/Instances/Monoid/Regex/Derivative.agda:139-184` proves, by matching
on splittings, `Dl-⊗-out`, `Dl-⊗-in-l`, `Dl-⊗-in-r`, `Dl-⊗-out!`, `Dl-⊕-out`,
`Dl-⊕-in`, `Dl-map`. Every one binds `m` and a model element and calls
`uncons++` / `subst` / `Eq.pathToEq`:

```agda
Dl-⊗-out m (ms , e , (a , (b , _))) with
  uncons++ (ms zero) (ms (suc zero)) c m (Eq.eqToPath e)
```

`Derivative/General.agda:107-118` says in a comment that these are the general
`∂-⊕ᴰ` / `∂-⊕ᴰ⁻` / `∂-⊥` "done by hand over splittings", and *those* are stated
purely from `∂-intro`/`∂-intro⁻` (`∂-⊕ᴰ = ∂-intro⁻ (⊕ᴰ-elim λ y → ∂-intro (σ⊕ y))`).
`Regex/Derivative.agda` does not import `Derivative/General.agda` at all.

Additionally `Regex/Derivative.agda:182-184` re-defines `Dl-map`, which already
exists at `Derivative.agda:72-74` with the identical body. `Derivative.agda:68-71`
has a comment explaining why the duplicate exists ("at `roll↑` the implicit
carriers resolve only against a locally-defined one") — that is a unification
workaround, not a reason for a second definition; a re-export with an explicit
`{C = _} {D = _}` at the use site would do.

**Fix.** Import `Derivative/General.agda` into `Regex/Derivative.agda` and
replace `Dl-⊕-out`/`Dl-⊕-in` with `∂-⊕ᴰ`/`∂-⊕ᴰ⁻` transported along
`∂⌈⌉→Dl`/`Dl→∂⌈⌉` (`General.agda:135-147`, already an iso). `Dl-⊗-out` and
`Dl-⊗-out!` genuinely need the `uncons++` case split (there is no general
`∂`-preserves-`⊗` law) — those are **justified** escapes; keep them, but they
should be the only three, and `uncons++` (`:124-130`) should move next to
`Derivative.agda`'s other list facts rather than sit `private` in a regex file.

### S2.3 `Regex/Derivative.agda` (244 lines) has no importer, no test, and no consumer

```
$ grep -rn "Monoid.Regex.Derivative" --include=*.agda src   # → 0 hits outside itself
```

The header (`:2-16`) argues the derivative is the fix for `decide-r`'s
exponential behaviour on `(a|a)*b`, `δ` and `residual` are defined
(`:68-89`), and `δ-sound`/`δ-complete` are proved (`:188-244`) — but nothing
builds a matcher from them, and there is no `Regex/DerivativeTests.agda`, so the
claim in the header is unverified in the repo. Meanwhile `Lex/Regex.agda:7-10`
and `Regex/Examples.agda:137-143` both apologise that the ordered-choice path *is*
exponential.

**Fix.** Either (a) close the loop — add `matchδ : ∀ {n} → RE n → String → Bool`
as the fold `isNullable ∘ fst ∘ residual r` plus a `Regex/DerivativeTests.agda`
whose cases include the `(a|a)*b` blowup the header names, so the linearity claim
becomes a regression test; or (b) if the direction is abandoned, delete the file
and keep the `δ-sound`/`δ-complete` statement in `notes/`. Leaving 244 lines of
proved-but-unused development in the build is the worst of the three.

Same shape, smaller: `src/Theory/Instances/Monoid/Lex/Base.agda` (53 lines) has
zero importers. `Lex/Regex.agda` does not use it (it goes straight through
`decide-r`). Either wire `Lex/Base.lex` into `Regex/Examples.agda`'s `lex`
(`Examples.agda:123-126` re-implements the `observe`+`semact-dec` sandwich by
hand) or delete `Lex/Base.agda`.

### S2.4 Nine dead regexes in `Backreference/Stress/Common.agda`

`src/Theory/Instances/Monoid/Backreference/Stress/Common.agda`. Referenced by
`StressTests.agda`: `copyRE`, `starRE`, `litbackRE`, `deepRE`, `twiceRE`,
`ambigRE`. Referenced by nothing, anywhere in `src`:

| name | line |
| --- | --- |
| `fourRE` | `:49-53` |
| `ambigStarRE` | `:79-80` |
| `searchRE` | `:85-89` |
| `ctlTailRE` | `:93-94` |
| `ctlMidRE` | `:96-98` |
| `ctlTwoStarRE` | `:100-101` |
| `ctlGrpRE` | `:107-111` |
| `ctlGrpTailRE` | `:115-117` |
| `ctlGrpTailRefRE` | `:120-122` |

These are leftovers of a benchmarking session — the comments say so
(`:91-92` *"Controls with the same shape … to say what the reference actually
costs"*). The measurements are recorded in `StressTests.agda:4-27` but the
controls that produced them are not asserted anywhere.

**Fix.** Delete all nine (`nestBody`/`repA` stay — `deepRE`/`litbackRE` use them),
or add the corresponding `_ : matches ctlMidRE … ≡ …` assertions so they are
actually exercised. The header's timing table would then be reproducible.

### S2.5 `src/Lex/Det/Base.agda` compiles with `--allow-unsolved-metas`

`src/Lex/Det/Base.agda:1`

```agda
{-# OPTIONS -WnoUnsupportedIndexedMatch --allow-unsolved-metas #-}
```

The only such pragma anywhere under the reviewed trees. `src/Makefile:15` runs
`agda --build-library`, so this file is typechecked on every CI run and its holes
are silently accepted. It is part of the pre-port `Grammar Alphabet` world
(`:17-36`) that `Theory/Instances/Monoid/Lex` replaces.

`src/Lex/Det/Eval.agda` is worse: the entire 21-line module is

```agda
opaque
  unfolding unfoldParserDefs unfoldRecursiveDescentDefs GA.⟜-Trace-disj runLex ruleAction
  eval-lex-det : Unit
  eval-lex-det = tt
```

— a normalisation-timing probe with no assertion.

**Fix.** `src/Lex/**` has one live consumer (`src/Examples/Benchmark/Dyck.agda:34`).
Either port that benchmark onto `Theory/Instances/Monoid/Lex` and delete
`src/Lex/`, or at minimum remove `--allow-unsolved-metas` and fix the holes, and
delete `Eval.agda`. Shipping a library whose CI green light includes an
unsolved-metas file is the highest-leverage single fix in this section.

### S2.6 The whole `src/Thompson/**` tree is a superseded duplicate that CI still builds

Nine files, 1662 lines, against 1908 lines under
`src/Theory/Instances/Monoid/Thompson/`. `diff` on each pair shows the same
constructions in the old `Grammar Alphabet` / `StrongEquivalence` idiom:

```
Base                 210 diff lines of 104/138
Construction/Sum     499 diff lines of 228/335
Construction/LinearProduct  991 diff lines of 509/544
Construction/KleeneStar     988 diff lines of 542/512
```

Live consumers: `src/Examples/RegexParser.agda:14-15` only. `--build-library`
typechecks both trees, so every Thompson change costs two typechecks and the two
can drift.

**Fix.** Port `src/Examples/RegexParser.agda` onto
`Theory.Instances.Monoid.Thompson.{Base,Equivalence}` and delete `src/Thompson/`.
If the port is not imminent, at least record in `README.md` which tree is
canonical — right now nothing in either file says.

---

## S3 — Medium

### S3.1 `satG` → `satTy`, and the rest of the `…G` sweep

`src/Theory/Instances/Monoid/Sat.agda:25-26` (the rename the maintainer asked for):

```agda
satG : (P : Alphabet → Bool) → TheoryTy ℓM tt
satG P = ⊕[ x ∈ Sat P ] literal (x .fst)
```

Use sites to update (12 files):
`Sat.agda:25,26,30`; `Regex/Sat.agda:10,43,55,59,64,72,77`;
`Regex/Base.agda:34,133,134`; `Thompson/Construction/Sat.agda:44,90,130`;
`Thompson/Base.agda:52`; `Thompson/Equivalence.agda:41,68`;
`Regex/UnicodeTests.agda:62`; `Phase/Display.agda:130,167,179,185,186,300`;
`Automaton/Implicit/Soundness.agda:61,186,196,206,209,1055,1056,1192`.

Note `Phase/Display.agda:185` names the *instance* `Display-satG` and
`Automaton/Implicit/Soundness.agda:1055` names a lemma `unambiguous-satG` — both
carry the suffix into a compound name and should become `Display-satTy` /
`unambiguous-satTy`.

Same wrong-suffix problem elsewhere (all reachable from the reviewed modules):

| name | `path:line` | proposed |
| --- | --- | --- |
| `ℓG` (`= ℓ-max ℓM ℓ`, "grammar level") | `Combinator/Decidable/Base.agda:46-47`, `Combinator/Incomplete/Base.agda:37-38`, `Combinator/NonDet/Base.agda:48-49` — re-exported into `Regex/Base` and `Lex/Base` | `ℓTy`, or better `ℓAns` (it is the answer-type level) |
| `ℓG` (`= ℓ-max ℓM (ℓ-suc ℓ-zero)`) | `Combinator/Grammars/{Dyck,ArithGrammar,PolyGrammar}.agda:25/48/170` | same |
| `löbG` | `Suffix/Base.agda:239`, used at `Backreference/Parser.agda:207` | `löbTy` |
| `semact-skip*g` | `KleeneStar/Guarded.agda:154`, used at `Lex/Base.agda:53` | the `g` here means *guarded*, not *grammar* — but it reads as the latter next to `löbG`. Rename to `semact-skip*-löb` and `semact-*g` (`:147`) to `semact-*-löb`, matching the comment at `Lex/Base.agda:47` which spells out "i.e. löb" |

Stale "grammar" vocabulary in prose (all should say "theory type" / "`TheoryTy`"):

* `Derivative/General.agda:2` — `{- The derivative of a grammar by a grammar, …`
* `Derivative.agda:55` — `-- The character-level names from` **`Grammar.Derivative.Base`** — a cross-reference to the *old* tree (`src/Grammar/Derivative/Base.agda`), from a Theory-tree file. Either drop it or say "ported from".
* `Regex/Derivative.agda:181` — "a map of grammars acts on derivatives"
* `Lex/Base.agda:35,48`; `Lex/Regex.agda:40`; `Regex/Examples.agda:5`;
  `Backreference/Regex.agda:99`; `Backreference/Parser.agda:4,5,144`;
  `Thompson/Construction.agda:2`
* `Phase/Display.agda:4,45` — the class docstring still says "a grammar knows how
  to print itself"

### S3.2 Inconsistent regex-constructor suffix: `…r` vs `…R`

`Regex/Base.agda` and `Regex/Notation.agda` use a lowercase `r`: `εr`, `⊥r`,
`⟨_⟩r`, `satr`, `_⊗r_`, `_*r`, `anyr`, `oneOfr`, `noneOfr`, `strr`, `repr`,
`atMostr`, `betweenr`, `_?r`, `_+r`.

`Regex/Unicode.agda:64-95` switches to uppercase for the *same kind of thing*:
`rangeR`, `charR`, `digitR`, `alphaR`, `alnumR`, `upperR`, `lowerR`, `xdigitR`,
`spaceR`, `blankR`, `punctR`, `cntrlR`, `printR`, `graphR`, `wordR`,
`notDigitR`, `notSpaceR`, `notWordR`, `dotR`, `bracketR`, `bracketNotR` — but
then `strU` (`:126`) uses neither. All three files are re-exported into the same
namespace by `Regex/Parse.agda:30`, so a reader sees `charR '-' ?r ⊗r digitR +r`
(`UnicodeTests.agda:85`) with two conventions in one expression.

**Fix.** Lowercase everywhere: `rangeR → ranger`, `digitR → digitr`, …,
`strU → stru`. 21 renames, all confined to `Regex/Unicode.agda`,
`Regex/Parse.agda:133-136,249,253`, `Regex/UnicodeTests.agda`, and
`Phase/Display.agda:311`.

### S3.3 Four copies of the `iso to from tf ft` boilerplate, three of `the-dec-prop`

The "this inductive `εTrans` type is a nested `⊎`" isomorphisms:

* `Thompson/Construction/Sum.agda:51-71` (`⊕State-rep`) and `:85-110` (`⊕εTrans-rep`)
* `Thompson/Construction/LinearProduct.agda:73-96` (`⊗εTrans-rep`)
* `Thompson/Construction/KleeneStar.agda:73-96` (`*εTrans-rep`)

All four are `to`/`from`/`tf`/`ft`, all four are a fan of `refl` clauses, and the
names carry no information (`tf`/`ft` = "to-from"/"from-to"?). And the finiteness
of the accepting-state sigma is written three times:

```agda
the-dec-prop : ⟨ N .Q ⟩ → Σ (hProp ℓ-zero) λ P → Dec (P .fst)
the-dec-prop q = isFinSet→DecProp-Eq≡ isFinSetBool true (N .isAcc q)
```
`LinearProduct.agda:117-118`, `KleeneStar.agda:114-115`, and inline at
`Thompson/Base.agda:123-124` and `:136-137`.

**Fix.**
1. New `Thompson/Construction/Finiteness.agda` exporting
   `isFinSetAcc : (N : NFA ℓ) → isFinSet (Σ[ q ∈ ⟨ N .Q ⟩ ] (true Eq.≡ N .isAcc q))`
   and `isFinOrdAcc`. Removes all five `the-dec-prop`/inline copies.
2. Rename the iso components in all four sites: `to → encode`, `from → decode`,
   `tf → decode-encode`, `ft → encode-decode` (or use the Cubical convention
   `sec`/`ret` directly). `Src` should be spelled out as e.g. `⊕εTrans-code`.

### S3.4 Opaque `cong`-motive scaffolding in `Thompson/Construction/KleeneStar.agda`

`src/Theory/Instances/Monoid/Thompson/Construction/KleeneStar.agda:357-420`

```agda
    -- the shapes each branch passes through
    nA : … ; nB : … ; nC : …
    εB : …
    sA : … ; sB : … ; sC : … ; sD : … ; sE : …
```

Eight helpers named by letter. They are `cong`-motives for the chain at
`:431-455`, so they are not algorithms, but the reader has no way to tell `sB`
from `sD` without expanding both. Related weak names in the same file:
`hOf` (`:322`), `pf` (`:429`), `Eqr` (`:316`), `to`/`from`/`tf`/`ft` (`:78-96`),
`the-dec-prop` (`:114`).

`LinearProduct.agda:428-497` already uses a better convention for the *same*
argument — `accA`/`accB`/`accB2`/`accC`, `stepA`…`stepE`, `secL-uncurry`,
`V-acc`/`V-step` — so the two sibling files disagree.

**Fix.** At minimum align KleeneStar with LinearProduct: `nA/nB/nC → stopA/stopB/stopC`,
`sA…sE → stepA…stepE`, `hOf → branch-roll`, `pf → equalizes`, `Eqr → EqCarrier`.
Better: name them for what they do, e.g. `stopA → after-from*`,
`stopB → stop-then-star`, `stopC → stop-under-unitor`, `stepC → step-through-dst`,
`stepE → step-rolled`. The same pass should hit LinearProduct's `accB2`,
which is a name that says "the second one".

`Thompson/Construction/Sat.agda:117` and `Literal.agda:~85` both define a *local*
`roll↑`, which **shadows** the global `roll↑` of `KleeneStar.Guarded` (the star's
fold-in, used at `Regex/Base.agda:170` and `Regex/Derivative.agda:208`). Rename
to `roll-step` — which is exactly what `LinearProduct.agda:294` already calls the
same thing.

### S3.5 `namedClass`'s `go` ignores both of its arguments

`src/Theory/Instances/Monoid/Regex/Parse.agda:139-159`

```agda
namedClass cs = go (AS.primStringToList "alpha") isAlpha
  where
  …
  go : List AC.Char → (UChar → Bool) → M.Maybe (UChar → Bool)
  go _ _ =
    try "alpha" isAlpha (try "digit" isDigit ( … ))
```

`go` takes two parameters and pattern-matches neither; the call site passes
`"alpha"` and `isAlpha` as dummies. This is a half-finished refactor: the
`try`-chain closes over `cs` from the enclosing scope, so `go` is a zero-argument
thunk wearing two arguments.

**Fix.** Delete `go` and inline the `try`-chain as `namedClass`'s body. Rename
`try` to `matchName` and `same` to `sameChars` while there.

Other meaningless `go`s in the same file, each with an obvious name:
`:105` (`digitVal`'s) → `scanDigits`; `:114` (`number`'s) → `accumulate`;
`:168` (`posixName`'s) → `untilCloseBracket`; `:213` (`cat`'s) → `nextPiece`;
`:261` (`parseRE`'s) → inline it, the wrapper adds nothing over
`alt (suc (suc (length cs * 4)))`. And `Regex/Sat.agda:76` `go` →
`decideAt` (it dispatches on whether `P d` is `true`); `Unicode/Base.agda:75`
`go` → `weighted` (it carries the place value).

### S3.6 Fresh-alphabet + `matches` boilerplate duplicated three times

Identical `data L : Type ℓ-zero where a b : L`, `_≟L_`, `ℓr`, `matches`:

* `Regex/Tests.agda:15-29`
* `Backreference/RegexTests.agda:16-30`
* `Backreference/Stress/Common.agda:19-34`

plus `copyRE` appearing both at `RegexTests.agda:88` and `Stress/Common.agda:38`.

**Fix.** Subsumed by S1.3 if the tests move to `UChar`; otherwise one
`Theory/Instances/Monoid/Regex/TwoLetter.agda` exporting `L`, `_≟L_`, `ℓr`.

### S3.7 Two `RE?` types with two sets of smart constructors

`Regex/Parse.agda:34-67` defines `RE?`, `_⊗?_`, `_⊕?_`, `ε?`, `sat?`, `opt?`,
`star?`, `plus?`, `rep?`. `Regex/Derivative.agda:38-64` defines a second `RE?`,
`_⊗s_`, `_⊕s_`, `∅?`, `ε?`. `_⊗?_` and `_⊗s_` have literally the same body:

```agda
(n , r) ⊗? (n' , r') = n ·ν n' , r ⊗r r'      -- Parse.agda:42
(n , r) ⊗s (n' , r') = n ·ν n' , r ⊗r r'      -- Derivative.agda:61
```

Both files also re-export `Regex.Notation` `public`, so a module importing both
gets an ambiguous `RE?` and `ε?`.

**Fix.** Move `RE?`, `_⊗?_`, `_⊕?_`, `ε?`, `∅?` into `Regex/Base.agda` (they are
just the existential packing of the index) and have both consumers import them.
Keep `Derivative.agda`'s comment at `:55-59` — the argument for *not* making
`_⊗s_` smart is a good one and should survive the move.

---

## S4 — Low

### S4.1 Comments that restate the code

* `Regex/Derivative.agda:99-104` — two consecutive comment blocks that say the
  same thing: *"The smart constructors do not change the language. Confining the
  case analysis to these four lemmas is what keeps `δ-sound`/`δ-complete`
  structural."* then *"...so these are all the identity, and the theorem below
  never has to ask what a constructor did."* Merge into one.
* `Unicode/Base.agda:69-71` — *"Accumulator form, so the recursive call appears
  once. Measured: the duplicating form (`toNat bs + toNat bs`) is no slower, so
  Agda shares the thunk -- this is defensive, not a fix."* Three lines narrating
  a measurement that found nothing. Cut to *"accumulator form"*.
* `Regex/Notation.agda:35-37` and `:47-48` and `:64-65` and `:76-77` — four
  section banners on a 96-line file whose content is fifteen one-liners.
  `:59` (`-- no trailing `⊕r ⊥r` to explore`) is the only one that says
  something a reader could not see.
* `Backreference/Base.agda:44-45` — *"A `Σ` over a constant family is a `×`, so
  the two are the same type"* immediately above `⊗ᴰ-const = refl`.
* `Thompson/Construction/Bottom.agda:2-3` and `Epsilon.agda:2-3` — the headers
  describe five-field record literals that are self-evident.

### S4.2 Non-obvious steps with no comment

* `Regex/Base.agda:113` — `parse (r *r) ℓK = many ℓK ⟦ r ⟧ (parse▷ r (ℓ⊗ (ℓF (lv r)) ℓK) refl)`.
  The level argument `ℓ⊗ (ℓF (lv r)) ℓK` is the only place `ℓF` appears in a
  `parse` clause and it is not obvious why the continuation level has to absorb
  the star's own level. One line would fix it.
* `Regex/Sat.agda:44-52` (`sat⊗-precise`) — six lines of `t .snd .snd .snd .fst`
  projection chains with one comment. The `tails` equation is doing the real work
  and deserves a word about *why* `L.cons-inj₂` is the right injectivity.
* `Regex/Parse.agda:262` — `alt (suc (suc (AN._*_ (length cs) 4))) cs`. The fuel
  bound `4·|cs|+2` is a load-bearing magic number (too small and a valid pattern
  is rejected as malformed, which surfaces as a *type* error at the use site).
  Nothing says where the 4 comes from.
* `Backreference/Parser.agda:126-129` and `:156-159` — the
  `▷laxᴰ`/`&ᴰ-intro`/`π (l₁ ++ l₂)` sandwich is repeated verbatim in `seqDD` and
  `seqDᴰ` and is the hardest term in the file; neither copy is annotated. It is
  also a duplication (`seqDD B = seqDᴰ (λ _ → B)` should hold definitionally, by
  the same `⊗ᴰ-const` argument that justifies `toParser`) — worth checking, and if
  it holds, `seqDD` becomes one line.
* `Thompson/Base.agda:91` — `EquivPresIsFinOrd (invEquiv (isoToEquiv (satSTATE≅Fin2 P)) ∙ₑ LiftEquiv)`
  is the only clause with a `∙ₑ LiftEquiv`, because `satNFA` is the only automaton
  whose states are `Lift`ed. Unexplained.

### S4.3 File-top essays

`Backreference/StressTests.agda:2-27` is a 26-line header containing a table of
wall-clock timings *"Measured on this machine"* and a paragraph of interpretation.
The measurements are valuable but they are notes, not source, and they will rot
(the numbers are already unreproducible — S2.4 shows the controls that produced
them are not asserted). **Fix.** Move to `notes/`, or to a forest tree, and leave
a one-line pointer plus the invariant that actually matters
(*"asserts both polarities; a decider that ignored the backreference fails the
`nothing` cases"* — `:25-27`).

`Regex/Examples.agda:137-143` embeds a 7-line apology inside a test table
explaining that the `"wherever"` case is *wrong* and kept for contrast. Correct
call, but it belongs above the `passes` block, not inside the list — as written,
the list literal has a paragraph in the middle of it.

### S4.4 Scratch

* `Regex/Derivative.agda:185-187` — three consecutive blank lines between
  `Dl-map` and `δ-sound`.
* `Regex/Examples.agda:126` — `where import Cubical.Data.List as List` inside a
  `where` clause of a `private` definition, used once at `:125`. Move to the
  file's import block.
* `Thompson/Construction/Literal.agda` — `isSetSTATE` and `isDiscSTATE` (in the
  block deleted in the Sat clone, ~`:56-61`) have no use in the file or outside
  it; `Parse≅ = litNFA≅` at the end is a bare alias for the preceding definition.

No `postulate`, `TERMINATING`, `NON_TERMINATING`, `trustMe`, or commented-out
blocks were found anywhere in scope. `--allow-unsolved-metas` appears exactly
once (S2.5).

---

## S5 — Modularity

### S5.1 Over-broad `public` re-exports

`Regex/Base.agda:27-34` re-exports three whole modules:

```agda
open import Theory.Instances.Monoid.Combinator.Decidable.Star Alphabet _≟_ ℓ public
open import Theory.Instances.Monoid.KleeneStar.Guarded Alphabet isSetAlphabet public
open import Theory.Instances.Monoid.Regex.Sat Alphabet _≟_ ℓ using (…) public
```

Only the third has a `using` list. As a result `isSetAlphabet` — which is *not* a
parameter of `Regex/Base.agda` — is in scope at `:29` and `:31` purely as a
transitive re-export, as are `ℓG`, `ℓM`, `⊤Ty`, the whole parser-combinator
vocabulary, and `Suite`'s `passes`/`_at_`/`_↦_`. `Regex/Notation.agda:25` and
`Regex/Derivative.agda:36` and `Lex/Regex.agda:28` then re-export *that*
`public` again, so `Regex/Parse.agda:30`'s single import brings in essentially
the entire monoid theory. It works, but nothing in the chain declares what it
depends on, and S3.7's `RE?` ambiguity is a direct consequence.

**Fix.** Add `using` lists to `Regex/Base.agda:27` and `:29`. The `Decidable.Star`
surface actually needed is roughly `Parser`, `⟨▷⟩`, `⟨□⟩`, `mkP`, `nil`, `fail`,
`tok`, `seq`, `_<|>_`, `many`, `box`, `pmore`, `runP`, `Decidable`, `DecTy`,
`⊤Ty`, `⊢`, `∘⊢`, `id⊢`; from `KleeneStar.Guarded` it is `roll↑`, `unroll↑`,
`StarSet`, `¬Nullable` and friends.

### S5.2 Oversized files

`Thompson/Construction/LinearProduct.agda` (544) and `KleeneStar.agda` (512) are
each one `module _ (N : NFA ℓN) …` containing the automaton, the forward fold,
the backward fold, the equalizer argument, and the iso. The natural cut is at the
equalizer: `nested-induction` (`KleeneStar.agda:422-455`) and everything it needs
(`C⟜`, `nL`, `nR`, `Eqr`, `eqπ`, `U-*`, `nA`…`sE`) is a self-contained ~150-line
argument that would read better as `Construction/KleeneStar/Section.agda`, with
`KleeneStar.agda` keeping the automaton + `*NFA≅`. Same cut in `LinearProduct.agda`
at `:379-510`.

### S5.3 Tests living at the bottom of definition files

`Phase/Display.agda:~280-323` ends with `module Demo` and `module RegexDemo`,
including `_ : display (text "x1_") parsed ≡ "x1_"`. That is a test module inside
a 323-line definitions file — it should be `Phase/DisplayTests.agda`. Flagged
here because it is the *only* place a display action is actually exercised, and
S1.3's fix wants to import it.

Nothing else in scope has this problem: `Regex/{Tests,ParseTests,UnicodeTests}`,
`Backreference/{RegexTests,StressTests}` are all correctly separated — their
problem is content (S1.3), not location.

---

## Summary of proposed new/moved files

| new file | absorbs |
| --- | --- |
| `Regex/Nullability.agda` | `Regex/Base.agda:39-58`, `Backreference/Regex.agda:37-55` (S2.1) |
| `Regex/Harness.agda` | the five ad-hoc `matches`/`yes`/`no` (S1.3) |
| `Thompson/Construction/OneStep.agda` | `Construction/Literal.agda` ∩ `Construction/Sat.agda` (S1.4) |
| `Thompson/Construction/Finiteness.agda` | three `the-dec-prop` + two inline (S3.3) |
| `Phase/DisplayTests.agda` | `Phase/Display.agda`'s two `Demo` modules (S5.3) |

| delete | reason |
| --- | --- |
| `src/Lex/Det/Eval.agda` | timing probe, no assertion (S2.5) |
| `src/Lex/Det/Base.agda`, `src/Thompson/**` | superseded; unblock by porting `Examples/{RegexParser,Benchmark/Dyck}` (S2.5, S2.6) |
| 9 defs in `Backreference/Stress/Common.agda` | unreferenced (S2.4) |
| `Regex/Derivative.agda`'s `Dl-⊕-*`, `Dl-map` | already in `Derivative{,/General}.agda` (S2.2) |
