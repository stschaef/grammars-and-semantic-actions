# Test / example / demo audit — `grammars-and-semantic-actions`

Read-only survey of `src/**` (excluding `src/_build/**`), branch `theory-core`,
371 `.agda` files. Every claim below carries a path; line numbers are given
wherever they matter.

> **The repo changed while this audit ran.** Three things landed on disk during
> the survey and are reflected below: `Suite.rejects` was added
> (`Theory/Type/SemanticAction/Base.agda:52-54`); `STLC.agda` shrank from 2008
> to 1121 lines (line numbers in §B.1 are post-edit); and
> `Theory/Type/Decidable/DiscreteEq.agda` appeared, which addresses §C.3. The
> file census itself is unchanged — no test file was added or removed.

The maintainer's brief is `review.md:41-67` ("# Tests"), quoted in full at the
end of §0 so the criteria are not paraphrased.

---

## 0. The three criteria, as they stand today

### 0.0 The brief (`/home/steven/grammars-and-semantic-actions/review.md:41-67`)

> concrete test modules should follow this rough skeleton
> 1. Use the unicode lexer so that the input is human readable
> 2. Use the uniform testing interface `passes` and `rejects` (does this
>    exist?) found in `Theory.Type.SemanticAction.Base`. Check that these
>    test case helpers aren't duplicated
> 3. When writing the correct output, be sure to use a semantic action
>    to display human-readable output. I think there may be some
>    outstanding work on writing "display" semantic actions for each
>    type to give a canonical output
> …
> This means we should move any tests/examples that are at the bottom of a
> definitions file into its own test file for readability
> We should also sometimes have stress test files that push the input size up
> so that we can test how long typechecking time gets for large inputs

Related, from the same file: `review.md:22-33` asks specifically that the
Lambda/STLC tests "use the unicode lexer, parse these into lambda terms, scope
check these lambda asts, and then type check".

---

### 0.1 Criterion 1 — the unicode lexer

There are **two** relevant modules, and they are complementary:

**`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Unicode/Base.agda`** — the alphabet.
* `Bits : ℕ → Type` (:35), `UChar = Bits 21` (:59) — a code point as 21 structural
  bits, so `_≟U_` (:62) reduces to `Eq.refl` instead of going through
  `String.Unicode`'s postulated path oracle (see the header comment, :2-9).
* `ch : AC.Char → UChar` (:88) — a character literal enters.
* `text : AS.String → List UChar` (:95) — **"text enters the theory here and
  nowhere else"**. This is the input side of the skeleton.
* `unch` (:98) / `untext : List UChar → AS.String` (:101) — **"…and leaves here,
  which is what lets a test state its result as text"**. This is the *fallback*
  output side (see §0.3: `Display` is the real one).

**`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Regex/Unicode.agda`** — POSIX classes at `UChar`.
* re-exports `Unicode.Base` and `Regex.Notation UChar _≟U_` publicly (:16-19).
* character predicates `isDigit/isAlpha/isAlnum/isSpace/isPunct/isWord/…`
  (:38-58) and the matching regexes `digitR/alphaR/…/dotR` (:60-96).
* `bracketR` / `bracketNotR` over `Item` (:98-124) — `[abc0-9[:alpha:]]`.
* `strU : (w : AS.String) → RE (nullb (text w))` (:127-129) — a literal word
  written as text: `strU "let"` rather than `strr (ch 'l' ∷ ch 'e' ∷ ch 't' ∷ [])`.

**How a test is *meant* to use them.** The one file in the repo that does it
end-to-end is
`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Regex/Examples.agda`.
The recipe, with its line numbers:

1. Open `Unicode.Base` and `Regex.Parse` (:26-27) — `Regex.Parse` gives `reOf`,
   the POSIX-string → `RE` elaborator, so a *pattern* is also written as text:
   `ident = reOf "[[:alpha:]_][[:alnum:]_]*"` (:51).
2. Build the decision: `decide-r r ℓr : Decidable (ty ⟦ r ⟧)`.
3. Run it at a **`text`-lexed** input and observe with a semantic action:
   `matched r = λ w → observe (decide-r r ℓr) (semact-dec (yield r)) (text w)` (:40-41).
4. Bring the answer back to text: `show (M.just cs) = M.just (untext cs)` (:44-46).
5. State the table with `passes`/`_at_`/`_↦_` (:58-93).

For a *lexer* (many rules), the second half of the same file (:99-149) shows the
shape: a `Lexicon` written as a list of `reOf "…"` (:106-113), a `name : ℕ × List
UChar → Tok` that maps rule index + lexeme to a token (:116-121), and
`lex w = observe (lexer lexicon) (semact-dec (semact-map (List.map name) (tokens lexicon))) (text w)` (:123-125).
Then the table is literally
`"let x = 42" ↦ M.just (KW "let" ∷ WS ∷ Ident "x" ∷ …)` (:129-149).

The `yield`/`which`/`tokens` semantic actions this relies on live at
`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Lex/Regex.agda:65-90`.

**Adoption today: 6 files out of 371 write any `text "…"` input.**

| file | `text "…"` occurrences |
|---|---|
| `src/Theory/Instances/Monoid/Automaton/Implicit/AnalysisExamples.agda` | 20 |
| `src/Theory/Instances/Monoid/Greedy/Examples.agda` | 15 |
| `src/Theory/Instances/Monoid/Regex/Examples.agda` | 6 |
| `src/Theory/Instances/Monoid/Phase/Display.agda` | 5 |
| `src/Theory/Instances/Monoid/Automaton/LexiconExamples.agda` | 4 |
| `src/Theory/Instances/Monoid/Automaton/TokenStreamExamples.agda` | 1 |

Against that, **27 files** contain at least one four-element-or-longer raw cons
list `x ∷ y ∷ z ∷ w ∷ []` as test input (top offenders: `Combinator/Decidable/Arrow.agda` 20,
`Combinator/Grammars/ArithTests.agda` 14, `Backreference/RegexTests.agda` 12,
`Combinator/Grammars/PolynomialTests.agda` 11, `Combinator/Decidable/WidthsTests.agda` 10,
`Combinator/Decidable/Arith.agda` 10, `Examples/Benchmark/Dyck.agda` 10).

A second, *independent* Unicode-lexing stack exists in the paper tree:
`/home/steven/grammars-and-semantic-actions/src/Examples/Benchmark/Dyck.agda:106-164`
hand-rolls `litAut`/`⊕Aut`/`LexRule`/`Lexicon`/`runLex` over `String.Unicode` to
obtain `fromString : AS.String → String` (:163). This duplicates `text` and does
not share an alphabet with the `Theory/` tree.

---

### 0.2 Criterion 2 — the uniform testing interface

**File: `/home/steven/grammars-and-semantic-actions/src/Theory/Type/SemanticAction/Base.agda`.**

> **Note, mid-audit.** When this audit started, `module Suite` was lines 34–48
> and `rejects` did **not** exist. It was added to disk while the audit ran and
> is now `Base.agda:50-54`. Both states are recorded below, because the
> migration plan depends on knowing that `rejects` has **zero users** and one
> immediate name clash.

`module Suite` is lines **34–54**, followed by `open Suite public` at :56.
Verbatim, that is the *whole* of it:

```agda
module Suite where
  Case : Type ℓX → Type ℓX                                          -- :35
  Case X = X × X                                                    -- :36

  infix 6 _↦_                                                       -- :38
  _↦_ : {W : Type ℓY} {X : Type ℓX} → W → X → W × X                 -- :39
  w ↦ x = w , x                                                     -- :40

  passes : {X : Type ℓX} → List (Case X) → Type ℓX                  -- :42
  passes cs = List.map fst cs ≡ List.map snd cs                     -- :43

  infix 3 _at_                                                      -- :45
  _at_ : {W : Type ℓY} {X : Type ℓX}                                -- :46
    → (W → X) → List (W × X) → List (Case X)                        -- :47
  f at cs = List.map (λ c → f (c .fst) ↦ c .snd) cs                 -- :48

  -- The negative suite.  A pass that refutes reports `nothing`, so a       :50
  -- rejection needs no expected value and the inputs are listed bare.      :51
  rejects : {W : Type ℓY} {X : Type ℓX}                             -- :52
    → (W → M.Maybe X) → List W → Type ℓX                            -- :53
  rejects f ws = passes (f at List.map (_↦ M.nothing) ws)           -- :54
```

Outside `Suite` but in the same file and relied on by every test:
`Δ` (:58), `SemanticAction` (:61), **`run` (:64)** and **`observe` (:67)** — note
that `run`/`observe` are *not* inside `module Suite`; they are top-level.
Everything from `semact-pure` (:71) down is the action algebra.

**Answering the maintainer's parenthetical directly:**

* `Case`, `_↦_`, `passes`, `_at_` — **exist** (and always did).
* `run`, `observe` — **exist**, at module level, not in `Suite`.
* **`rejects` did not exist when this audit began; it exists now** at
  `Base.agda:52-54`, exactly as proposed below. It has **zero call sites**:
  `grep -rn '\brejects\b' src --exclude-dir=_build` returns only its own
  definition, prose comments, and the two *shadowing* lemma names below.
* **`accepts` still does not exist** as a combinator, which leaves the positive
  side asymmetric with the negative one (see the proposal below).
* The name `rejects` is **already taken, twice, as a top-level test-lemma name**
  in the `accepts : passes (…) / rejects : passes (…)` idiom:
  `/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Combinator/Decidable/ListLit.agda:61,70`
  and
  `/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Combinator/Incomplete/ListLit.agda:66,75`.
  Both files reach `Suite` through `Combinator/*/Star.agda → …/Base.agda →
  Theory.Instances.Monoid.SemanticAction:19 → Suite`, so the new combinator and
  the old lemma name now collide in the two files that were closest to the
  target style. They only survive because neither file *uses* the name after
  defining it. **Rename both pairs before anything else lands.**
* `accepts` is also taken as a local helper at
  `.../Automaton/Implicit/RegExpExamples.agda:87` and
  `.../Automaton/Implicit/AnalysisExamples.agda:62` (both `: String → Bool`),
  so adding a `Suite.accepts` will collide there too.

**Reach.** `Suite` is re-exported publicly by
`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/SemanticAction.agda:19`
(`open import Theory.Type.SemanticAction.Base … public`), which is in turn
re-exported by each `Combinator/*/Base.agda`, so a test in the Monoid tree gets
`passes`/`at`/`↦` for free. There is a recorded name hazard at
`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Types.agda:42`:
*"`at` clashes with the `_at_` of `SemanticAction`, which every test uses"* (the
other `at` being `Theory/Type/Decidable/Base.agda:49`).

**Adoption today: 11 files use `passes`.**
`Regex/Examples.agda`, `Combinator/Decidable/{Dyck,ListLit}.agda`,
`Combinator/Incomplete/{Dyck,ListLit}.agda`,
`Combinator/Grammars/{Arith,Dyck,Polynomial,Regex}Tests.agda`,
`Bags/Quicksort/Tests.agda` (no — see §A), and that is it. Of the
~430 test cases counted in §A, roughly 190 go through `passes`; the rest are
ad-hoc `_ : f x ≡ y ; _ = refl` or `theYes/theNo … Eq.refl` witnesses.

#### The missing half: `accepts`

`rejects` as landed is the right shape. Its counterpart is not there, so a
positive table still has to spell `M.just` on every line
(`Regex/Examples.agda:58-93` does exactly this, 24 times). `Cubical.Data.Maybe`
is already imported as `M` (:18), so add, immediately after `rejects`:

```agda
  -- The affirming side, dual to `rejects`.  `f` is a decision read through
  -- `semact-dec`, so its `nothing` is a refutation and not a dropped error;
  -- a case is written "input ↦ what the display action prints", with the
  -- `just` supplied here rather than at every line of every table.
  accepts : {W : Type ℓY} {X : Type ℓX}
    → (W → M.Maybe X) → List (W × X) → Type ℓX
  accepts f cs = passes (f at List.map (λ c → c .fst ↦ M.just (c .snd)) cs)
```

It lands in `Type ℓX` exactly as `passes`/`rejects` do, so it composes with the
existing `open Suite public`. A test then reads

```agda
_ : accepts (displayDec decIdent)
      ( "buffer_size" ↦ "buffer_size"
      ∷ "x"           ↦ "x"
      ∷ [] )
_ = refl

_ : rejects (displayDec decIdent) ( "2fast" ∷ "" ∷ [] )
_ = refl
```

which is the whole skeleton in four lines. If a `Bool`-valued variant is wanted
for the `accepts : String → Bool` helpers in `Automaton/Implicit/*Examples.agda`,
add `passesTrue f ws = List.map f ws ≡ List.map (λ _ → true) ws` rather than
letting each file define its own.

Two smaller gaps worth closing at the same time:

* `Suite` has no way to *name* a suite, so every table is an anonymous `_ : …`.
  A `Suite`-level `Named : AS.String → Type ℓX → Type ℓX` is not needed —
  naming the lemma (`idents-accept : accepts …`) is enough — but the repo is
  currently split 50/50 between anonymous and named and should pick one
  (recommend **named**, so a CI failure says which table broke).
* There is no shared refutation helper for the *metalanguage* `Dec`, which is
  why `STLC.agda:1051-1061` re-implements `isYes`/`theYes`/`theNo` as
  `isYesD`/`theD`/`theNotD` (see §B.1 and §C.1).

---

### 0.3 Criterion 3 — display semantic actions

**The machinery exists and is good. It has zero test-file users.**

* `record Display (A : TheoryTy ℓA tt)` with field `shown : SemanticAction A AS.String`
  — `/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Phase.agda:102-105`,
  plus `displayOf` (:107). The header comment at :96-100 states the intent
  exactly as the maintainer does: *"a test says `display (run p input)` rather
  than reaching into the parse by hand; the point is that a test can only print
  what the grammar actually says."*
* The instances —
  `/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Phase/Display.agda`,
  `module Displays` (:40) parameterised by `showA : Alphabet → AS.String`:

  | connective | instance | line |
  |---|---|---|
  | `εTy` | `Display-εTy` | :70 |
  | `＂ c ＂` | `Display-lit` | :74 |
  | `char` | `Display-char` | :78 |
  | `A ⊗ B` | `Display-⊗` | :82 |
  | `A ⊕ B` | `Display-⊕` | :89 |
  | `A *` | `Display-*` | :95 |
  | `⊤Ty` | `Display-⊤Ty` | :102 |
  | `⊥Ty` | `Display-⊥Ty` | :107 |
  | `LiftTheoryTy` | `Display-Lift` | :110 |
  | `String*` | `Display-String*` | :119 |
  | `satTy P` | `Display-satTy` (in `module SatDisplay`, :174) | ~:181 |
  | `⊕[ y ∈ Y ] A y` | **deliberately not an instance**; `displayΣ` (:135) / `displayΣ-tagged` (:140) passed explicitly, with the reason recorded at :122-133 |

  The boundary functions are `display` (:153) and `displayDec` (:160), the
  latter being `runPhase` with the canonical emission — i.e. *exactly* the
  `W → M.Maybe AS.String` that the proposed `accepts`/`rejects` want.

* The comment at `Phase/Display.agda:114-118` is the key limitation, stated by
  its own author: **every hand-written `μ` needs its own instance**, and it names
  the ones that do not resolve today — `Examples.Dyck`, `Grammars.Dyck`, the NFA
  `Trace`.

**Which types have a display today**

| subsystem | has a display action? | where |
|---|---|---|
| the monoid connectives (`ε`,`lit`,`char`,`⊗`,`⊕`,`*`,`⊤`,`⊥`,`Lift`,`String*`) | **yes**, instance-resolved | `Phase/Display.agda:68-120` |
| `satTy P` / any `ty ⟦ r ⟧` for a regex `r` | **yes** | `Phase/Display.agda:174-181` |
| `⊕[ y ∈ Y ] A y` | manual, by design | `Phase/Display.agda:135-144` |
| regexes, as "what did it match" | **yes, but a second implementation** — `yield`/`which`/`tokens` | `Theory/Instances/Monoid/Lex/Regex.agda:65,80,88` |
| automaton runs, as "what word did it read" | **yes, but not a `Display`** — `print : Trace b q ⊢ char *` with a uniqueness proof | `Theory/Instances/Monoid/Automaton/Print.agda:36-58`; older copies at `src/Automata/Deterministic.agda:92-98` and `src/Automata/Implicit.agda:247-262` |
| Dyck (`Theory/Instances/Monoid/Grammars/Dyck.agda`) | **no** — `semactS` yields the `Dyck` ADT, tests print the ADT | see §A row |
| Dyck (`src/Examples/Dyck.agda`) | **no** — `abstractify : Dyck ⊢ Δ DyckAST` in `Examples/Benchmark/Dyck.agda:57` |
| BinOp (`src/Examples/BinOp.agda`) | **no** — `abstractify` in `Examples/RecursiveDescent/BinOp.agda:180` |
| STLC types `ATy` / terms `ATm` | **no** — expected values are raw ADT constructors |
| token streams (`Automaton/TokenStream.agda`, `Automaton/Lexicon.agda`) | **no `Display`**; they have an ad-hoc "display boundary" returning `List (ℕ × String)` — `TokenStream.agda:136,457`, `Lexicon.agda:284,294,317` |
| NFA/DFA `Trace` (`Theory/Instances/Monoid/Automata/**`) | **no** |
| Bags / `Sorted` / `Seq` | **no `Display`**; `elements : Seq m → List ℕ` plays the role — `Bags/Quicksort/Tests.agda:71` |
| backreference grammars (`REB`) | **no** — every test's expected value is `M.just tt` |
| parser-combinator answers (`Decidable`/`Incomplete`/`NonDet`) | **no** — every test's expected value is `M.just tt`, `M.nothing` or a raw tree |

Grep evidence that no test uses it:
`grep -rn 'Display\|mkDisplay\|displayDec\|\bdisplay\b' src --exclude-dir=_build`
returns hits **only** inside `Phase.agda` / `Phase/Display.agda` plus six prose
comments elsewhere. `Phase/Display.agda`'s own `module Demo` (:192-300) and
`module RegexDemo` (:303-323) are the only exercises of it — 7 assertions, and
5 of the 7 hand-construct their *input* parse tree (see §B.3).


---

## A. Census

**37 files contain test cases** (~600 individual assertions / `↦` rows), plus
one test-fixture module with no assertions of its own
(`Backreference/Stress/Common.agda`). Split:

* **23 dedicated test/example/demo files**
* **14 definitions files with tests appended at the bottom** — the ones the
  maintainer wants moved out.

**Files satisfying all three criteria: zero.**
Best in class is
`/home/steven/grammars-and-semantic-actions/src/Theory/Instances/Monoid/Regex/Examples.agda`
(C1 ✓, C2 ✓, C3 via a *local* `show`, not the `Display` class).

Legend: **C1** = input written as `text "…"` through the Unicode lexer;
**C2** = `passes`/`_at_`/`_↦_` from `Suite`; **C3** = expected output produced by
a display/print semantic action (✓ = the `Display` class; ~ = an ad-hoc
`untext`/`show`/`abstractify` action; ✗ = raw value comparison).

### A.1 Dedicated test / example / demo files (23)

| # | path | lines | ≈cases | C1 | C2 | C3 |
|---|---|---|---|---|---|---|
| 1 | `src/Theory/Instances/Bags/Quicksort/Tests.agda` | 76–123 | 10 | ✗ (`∷ᵍ` bag literals, ℕ) | ✗ ad-hoc `_ = refl` | ~ `elements` (`sort`, :73) |
| 2 | `src/Theory/Instances/Monoid/Automaton/Demo.agda` | 88–129, 147–148 | 13 | ✓ `lex "…"` | ✗ | ~ `untext` (:79) |
| 3 | `src/Theory/Instances/Monoid/Automaton/GreedyExamples.agda` | 50–72 | 4 | ✗ raw `L2` | ✗ | ✗ |
| 4 | `src/Theory/Instances/Monoid/Automaton/GreedyMaxExamples.agda` | 39–83 | 8 | ✗ raw `L2` | ✗ | ✗ |
| 5 | `src/Theory/Instances/Monoid/Automaton/Implicit/AnalysisExamples.agda` | 74–212 | 31 | ✓ `text "…"`, `POSIX "…"` | ✗ | ✗ (type-level `Trace` witness) |
| 6 | `src/Theory/Instances/Monoid/Automaton/Implicit/RegExpExamples.agda` | 94–134 | 8 | ✗ hand-built `L2` automaton | ✗ | ✗ (`Bool`) |
| 7 | `src/Theory/Instances/Monoid/Automaton/Implicit/SoundnessExamples.agda` | 30–64 | 4 | ✗ raw `DetReg` towers | ✗ | ✗ |
| 8 | `src/Theory/Instances/Monoid/Automaton/LexiconExamples.agda` | 69–162 | 19 | ✓ `lexS "…"` | ✗ | ~ `untext` (:63,:119) |
| 9 | `src/Theory/Instances/Monoid/Automaton/TokenStreamExamples.agda` | 92–147 | 12 | ✓ | ✗ | ~ `untext` (:79,:84,:135) |
| 10 | `src/Theory/Instances/Monoid/Automaton/ScratchPerf.agda` | 61–62 | 1 | ✓ (`POSIX`, `ch 'a'`) | ✗ | ✗ |
| 11 | `src/Theory/Instances/Monoid/Regex/Tests.agda` | 36–185 | 31 | ✗ 2-letter `data L` | ✗ | ✗ (`Maybe Unit`) |
| 12 | `src/Theory/Instances/Monoid/Regex/ParseTests.agda` | 40–133 | 29 | ✓ `text w` + POSIX source strings | ✗ (local `Yes/No/yes/no`) | ✗ |
| 13 | `src/Theory/Instances/Monoid/Regex/UnicodeTests.agda` | 45–135 | 18 | ✓ | ✗ (local `Yes/No/yes/no`) | ~ one `readIdent` action (:62–74) |
| 14 | `src/Theory/Instances/Monoid/Regex/Examples.agda` | 49–166 | 24 rows + 3 witnesses | ✓ | **✓** (6 `passes` tables) | ~ local `show` (:44) + `untext` |
| 15 | `src/Theory/Instances/Monoid/Backreference/RegexTests.agda` | 32–117 | 20 | ✗ 2-letter `data L` | ✗ | ✗ (`Maybe Unit`) |
| 16 | `src/Theory/Instances/Monoid/Backreference/StressTests.agda` | 35–69 | 9 | ✗ (128-element cons lists) | ✗ | ✗ |
| 17 | `src/Theory/Instances/Monoid/Greedy/Examples.agda` | 64–146 | 7 | ✓ `text "aaa"` | ✗ | ~ `untext` |
| 18 | `src/Theory/Instances/Monoid/KleeneStar/GuardedTests.agda` | 42–52 | 4 | ✗ 2-letter `data L` | ✗ | ✗ (`Maybe ℕ`) |
| 19 | `src/Theory/Instances/Monoid/Combinator/Grammars/ArithTests.agda` | 42–111 | 42 rows / 3 tables | ✗ abstract `Tok` | **✓** (opened :52) | ✗ (`Maybe Unit`) |
| 20 | `src/Theory/Instances/Monoid/Combinator/Grammars/DyckTests.agda` | 35–85 | 15 rows / 3 tables | ✗ `lp ∷ rp ∷ []` | **✓** (opened :45) | ✗ (raw `Dyck` ASTs) |
| 21 | `src/Theory/Instances/Monoid/Combinator/Grammars/PolynomialTests.agda` | 49–125 | 45 rows / 3 tables | ✗ `Bool` alphabet | **✓** (opened :59) | ✗ (`Maybe Unit`) |
| 22 | `src/Theory/Instances/Monoid/Combinator/Grammars/RegexTests.agda` | 50–128 | ~18 / 6 tables | ✗ `Two` alphabet | **✓** (opened :46) | ✗ (raw `Sum` trees) |
| 23 | `src/Theory/Instances/Monoid/Combinator/Decidable/WidthsTests.agda` | 19–74 | 14 | ✗ `ta ∷ tc ∷ []` | ✗ `theYes`/`theNo` | ✗ |

Fixture, no assertions:
`src/Theory/Instances/Monoid/Backreference/Stress/Common.agda` (alphabet
`L`/`_≟L_` :19–25, `matches` :33, and the ten stress patterns :36–122).

### A.2 Definitions files with tests appended at the bottom (14) — **all must move**

| # | path | file len | test lines | ≈cases | C1 | C2 | C3 | proposed destination |
|---|---|---|---|---|---|---|---|---|
| 24 | `src/Theory/Instances/Monoid/Combinator/Decidable/Dyck.agda` | 65 | 28–65 | 12 | ✗ | ✓ (mixed with `theNo` at :31–34) | ✗ | `Combinator/Decidable/DyckTests.agda` |
| 25 | `src/Theory/Instances/Monoid/Combinator/Decidable/ListLit.agda` | 78 | 58–78 | 9 | ✗ | ✓ | ✗ | `Combinator/Decidable/ListLitTests.agda` |
| 26 | `src/Theory/Instances/Monoid/Combinator/Decidable/Arith.agda` | 102 | 33–102 | 20 (incl. a scale section :78–102) | ✗ | ✗ `theYes`/`theNo` | ✗ | `Combinator/Decidable/ArithTests.agda` + `ArithStress.agda` |
| 27 | `src/Theory/Instances/Monoid/Combinator/Decidable/Arrow.agda` | 328 | 263–328 | 15 | ✗ | ✗ | ✗ | `Combinator/Decidable/ArrowTests.agda` |
| 28 | `src/Theory/Instances/Monoid/Combinator/Decidable/Lambda.agda` | 98 | 69–98 | 9 | ✗ | ✗ | ✗ | `Combinator/Decidable/LambdaTests.agda` |
| 29 | `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda` | 1121 | 235–358, 556–612, 1063–1121 | ~57 | ✗ (own `Src` token DSL, ~:170–232) | ✗ | ✗ | `Combinator/Decidable/STLCTests.agda` |
| 30 | `src/Theory/Instances/Monoid/Combinator/Incomplete/Dyck.agda` | 52 | 26–52 | 10 | ✗ | ✓ | ✗ | fold into `Combinator/Grammars/DyckTests.agda` |
| 31 | `src/Theory/Instances/Monoid/Combinator/Incomplete/ListLit.agda` | 83 | 57–83 | 9 | ✗ | ✓ | ✗ | fold into one `ListLitTests.agda` |
| 32 | `src/Theory/Instances/Monoid/Pipeline/Dyck.agda` | 153 | 100–153 | 15 | ✓ `lex "(())"` | ✗ | ✗ (raw `Result`/`Dyck`) | `Pipeline/DyckTests.agda` |
| 33 | `src/Theory/Instances/Monoid/Phase/Display.agda` | ~325 | 192–300 (`module Demo`), 303–323 (`module RegexDemo`) | 7 | ✓ | ✗ | **✓ the only `Display` user** | `Phase/DisplayTests.agda` |
| 34 | `src/Examples/Benchmark/Dyck.agda` | ~415 | 190–200 (commented), 202–346, 348–415 | 20 live + 14 commented | ~ own lexer (`fromString`, :163) | ✗ | ~ `abstractify` (:57) | `Examples/Benchmark/DyckStress.agda` |
| 35 | `src/Examples/RecursiveDescent/BinOp.agda` | ~270 | 190–270 | 20 | ✗ raw `num 1 ∷ + ∷ …` | ✗ | ~ `abstractify` (:180) | `Examples/RecursiveDescent/BinOpTests.agda` |
| 36 | `src/Examples/RecursiveDescent/Dyck.agda` | ~175 | 136–175 | 11 | ~ borrows `fromString` from #34 | ✗ | ~ `abstractify` | `Examples/RecursiveDescent/DyckTests.agda` |
| 37 | `src/String/ASCII/Base.agda` | ~186 | 185–186 | 1 (`_ : 97 ≡ length translation`) | n/a | ✗ | n/a | leave in place, or `String/ASCII/Tests.agda` |

### A.3 Confirmed test-free (so the census is complete)

Whole trees with **zero** test cases: `src/Automata/**` (12 files),
`src/Grammar/**` (~150 files), `src/Term/**`, `src/Parser/**`, `src/Cubical/**`,
`src/Lex/**`, `src/Thompson/**`, `src/Determinization/**`,
`src/Theory/Type/**` (46 files — `Type/SemanticAction/Base.agda` *defines* the
harness but asserts nothing), `src/Theory/Free/**`, `src/Theory/Base.agda`,
`src/Theory/Instances/{Lambda,STLC}/**`,
`src/Theory/Instances/Monoid/Automata/**` (DFA/Base, NFA/Base, NFA/Properties),
`src/Theory/Instances/Monoid/Thompson/**` (12 files),
`src/Theory/Instances/Monoid/{Derivative,Determinization,Lookahead,Residual,SequentialUnambiguity,Suffix}/**`,
and every top-level `src/Theory/Instances/Monoid/*.agda`.

Notable, because the names mislead:

* `src/Theory/Instances/Monoid/Examples.agda` (49 lines) is **not** an example
  file — it is definitions only (`LiteralStar`, `DyckCode`, `Dyck`,
  `dyck-NIL`/`dyck-BALANCED`). It should be renamed (`Grammars/Fixtures.agda`
  or merged into `Grammars/Dyck.agda`).
* `src/Examples/Dyck.agda` (652 lines) and `src/Examples/BinOp.agda` (693
  lines) — the two largest example grammars, with full soundness/completeness
  proofs — have **no executable tests of their own**; all their testing lives in
  the three `RecursiveDescent`/`Benchmark` files.
* `src/Examples/Section2/{Alphabet,Figure1,Figure3,Figure4,Figure5}.agda` are
  paper figures with **no assertions at all** (Figure5 is a 312-line NFA
  equivalence proof).
* `src/Theory/Instances/Monoid/Lex/Base.agda:43` defines
  `lexTest : Test (ty Tokens)` — **production code**, not a test. `Test` is the
  answer-functor type `Test A = ⊤Ty ⊢ Maybe A`
  (`Combinator/Incomplete/Base.agda:131-132`). This name should be changed
  (`Attempt`, `Recognizer`) before "Tests" becomes the file-naming convention,
  or every grep for tests will hit it.


---

## B. Violations — tests that are unreadable in the maintainer's sense

The forbidden shape has two independent faults, and they occur separately as
well as together:

* **(i) raw AST / raw constructor input** instead of lexed concrete syntax;
* **(ii) ad-hoc refutation** (`theNotD … Eq.refl`, `theNo … Eq.refl`,
  `_ : … ≡ M.nothing`) instead of a uniform `rejects`.

### B.1 The exact case cited, and its neighbours — `Combinator/Decidable/STLC.agda`

The cited line is real and reads, verbatim:

```
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:1114
  badApp-refuted : Ty? [] (App (Lam vx Na (Nm vx)) Tru) → Empty.⊥
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:1115
  badApp-refuted = theNotD (typed? [] (App (Lam vx Na (Nm vx)) Tru)) Eq.refl
```

Its siblings in the same block (`:1063-1121`), all with the AST written **twice**,
once in the type and once in the body:

```
:1082  unbound-refuted = theNotD (scoped? [] (Nm vx)) Eq.refl
:1085  bound-scoped : Scoped [] (Lam vx Na (Nm vx))
:1109  badIf-refuted = theNotD (typed? [] badIfAST) Eq.refl
:1111  badSuc-refuted : Ty? [] (Suc Tru) → Empty.⊥
:1117  badCons-refuted : Ty? [] (Cons Tru (Nil Na)) → Empty.⊥
:1120  badFst-refuted : Ty? [] (Fst Zer) → Empty.⊥
```

`theNotD` itself is the ad-hoc part. `STLC.agda:1051-1061` re-implements
`isYes`/`theYes`/`theNo` (`Theory/Type/Decidable/Base.agda:77,81,74`) for
`Cubical`'s metalanguage `Dec`:

```
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:1051  isYesD : {A : Type ℓ-zero} → Dec A → Bool
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:1055  theD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ true → A
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:1059  theNotD : {A : Type ℓ-zero} (d : Dec A) → isYesD d Eq.≡ false → A → Empty.⊥
```

The irony is that the same file *already has* a concrete-syntax DSL
(`Src`, `` `λ_∶_∙_ ``, `` `if_`then_`else_ ``, `` `let_≔_`in_ ``, ~:170-232)
and uses it for the positive cases (`idSrc` :250, `addSrc` :265, `fibSrc`
:278, `sumSrc` :294) — and then abandons it for the negative ones:

```
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:319
  no-bare-lam : ¬Ty Term (klam ∷ vx ∷ kdot ∷ vx ∷ [])
  no-bare-lam = theNo (parseTm (klam ∷ vx ∷ kdot ∷ vx ∷ []) tt) Eq.refl
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:323
  no-half-if : ¬Ty Term (kif ∷ ktrue ∷ kthen ∷ kzero ∷ [])
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:327
  no-short-natrec : ¬Ty Term (knatrec ∷ kzero ∷ kzero ∷ [])
src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:331
  no-kw-type : ¬Ty Type′ (karr ∷ knat ∷ ktrue ∷ [])
```

Nothing in the file lexes text: there is no `String → List Tok`. `review.md:22-33`
asks for exactly that.

### B.2 The single worst offender by size — `Backreference/StressTests.agda`

`src/Theory/Instances/Monoid/Backreference/StressTests.agda:36` is a **128-element
hand-written cons list on one physical line (~1.1 kB)**:

```
_ : matches copyRE (a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ b ∷ b ∷ a ∷ b ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ a ∷ a ∷ b ∷ b ∷ b ∷ a ∷ … ∷ []) ≡ M.just tt
_ = refl
```

Same shape at `:40` (128), `:44` (128), `:48` (64 `a`s), `:52` (32 `a`s), `:64`
(20 `a`s), `:68` (13). `Stress/Common.agda:56` already defines `repA` for the
*pattern* side but nothing generates the *input* side, so runs of 64 identical
letters are typed out. The whole file could be `text "abbaab…"` at a two-letter
sub-alphabet of `UChar`, or `rep 128 (…)` — either removes 5 kB of source.

### B.3 Raw parse trees pasted from the typechecker — `Examples/Benchmark/Dyck.agda`

`src/Examples/Benchmark/Dyck.agda:255` is a 38-line hand-pasted *normalised
parse tree*, full of `μ.roll`, splitting witnesses and `Eq.refl`:

```
  _ : D.parse? (mkInput 4)
  _ = Sum.inl
       (μ.roll (LP ∷ LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ RP ∷ [])
        (balanced' ,
         ((LP ∷ [] , LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ RP ∷ []) , Eq.refl) ,
         lift Eq.refl ,
         ((LP ∷ LP ∷ RP ∷ LP ∷ RP ∷ RP ∷ [] , RP ∷ []) , Eq.refl) , …
```

The comment at `:243-245` admits the provenance: *"the below is written by
starting with `? , refl` and then `C-u C-u C-c C-s` to solve for the normalized
parse trees"*. The comment at `:341-344` records that the same trick for
`mkInput 10` "takes 3000 lines to display" and was abandoned. `:296` is 50 lines
of nested `bal`/`mt` at ~24 levels of indentation; `:392` is a 70-character
bracket literal with a 22-line expected value.

This is precisely the class the `Display` action is meant to eliminate: with a
`Display (Dyck …)` instance the expected value is the string `"[][]"`.

### B.4 Test *inputs* hand-constructed as proof terms — `Phase/Display.agda`

Ironically, the display module's own demo violates criterion 1 for 5 of its 7
cases:

```
src/Theory/Instances/Monoid/Phase/Display.agda:238
  ds : Ds (d ∷ d ∷ [])
  ds = CONS {A = ＂ d ＂} _
         (⊗pt ＂ d ＂ Ds (d ∷ []) (d ∷ []) (lit-pt d)
           (CONS {A = ＂ d ＂} _
             (⊗pt ＂ d ＂ Ds (d ∷ []) [] (lit-pt d) nilD)))
```

and likewise `parse` (:243), `parse'` (:249), `chars` (:260). Only `RegexDemo`
(:319) obtains its parse honestly, via `decide-r`. The header at :30-33 explains
*why* (`⊗pt` needs both grammars explicit or pattern unification blocks), but
the fix is to parse the input rather than to build the tree.

### B.5 A regex/automaton written as constructors where a POSIX string exists

`src/Theory/Instances/Monoid/Automaton/Implicit/SoundnessExamples.agda:38-61`:

```
  star : DetReg (¬ℙ ⟦ true ⟧ℙ ∩ℙ ⊤ℙ) (¬ℙ ⟦ true ⟧ℙ) false
  star = ＂ true ＂dr *DR[ (λ _ → Sum.inl tt*) ]
  alt = _⊕DR[_]_ {notBothNull = Eq.refl} ＂ true ＂dr sep ＂ false ＂dr
    where
    sep : (c : Bool) → (c ∈ℙ (¬ℙ ⟦ true ⟧ℙ)) Sum.⊎ (c ∈ℙ (¬ℙ ⟦ false ⟧ℙ))
```

`AnalysisExamples.POSIX "true|false"` in the sibling file does the same job from
a string. Similarly
`src/Theory/Instances/Monoid/Automaton/Implicit/RegExpExamples.agda:59-63`
hand-assembles the automaton (`bStar = *Aut discL2 (litAut discL2 b) refl
litFollows`), and `GreedyExamples.agda` / `GreedyMaxExamples.agda` inherit that
file's raw `L2` alphabet, so all 12 of their cases are raw `a ∷ b ∷ …`.

### B.6 Double-written token lists

`src/Theory/Instances/Monoid/Combinator/Decidable/Arrow.agda:296-299` — 11 raw
tokens for what is morally `((x, y) => x).f`, spelled twice:

```
yes-arrow2-member : E (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
yes-arrow2-member =
  theYes (parse (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ [])
    tt) Eq.refl
```

Same pattern throughout `Arrow.agda:263-328` (15 cases),
`Combinator/Decidable/Arith.agda:34-77` (13),
`Combinator/Decidable/Lambda.agda:69-98` (8),
`Combinator/Decidable/WidthsTests.agda:19-74` (14, e.g. `:70`
`(ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ [])`).

### B.7 Where the alphabet is a bespoke two-letter type instead of `UChar`

`Regex/Tests.agda` (31 cases) and `Backreference/RegexTests.agda` (20) use raw
`a ∷ b ∷ []` over a local `data L`, while `Regex/UnicodeTests.agda` and
`Regex/ParseTests.agda` prove the `text "…"` path works for the *same* regex
constructs. `Regex/Tests.agda:143` even writes `word = strr (a ∷ b ∷ a ∷ [])`
where `Regex/Unicode.agda:127`'s `strU "aba"` exists.

### B.8 Summary of violation counts

| fault | files | ≈cases |
|---|---|---|
| raw constructor / AST input | 27 | ~430 |
| ad-hoc refutation (`theNo`/`theNotD`/`≡ M.nothing`) rather than `rejects` | 20 | ~150 |
| expected value is a raw ADT / `Maybe Unit` rather than a printed string | 33 | ~560 |
| uses `rejects` | **0** | **0** |
| uses the `Display` class | **1** (its own demo) | **7** |

---

## C. Duplicated test helpers

The maintainer's specific concern. Ordered by how much they cost.

### C.1 `theD` / `theNotD` / `isYesD` — a re-implementation of a library function

* library: `theYes` `Theory/Type/Decidable/Base.agda:81`, `theNo` :74,
  `isYes` :77 — for the *internal* `DecTy`.
* copy: `theD` `Combinator/Decidable/STLC.agda:1055`, `theNotD` :1059,
  `isYesD` :1051 — for the *metalanguage* `Dec`.

This is the one genuine "should be in the library" helper. It belongs next to
`theYes`/`theNo`, or better: STLC's `scoped?`/`typed?` should return `DecTy`
rather than `Dec` so the library versions apply. **Fixing this deletes the
`theNotD` idiom the maintainer named.**

### C.2 The two-letter alphabet fixture — 4 byte-identical copies + 2 renamed

The identical 8-line block

```agda
data L : Type ℓ-zero where a b : L

_≟L_ : (x y : L) → (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥)
a ≟L a = Sum.inl Eq.refl
b ≟L b = Sum.inl Eq.refl
a ≟L b = Sum.inr λ ()
b ≟L a = Sum.inr λ ()
```

appears at
`KleeneStar/GuardedTests.agda:14-20`,
`Regex/Tests.agda:15-21`,
`Backreference/Stress/Common.agda:19-25`,
`Backreference/RegexTests.agda:16-22`.
Renamed variants: `Two`/`_≟_` at `Combinator/Grammars/RegexTests.agda:21-27`;
`L2`/`_≟L2_`/`discL2` at `Automaton/Implicit/RegExpExamples.agda:26-39` (used
also by `GreedyExamples` and `GreedyMaxExamples`).

### C.3 The token-alphabet fixture `data Tok` + `_≟T_` — 8 copies

`Combinator/Decidable/Lambda.agda:20,23`,
`Combinator/Decidable/Widths.agda:26,29`,
`Combinator/Decidable/ListLit.agda:23,26`,
`Combinator/Decidable/Bracket.agda:27,30`,
`Combinator/Decidable/STLC.agda:29,32`,
`Combinator/Incomplete/ListLit.agda:23,26`,
`Combinator/Grammars/ArithGrammar.agda:30,33`,
`Combinator/Grammars/PolyGrammar.agda:43`.
Each is a hand-written quadratic `_≟T_` (16 clauses for 4 constructors).

**Partly solved during the audit**: `src/Theory/Type/Decidable/DiscreteEq.agda`
appeared on disk while this survey ran. It supplies `DiscreteEq Y` (:19-20) and
`decEqRetract` (:26-33), whose header says exactly this: *"an enumeration — a
datatype all of whose constructors are nullary — is a retract of `ℕ` by the
constructor's index, so its `DiscreteEq` costs one clause per constructor rather
than one per ordered pair of them."* All eight copies should be rewritten
through it; none has been yet.

### C.4 `matches` — 3 verbatim copies

```agda
matches r = observe (decide-r r ℓr) (semact-dec (semact-pure tt))
```

`Regex/Tests.agda:28`, `Backreference/RegexTests.agda:29`,
`Backreference/Stress/Common.agda:33` (the latter two differ only by
`decide-r`→`decide-b`; `RegexTests` could simply import `Common`).

### C.5 `Yes` / `No` / `yes` / `no` witness quartet — 2 near-identical copies

`Regex/UnicodeTests.agda:26,29,32,36` and `Regex/ParseTests.agda:24,27,30,34`.
The only difference is indexing by the POSIX source string rather than by an
`RE`. This quartet is *exactly* what `accepts`/`rejects` replace.

### C.6 `ℓr : Level ; ℓr = ℓ-suc ℓ-zero` — 8 copies

`Regex/ParseTests.agda:22`, `Regex/Tests.agda:26`, `Regex/UnicodeTests.agda:23`,
`Regex/Examples.agda:35`, `Phase/Display.agda:311`,
`Backreference/RegexTests.agda:27`, `Backreference/Stress/Common.agda:31`,
`Greedy/Examples.agda:42`.

### C.7 Input-size generators — 8 copies of "repeat one character n times"

`Automaton/Demo.agda:137` `xs : ℕ → List UChar`;
`Automaton/LexiconExamples.agda:152` `as`;
`Automaton/ScratchPerf.agda:48` `as`;
`Automaton/Implicit/RegExpExamples.agda:126` `bs : ℕ → String`;
`Automaton/Implicit/AnalysisExamples.agda:164` `bs`;
`Greedy/Examples.agda:118` `reps`;
`Backreference/Stress/Common.agda:56` `repA` (pattern-side);
`Examples/Benchmark/Dyck.agda:38` `iterChar`.
Plus the token-list flavours `chain`/`nest` at `Combinator/Decidable/Arith.agda:81,85`
and `mkInput` at `Examples/Benchmark/Dyck.agda:44`.

### C.8 Lexer-output readback wrappers — 6+ near-duplicates

All of the shape `Mb.map-Maybe (L.map (λ x → toℕ (x .fst) , untext (x .snd)))`:
`Automaton/Demo.agda:79` `lex`;
`Automaton/LexiconExamples.agda:63` `lexS`, `:119` `toks`, `:155` `lexLen`;
`Automaton/TokenStreamExamples.agda:79` `toks`, `:84` `lex1`, `:135` `phaseToks`;
`Regex/Examples.agda:123` `lex`;
`Pipeline/Dyck.agda:68` `lex`.
Also `Automaton/Demo.agda:141` `len` ≡ `LexiconExamples.agda:155` `lexLen`.
**These are all hand-rolled displays; `displayDec` subsumes every one of them.**

### C.9 Automaton rule-table boilerplate `Qs`/`Ms`/`Dead`/`sQs` — 4 copies, ~20 lines each

`Automaton/Demo.agda:47-76` (5 rules),
`Automaton/LexiconExamples.agda:38-59` (3 rules),
`Automaton/ScratchPerf.agda:26-46` (3 rules — verbatim dup of the previous),
`Automaton/TokenStreamExamples.agda:42-70` (5 rules — verbatim dup of Demo).

### C.10 The three-answer parser triple — 4 copies

`parseDec`/`parseInc`/`parseND` at
`Combinator/Grammars/ArithTests.agda:57,60,63`,
`Combinator/Grammars/DyckTests.agda:47,50,53`,
`Combinator/Grammars/PolynomialTests.agda:64,67,70`,
and renamed at `Combinator/Grammars/RegexTests.agda:58,61,64,67,70`.
The trivial `sem : SemanticAction … Unit` beside them is duplicated at
`ArithTests.agda:54` and `PolynomialTests.agda:61`.

### C.11 Whole duplicated test *blocks* — Decidable vs Incomplete

* `Combinator/Decidable/ListLit.agda:58-78` ≡ `Combinator/Incomplete/ListLit.agda:62-83`
  (`ok?`, `accepts`, `rejects`; identical case tables, only `semact-dec` →
  `semact-Maybe`).
* `Combinator/Decidable/Dyck.agda:43-65` ≡ `Combinator/Incomplete/Dyck.agda:29-52`
  (`parseDyck`, `dyck-trees`, `dyck-no-trees`).
* Both are then duplicated a *third* time in
  `Combinator/Grammars/DyckTests.agda:56-85`, which runs the same cases at all
  three answers in one file — i.e. the right pattern already exists and the
  other two copies are dead weight.

### C.12 Two Unicode-lexing stacks

`Examples/Benchmark/Dyck.agda:106-164` hand-rolls `litAut`/`⊕Aut`/`LexRule`/
`Lexicon`/`runLex` over `String.Unicode` to get `fromString`, duplicating
`Theory/Instances/Monoid/Unicode/Base.agda:95` `text`. The `Examples/` tree and
the `Theory/` tree share no lexer, so the same input is `fromString "[]"` in one
and `text "[]"` in the other.

### C.13 A display implemented twice

`Lex/Regex.agda:65-77` `yield` (structural recursion over `RE` producing
`List Alphabet`) reimplements what `Phase/Display.agda:68-120`'s instances
produce as `AS.String`. Likewise `Automaton/Print.agda:36-43` `print`
(with copies at `src/Automata/Deterministic.agda:92-98` and
`src/Automata/Implicit.agda:247-262`), and the `abstractify` actions at
`Examples/Benchmark/Dyck.agda:57` and `Examples/RecursiveDescent/BinOp.agda:180`.
Five separate structural read-back functions, none of them a `Display`.

### C.14 Trivial

`showU c = untext (c ∷ [])` defined twice **inside one file**:
`Phase/Display.agda:197` and `:307`.

---

## D. Placement — a uniform layout

### D.1 Naming: pick `Tests`, drop `Examples`/`Demo`

Today the repo uses four conventions at once:

| convention | files |
|---|---|
| `<X>Tests.agda` | `Regex/ParseTests`, `Regex/UnicodeTests`, `Backreference/RegexTests`, `Backreference/StressTests`, `KleeneStar/GuardedTests`, `Combinator/Decidable/WidthsTests`, `Combinator/Grammars/{Arith,Dyck,Polynomial,Regex}Tests` (10) |
| `Tests.agda` | `Bags/Quicksort/Tests`, `Regex/Tests` (2) |
| `<X>Examples.agda` / `Examples.agda` | `Automaton/{Greedy,GreedyMax,Lexicon,TokenStream}Examples`, `Automaton/Implicit/{Analysis,RegExp,Soundness}Examples`, `Regex/Examples`, `Greedy/Examples`, `Monoid/Examples` (10, one of which has no tests) |
| `Demo.agda` / `ScratchPerf.agda` | `Automaton/Demo`, `Automaton/ScratchPerf` (2) |

**Recommendation.** One convention, exactly as `review.md:62` says:

* `Tests.agda` when a directory has one test module (`Bags/Quicksort/Tests.agda`,
  `Regex/Tests.agda`).
* `<X>Tests.agda` when a directory has several, one per definitions module
  (`Combinator/Decidable/ArrowTests.agda`).
* `<X>Stress.agda` for the size-scaling suites (§E).
* Retire `Examples`, `Demo`, `ScratchPerf` entirely. "Example" and "demo" both
  mean "a test whose failure nobody notices"; they are all `passes`/`rejects`
  tables underneath.
* Rename `Combinator/Incomplete/Base.agda:131` `Test` → `Attempt` (or
  `Recognizer`) and `Lex/Base.agda:43` `lexTest` → `lexAttempt`, so the word
  "test" means one thing.

### D.2 Target layout, directory by directory

```
src/Theory/Instances/Bags/Quicksort/
    Tests.agda                    ← unchanged (already correct name)
    Stress.agda                   ← NEW: 64/128/256 element sorts (§E)

src/Theory/Instances/Monoid/Regex/
    Tests.agda                    ← MERGE Tests + UnicodeTests + Examples,
                                    all at UChar via `text`
    ParseTests.agda               ← keep (tests the POSIX elaborator itself)
    Stress.agda                   ← NEW

src/Theory/Instances/Monoid/Backreference/
    Tests.agda                    ← RENAME from RegexTests.agda, re-alphabet to UChar
    Stress.agda                   ← RENAME from StressTests.agda
    Stress/Common.agda            → fold into a shared fixture module (§D.3)

src/Theory/Instances/Monoid/Automaton/
    Tests.agda                    ← MERGE Demo + LexiconExamples + TokenStreamExamples
    GreedyTests.agda              ← MERGE GreedyExamples + GreedyMaxExamples
    Stress.agda                   ← MERGE the four "at scale" sections + ScratchPerf
    Implicit/Tests.agda           ← MERGE Analysis/RegExp/SoundnessExamples

src/Theory/Instances/Monoid/Combinator/Decidable/
    ArithTests.agda   ArrowTests.agda   LambdaTests.agda
    DyckTests.agda    ListLitTests.agda WidthsTests.agda  STLCTests.agda
    Stress.agda                   ← chain/nest from Arith.agda:78-102, scaled up

src/Theory/Instances/Monoid/Combinator/Incomplete/
    (no test files — its cases fold into Combinator/Grammars/*Tests.agda,
     which already runs every grammar at all three answer functors)

src/Theory/Instances/Monoid/Combinator/Grammars/
    ArithTests.agda  DyckTests.agda  PolynomialTests.agda  RegexTests.agda
                                  ← unchanged names; absorb the Decidable/
                                    and Incomplete/ duplicates

src/Theory/Instances/Monoid/KleeneStar/  GuardedTests.agda   ← keep
src/Theory/Instances/Monoid/Greedy/      Tests.agda          ← RENAME from Examples.agda
src/Theory/Instances/Monoid/Pipeline/    DyckTests.agda      ← NEW, from Dyck.agda:100-153
src/Theory/Instances/Monoid/Phase/       DisplayTests.agda   ← NEW, from Display.agda:192-323
src/Theory/Instances/Monoid/             Grammars/Fixtures.agda ← RENAME of Examples.agda

src/Examples/
    RecursiveDescent/BinOpTests.agda   ← NEW, from BinOp.agda:190-270
    RecursiveDescent/DyckTests.agda    ← NEW, from Dyck.agda:136-175
    Benchmark/DyckStress.agda          ← RENAME of Benchmark/Dyck.agda's test half
    Benchmark/Dyck.agda                ← keeps only the lexer + `mkInput`, or is
                                         deleted once it uses `Unicode.Base.text`
src/String/ASCII/Base.agda:185         ← the one-line `length translation` check
                                         may stay; it is a definitional invariant
```

### D.3 One shared fixture module

Create `src/Theory/Instances/Monoid/TestFixtures.agda` (or
`Theory/Type/SemanticAction/Fixtures.agda` if it must be theory-generic) holding
exactly what §C found duplicated:

* `ℓr : Level` (C.6);
* `rep : ℕ → Alphabet → String` and `repText : ℕ → AS.String → AS.String` (C.7);
* the two-letter alphabet as a `UChar` sub-alphabet, so `a`/`b` are `ch 'a'`/`ch 'b'`
  and the same tests read as text (C.2);
* a generic decidable equality for a finite token type, replacing eight
  hand-written `_≟T_` (C.3);
* nothing else — `matches`/`ok?`/`lex`/`toks`/`Yes`/`No` are all replaced by
  `accepts`/`rejects` over `displayDec`, not moved (C.4, C.5, C.8).

---

## E. Stress tests

### E.1 What exists

Fifteen places scale input size; only **two** are dedicated files, and none
share a pattern.

| # | location | how size scales | asserted at scale? | measured cost recorded |
|---|---|---|---|---|
| 1 | `Backreference/StressTests.agda` (whole file) | hand-typed input length 128/128/128/64/32/20/13 + pattern args `litbackRE 31`, `deepRE 15` | yes, 9 cases | yes, `:4-28`: n=8 0.6 s, n=12 2.6 s, n=16 22 s, n=20 killed at 376 s |
| 2 | `Automaton/ScratchPerf.agda` (whole file) | `as : ℕ → List UChar`, `as 3200` | yes, 1 case | no (only a `-- BENCH 473108713` marker, `:55`) |
| 3 | `Examples/Benchmark/Dyck.agda:202-415` | `mkInput : ℕ → String` (:44), Fibonacci-ish growth; 10→92, 20→3068, 25→24524, 31→196544 chars | 1 live (`mkInput 25`); 14 commented out | yes, `:190-247`: 25→10 s, 27→20 s, 29→35 s, 31→63 s |
| 4 | `Automaton/GreedyExamples.agda:65-72` | `n` = 0/50/200/800/3200/12800 | **no — comment only** | yes: 2.9/3.0/3.0/3.4/5.1/12.3 s |
| 5 | `Automaton/GreedyMaxExamples.agda:68-83` | `bs n`, n = 0/200/800/3200/12800/51200 | yes, `bs 200` and `bs 3200` | yes: 3.0/3.1/3.3/4.8/9.9/49.8 s |
| 6 | `Automaton/LexiconExamples.agda:139-162` | `as n`, n = 50/200/800/3200/12800 | yes, `as 200` only | yes: +0.1 … +17.5 s |
| 7 | `Automaton/Demo.agda:131-148` | `xs 3200` | yes | claims 4× input ⇒ 4× time |
| 8 | `Automaton/Implicit/RegExpExamples.agda:114-134` | `bs n`, n = 0/50/200/800/3200/12800/25600 | yes, `bs 800`, both polarities | yes |
| 9 | `Automaton/Implicit/AnalysisExamples.agda:160-172` | `bs 100`, both polarities | yes | no |
| 10 | `Automaton/TokenStream.agda:461-474` | token count 40/80/160/320/640 | **no — definitions file, comment only** | yes: 0.91/4.25/20.51 vs 0.16/0.29/0.54/1.06/2.04 s |
| 11 | `Automaton/TokenStreamExamples.agda:143-147` | 19 tokens in one pass | yes | no |
| 12 | `Combinator/Decidable/Arith.agda:78-102` | `chain 8/32`, `nest 8/32` | yes, 5 cases | no |
| 13 | `Greedy/Examples.agda:100-146` | 200 successive `extendAt` | yes | no |
| 14 | `Bags/Quicksort/Tests.agda:99-123` | 8 sorted, 8 reverse-sorted, 32 shuffled | yes | yes, in the trailing comment: 64 ≈ 4 s, 128 ≈ 65 s, 256 > 3 min |
| 15 | `Combinator/Decidable/STLC.agda:302-358` | size canaries `length fibSrc ≡ 65`, `nodes fibTree ≡ 51` | yes | no |

**It is not uniform in any respect**: the file may be dedicated (1,2) or a
trailing comment in a definitions file (10,12); the size generator has eight
different names (§C.7); the measurement is a prose table (4,5,6), a single
number (2), an admission of failure (1), or absent (9,12,13,15); and the
"largest" case is sometimes asserted and sometimes only described (4 and 10
assert nothing at scale, so a regression there is invisible).

Two structural problems:

* **CI runs everything.** `src/Makefile:16` is `agda --build-library` and
  `.github/workflows/main.yml` runs `make check` on every push, so any stress
  file's cost lands on every CI run. `Examples/Benchmark/Dyck.agda` copes by
  commenting cases out — which means they are never run at all, and they rot.
  `Backreference/StressTests.agda` copes by capping at n=16.
* **`Stress/Common.agda` is the right idea in the wrong place.** It is a shared
  fixture (alphabet + `matches` + 10 patterns) sitting under one subsystem, and
  `Backreference/RegexTests.agda` re-declares its contents rather than importing
  it (§C.4).

### E.2 Proposed uniform pattern

One file per subsystem, `<Dir>/Stress.agda`, with a fixed four-part shape:

```agda
{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- <Subsystem> at size.  Wall time minus the N.Ns baseline of an empty module
   importing this one, measured on <machine>:

       n:      64    256   1024   4096
     sec:     0.4    0.9    3.1   14.7

   <one sentence saying what shape that is, and why>.  The largest row is the
   one asserted below; the rest are the record. -}
module <Dir>.Stress where

open import Theory.Instances.Monoid.TestFixtures   -- rep, ℓr, the alphabet

-- 1. the input generator, from the shared fixture, never re-declared
input : ℕ → AS.String
input n = repText n "a"

-- 2. the subject under test, as a displayDec, so the answer is a String
run : AS.String → Mb.Maybe AS.String
run = displayDec theDecision ∘ text

-- 3. the assertions: one `accepts` and one `rejects`, both at the top size
_ : accepts run ( input 4096 ↦ input 4096 ∷ [] )
_ = refl

_ : rejects run ( (input 4096 AS.++ "?") ∷ [] )
_ = refl
```

Rules that make it uniform:

1. **One size generator, shared** — `rep`/`repText` from the fixture module
   (§D.3), never a local `as`/`bs`/`xs`/`reps`/`iterChar`.
2. **Both polarities at the top size.** Half the existing suites assert only
   acceptance; `Backreference/StressTests.agda:4-28` shows the refutation path
   is the expensive one, so a one-sided stress test measures the wrong thing.
3. **The timing table is a comment with an explicit baseline**, in the header,
   in the `n:`/`sec:` two-row form that `GreedyExamples.agda:65-72` already uses.
   Adopt that formatting verbatim; it is the best one present.
4. **The top row is asserted, not just described.** No repeats of
   `GreedyExamples.agda` (table, nothing asserted) or
   `TokenStream.agda:461` (table in a definitions file).
5. **Opt-in from CI.** Either move `**/Stress.agda` out of the `include: .` path
   in `src/grammar.agda-lib` into a second library, or add a `stress` Make
   target that lists them explicitly and keep `make check` on the rest.
   Commenting cases out (`Examples/Benchmark/Dyck.agda`) is not a mechanism.

### E.3 Which subsystems most need one, in order

1. **Parser combinators** (`Combinator/Decidable/**`). The only scaling data is
   `Arith.agda:78-102` (`chain 32`, `nest 32`), buried at the bottom of a
   definitions file, with no timings. This is the subsystem whose cost model is
   least understood and whose grammars are largest (`STLC.agda` is 1121 lines);
   a `Combinator/Decidable/Stress.agda` with `chain`/`nest` at 32/128/512 and
   an `STLC` source at 65/260/1040 tokens is the highest-value new file.
2. **Regex derivatives** (`Regex/**`, `Backreference/**`). `Backreference` has
   the best stress file in the repo but at a bespoke alphabet and with typed-out
   inputs; plain `Regex/**` has *none* — `Regex/Tests.agda`'s 31 cases are all
   at length ≤ 5. Derivative blow-up on nested stars is exactly what wants
   measuring.
3. **Automaton tokenising** (`Automaton/**`). Has the most data (rows 4–11
   above) and the least organisation: four "at scale" comment tables, one
   scratch file, and a cost note stranded in `TokenStream.agda:461`. Merging
   them into one `Automaton/Stress.agda` is mostly a move, and it is the
   subsystem where the last two commits (`bc4d6a4` "Early exit on dead states:
   the tokeniser is linear", `5f83e87` "Tokeniser: memoise the scan") were
   explicitly performance work with no regression guard left behind.
4. **Quicksort on bags** (`Bags/Quicksort/**`). `Tests.agda:118-123` asserts 32
   elements and the trailing comment records 64 ≈ 4 s / 128 ≈ 65 s / 256 > 3 min
   — superlinear, and the file's own header (:1-41) documents two failure modes
   that "hang at two elements". A `Bags/Quicksort/Stress.agda` asserting 64 and
   documenting 128/256 turns that comment into a guard. Note
   `Theory/Type/Operation/Base.agda:133-134` already cites this file as the
   benchmark for a `>7min` vs `3.3s` decision, so it is load-bearing already.

---

## F. Migration plan

Ordered so that nothing has to be done twice. Effort: **S** ≤ 1 h, **M** ≤ half
a day, **L** ≥ a day.

### Phase 1 — make the interface usable (do first; everything else depends on it)

| # | action | effort |
|---|---|---|
| 1 | **Rename the two `accepts`/`rejects` lemma pairs that now shadow `Suite.rejects`**: `Combinator/Decidable/ListLit.agda:61,70` and `Combinator/Incomplete/ListLit.agda:66,75` → `lists-accepted` / `lists-rejected`. Also rename `accepts : String → Bool` at `Automaton/Implicit/RegExpExamples.agda:87` and `Automaton/Implicit/AnalysisExamples.agda:62` → `acceptsBool`. | **S** |
| 2 | **Add `accepts` to `module Suite`** (`Theory/Type/SemanticAction/Base.agda`, after :54) with the signature in §0.2. `M` is already imported at :18. | **S** |
| 3 | **Rename `Test` → `Attempt`** at `Combinator/Incomplete/Base.agda:131` and `lexTest` → `lexAttempt` at `Lex/Base.agda:43`, plus the 6 use sites, so "test" is unambiguous. | **S** |
| 4 | **Create `src/Theory/Instances/Monoid/TestFixtures.agda`** with `ℓr`, `rep`/`repText`, the two-letter `UChar` sub-alphabet, and a generic finite-token `_≟_` built on the new `Theory/Type/Decidable/DiscreteEq.agda` (§D.3). Delete the 8 copies of `ℓr` (§C.6), the 4+2 copies of `data L` (§C.2), and the 8 copies of `bs`/`as`/`xs`/`reps` (§C.7) as each file is touched below. | **M** |

### Phase 2 — close the display gap (criterion 3), so tests have something to print

| # | action | effort |
|---|---|---|
| 5 | **Write `Display` instances for the hand-written `μ`s** named at `Phase/Display.agda:114-118`: `Grammars/Dyck.agda`'s `Dyck`, `Examples/Dyck.agda`'s `Dyck`, `Examples/BinOp.agda`'s `EXP`, and `Automaton/Print.agda`'s `Trace`. Each is one `semact-rec` and replaces an `abstractify`/`print`/`semactS`. | **M** |
| 6 | **Make `Lex/Regex.agda:65-90` (`yield`/`which`/`tokens`) a `Display`**, or state it as one, so the six lexer readback wrappers (§C.8) become `displayDec`. | **M** |
| 7 | **Write a `Display` for token streams** (`Automaton/TokenStream.agda`, `Automaton/Lexicon.agda`), replacing the ad-hoc "display boundary" at `TokenStream.agda:136,457` and `Lexicon.agda:284,294,317`. | **M** |
| 8 | **Write a `Display` for STLC `ATy`/`ATm`** and for the `Bags` `Sorted`/`Seq` (`elements` is already 90 % of it, `Bags/Quicksort/Tests.agda:73`). | **M** |
| 9 | **Hoist `showU`** out of `Phase/Display.agda:197`/`:307` (§C.14) and give `UChar` a canonical `showA` in `Unicode/Base.agda`, so no test declares its own. | **S** |

### Phase 3 — move the embedded tests out (14 files, §A.2)

Each item is: cut the test lines into a new sibling, add the imports, rewrite
the cases as `accepts`/`rejects` over `displayDec`, and delete the local helper.

| # | action | effort |
|---|---|---|
| 10 | `Combinator/Decidable/{Dyck,ListLit}.agda:28-65 / 58-78` and `Combinator/Incomplete/{Dyck,ListLit}.agda:26-52 / 57-83` → **fold all four into the existing `Combinator/Grammars/DyckTests.agda` and a new `Combinator/Grammars/ListLitTests.agda`**, which already run every grammar at all three answers (§C.11). Net: 4 files lose their tails, 1 new file, ~40 duplicated cases collapse to ~20. | **M** |
| 11 | `Combinator/Decidable/Arith.agda:33-102` → `ArithTests.agda` + `Combinator/Decidable/Stress.agda` (the `chain`/`nest` half). | **S** |
| 12 | `Combinator/Decidable/Arrow.agda:263-328` → `ArrowTests.agda`. | **S** |
| 13 | `Combinator/Decidable/Lambda.agda:69-98` → `LambdaTests.agda`. | **S** |
| 14 | `Pipeline/Dyck.agda:100-153` → `Pipeline/DyckTests.agda`. Already uses `lex "(())"`, so only the harness changes. | **S** |
| 15 | `Phase/Display.agda:192-323` → `Phase/DisplayTests.agda`, and while there **replace the 5 hand-built parse trees (§B.4) with `decide-r` parses**, as `RegexDemo` already does. | **M** |
| 16 | `Examples/RecursiveDescent/BinOp.agda:190-270` → `BinOpTests.agda`; `Examples/RecursiveDescent/Dyck.agda:136-175` → `DyckTests.agda`. | **S** |
| 17 | `Examples/Benchmark/Dyck.agda:202-415` → `Examples/Benchmark/DyckStress.agda`, **deleting the pasted normalised parse trees at :255 and :296** in favour of the `Display` from item 5 (§B.3). | **M** |
| 18 | `Combinator/Decidable/STLC.agda:235-358, 556-612, 1063-1121` → `STLCTests.agda`. **~57 cases across three regions of an 1121-line file — do this one last of the moves.** | **L** |

### Phase 4 — the readability rewrites (criterion 1)

| # | action | effort |
|---|---|---|
| 19 | **Give STLC a Unicode front end** — a `Lexicon` of `reOf` rules mapping `UChar` text to `Tok`, exactly as `Regex/Examples.agda:106-125` does — then rewrite `STLCTests.agda` as `lex ∘ text`, scope-check, typecheck, per `review.md:22-33`. **This is the item the maintainer named**, and it is what kills `theNotD`/`badApp-refuted`: with `displayDec` the negative cases become one `rejects` table of source strings. Depends on items 8, 18. | **L** |
| 20 | **Delete `theD`/`theNotD`/`isYesD`** (`STLC.agda:1051-1061`) by making `scoped?`/`typed?` return `DecTy` (§C.1). | **M** |
| 21 | **Re-alphabet the bespoke two-letter tests to `UChar`** — `Regex/Tests.agda` (31 cases), `Backreference/RegexTests.agda` (20), `KleeneStar/GuardedTests.agda` (4), `Backreference/Stress/Common.agda`, `Combinator/Grammars/RegexTests.agda` — using the fixture from item 4, so every input is `text "abba"` (§B.7, §C.2). While there, use `strU "aba"` for `Regex/Tests.agda:143`. | **M** |
| 22 | **Merge `Regex/{Tests,UnicodeTests,Examples}.agda` into one `Regex/Tests.agda`**, deleting the duplicated `Yes`/`No`/`yes`/`no` quartet (§C.5) and the three copies of `matches` (§C.4) in favour of `accepts`/`rejects`. | **M** |
| 23 | **Give the token-alphabet parsers a lexer or a concrete-syntax DSL** — `Arrow`, `Arith`, `Lambda`, `Widths`, `ListLit`, `Bracket` (§B.6). Cheapest uniform answer: one `Lexicon` per token type in the fixture module, so `text "((x, y) => x).f"` works. ~60 cases affected. | **L** |
| 24 | **Replace the 128-element cons lists** in `Backreference/StressTests.agda:36,40,44,48,52,64,68` with `rep`/`text` (§B.2). | **S** |
| 25 | **Replace the hand-built automata/regexes** at `Automaton/Implicit/SoundnessExamples.agda:38-61` and `RegExpExamples.agda:59-63` with `POSIX "…"` from `AnalysisExamples.agda:42` (§B.5); `GreedyExamples`/`GreedyMaxExamples` then inherit a text alphabet for free. | **M** |

### Phase 5 — renames and consolidation (§D)

| # | action | effort |
|---|---|---|
| 26 | Rename `Greedy/Examples.agda` → `Greedy/Tests.agda`; `Backreference/RegexTests.agda` → `Backreference/Tests.agda`; `Backreference/StressTests.agda` → `Backreference/Stress.agda`; `Theory/Instances/Monoid/Examples.agda` → `Grammars/Fixtures.agda` (it holds no tests). | **S** |
| 27 | Merge `Automaton/{Demo,LexiconExamples,TokenStreamExamples}.agda` → `Automaton/Tests.agda`, deleting the 4 copies of the `Qs`/`Ms`/`Dead`/`sQs` table (§C.9) and the 6 lexer readback wrappers (§C.8). | **M** |
| 28 | Merge `Automaton/{GreedyExamples,GreedyMaxExamples}.agda` → `Automaton/GreedyTests.agda` (they share `munch`, §C duplicates). | **S** |
| 29 | Merge `Automaton/Implicit/{Analysis,RegExp,Soundness}Examples.agda` → `Automaton/Implicit/Tests.agda`, deleting the duplicated `accepts`/`traceOf` pair. | **M** |
| 30 | Collapse the four copies of `parseDec`/`parseInc`/`parseND` (§C.10) into one parameterised module used by all four `Combinator/Grammars/*Tests.agda`. | **S** |

### Phase 6 — stress tests (§E)

| # | action | effort |
|---|---|---|
| 31 | Add a `stress` target to `src/Makefile` listing `**/Stress.agda` explicitly, and move those modules out of the default `--build-library` path (a second `.agda-lib`, or an `--ignore` list), so CI cost does not grow with them. | **M** |
| 32 | `Automaton/Stress.agda` — merge the four "at scale" comment tables (`GreedyExamples:65`, `GreedyMaxExamples:68`, `LexiconExamples:139`, `RegExpExamples:114`), `ScratchPerf.agda`, and the stranded cost note at `TokenStream.agda:461`, into the §E.2 shape. **Assert the top row**, which two of them currently do not. | **M** |
| 33 | `Combinator/Decidable/Stress.agda` — `chain`/`nest` at 32/128/512 plus an STLC source at 65/260/1040 tokens. Highest-value *new* stress file (§E.3.1). | **M** |
| 34 | `Regex/Stress.agda` — nested-star derivative blow-up; there is currently no scaling data for plain regexes at all (§E.3.2). | **M** |
| 35 | `Bags/Quicksort/Stress.agda` — assert 64 elements, document 128/256, turning `Tests.agda:118-123`'s trailing comment into a guard (§E.3.4). | **S** |
| 36 | Rewrite `Backreference/Stress.agda` to the §E.2 shape and import the shared fixture instead of `Stress/Common.agda`'s private alphabet. | **S** |

### Definition of done

A directory is migrated when:

* it has exactly one `Tests.agda` (or `<X>Tests.agda` per definitions module)
  and at most one `Stress.agda`;
* no definitions file in it contains an `_ : … ; _ = refl`;
* every case is `accepts f ( "…" ↦ "…" ∷ [] )` or `rejects f ( "…" ∷ [] )`;
* `f` is `displayDec` of the subject, so both sides of every `↦` are text;
* the file declares no `ℓr`, no alphabet, no size generator, no `matches`, no
  `Yes`/`No` — all of it comes from `TestFixtures`.

**Current score: 0 of 21 directories.** After Phase 1–2, `Regex/` and
`Combinator/Grammars/` are within one commit each.
