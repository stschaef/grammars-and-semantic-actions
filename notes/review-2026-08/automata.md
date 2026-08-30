# Audit: the automata subsystem

Scope: `src/Theory/Instances/Monoid/Automata/**`, `src/Theory/Instances/Monoid/Automaton/**`,
`src/Theory/Instances/Monoid/Determinization/WeakEquivalence.agda`, with a comparison pass over
the legacy `src/Automata/**` and `src/Determinization/**`.

Sizes (Theory tree only): 24 files, ~5,100 lines. Legacy tree: 13 files, ~2,900 lines.

---

## 0. Executive summary — why it is hard to review

Four distinct causes, in order of how much they cost a reviewer:

1. **Three parallel copies of the same scan.** `Automaton/Greedy.agda` and
   `Automaton/GreedyMax.agda` are the *same algorithm* with a different match witness;
   `Automaton/TokenStream.agda` re-derives a third of both. `diff` of
   `Greedy.agda:74–130` against `GreedyMax.agda:243–318` shows the `scan-nil`/`unmatched`/
   `noMore`/`isSetTable`/`scan` skeleton is line-for-line identical. Nothing tells the
   reader which of the three to read.
2. **An abandoned second copy of the whole subsystem.** `src/Automata/**` +
   `src/Determinization/**` (2,907 lines) is ~70 % re-derived in the Theory tree, is imported
   by nothing under `src/Theory/**`, and is still typechecked on every build
   (`src/Makefile:15` runs `agda --build-library`, which compiles every `.agda` under `src/`;
   there is no `Everything.agda`). `src/Determinization/WeakEquivalence.agda` and its Theory
   counterpart share **414 of 490 byte-identical lines**.
3. **Four kinds of test file with four naming conventions.** `*Examples.agda`, `Demo.agda`,
   `ScratchPerf.agda`, and executable examples embedded in `Implicit/*Examples.agda` that are
   simultaneously the *fixture library* for the other test files. The repo's convention
   everywhere else is `*Tests.agda` (`Regex/Tests.agda`, `Bags/Quicksort/Tests.agda`,
   `Combinator/Grammars/DyckTests.agda`, …).
4. **Escapes from the DSL clustered in exactly the interesting places.** The code is
   overwhelmingly internal — `Automaton/Disjoint.agda`, `Automaton/Print.agda`,
   `Automata/NFA/Properties.agda` are model DSL style. But every *hard* step
   (`cancel`, `refuteExt`, `dead-empty`, `Trace→TraceTo`) drops to raw λ-terms over the
   model, which is where a reviewer most needs the DSL's help.

And, separately, in `Implicit/**`: **one lemma written nineteen times.** The
`with δ … | fail = ⊥Ty↑-elim | ↑f q = id⊢` coercion appears at nineteen sites in
`Implicit/Soundness.agda`, and a `subst … (STOP q)` transport at fifteen more. Naming those
two would remove well over a hundred lines from the largest file in the subsystem (§8.9.1).

**Highest-leverage single change:** factor `Greedy`/`GreedyMax`/`TokenStream`'s shared scan
into one parameterised module and delete `Automaton/Greedy.agda`. That removes ~130 lines,
one file, one test file (`GreedyExamples.agda`), and the "which one is current?" question.

**A recurring meta-pattern worth naming.** In six places the code *documents* a duplication
instead of fixing it, and in every case the fix is one word (`private` → nothing):

| Comment | Fix |
|---|---|
| `Soundness.agda:1069-1071` "`Compile` keeps them private … so they have to be written again here" | drop `private` at `Compile.agda:208` |
| `TokenStream.agda:224-225` "restated here rather than exported from its private block" | export `Greedy.accN` |
| `TokenStream.agda:258` "`GreedyMax`'s own `isSetMatch`/`isSetTable` are private there" | make them public |
| `SuffixChain.agda:10` "This belongs in `Suffix/`, next to the order it is about." | move the file |
| `GreedyExamples.agda:10` "If `Automaton/Greedy` is ever retired, this goes with it." | retire it |
| `Lexicon.agda:317-318` "see the note at the bottom of this file" | there is no such note |

Grepping for these comments is a good way to find the rest.

---

## 1. Internality to the DSL

### 1.1 UNJUSTIFIED — `STEP` bypasses the `step-in` that exists three lines above it
`src/Theory/Instances/Monoid/Automaton/Deterministic.agda:121-130`

```agda
  STEP {b = b} c q = roll ∘⊢ σ⊕ {Y = Tag b q} (step c) ∘⊢ STEP-branch
    where
    -- the only plumbing: a tensor's factors enter the code lifted, as in
    -- `KleeneStar.CONS-branch`
    STEP-branch : {b : Bool} → literal c ⊗ Trace b (δ q c)
      ⊢ ⟦ ⊗e _⊙_ (two (k (literal c)) (Var (lift (δ q c)))) ⟧TheoryTy
          (λ x → Trace b (x .lower))
    STEP-branch m (ms , e , l , t , _) = ms , e , two (lift l) (lift t)
```

`step-in` at `Deterministic.agda:96-98` is *exactly this map*, as a DSL term:
`step-in c = ⟦⊗e⟧⁻ _ _ ∘⊢ ⊗-map liftTy liftTy`. The comment "the only plumbing" is false —
the plumbing is already done and named. **Fix:** `STEP {b = b} c q = roll ∘⊢ σ⊕ (step c) ∘⊢ step-in c`.
The same fix applies verbatim to `GreedyMax.agda:94-99` (`STEPTo`'s local `branch`),
which duplicates `step-in` a *third* time.

### 1.2 UNJUSTIFIED — `unrollTrace`/`fromCode` destructure the code by hand
`src/Theory/Instances/Monoid/Automaton/Deterministic.agda:148-152, 161-165`

```agda
    fromF : ⟦ TraceTy b (lift q) ⟧TheoryTy (λ x → Trace b (x .lower))
          ⊢ TraceLayer b q
    fromF m (stop p , x) = Sum.inr (p , x)
    fromF m (step c , ms , e , f) =
      Sum.inl (c , ms , e , f zero .lower , f (suc zero) .lower , tt*)
```

`GreedyMax.agda:109-113` writes the *same* function for `TraceToTy` correctly, in the DSL:

```agda
    fromF = ⊕ᴰ-elim λ where
      (stop p) → inr ∘⊢ σ⊕ p
      (step c) → inl ∘⊢ σ⊕ c ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _
```

So the DSL version is known to typecheck for this shape. **Fix:** replace both `fromF`
(`:148`) and `fromCode` (`:161`) with `⊕ᴰ-elim λ where (stop p) → inr ∘⊢ σ⊕ p ; (step c) → inl ∘⊢ σ⊕ c ∘⊢ step-out c`,
reusing the `step-out` at `:92`. This is the single clearest "an algorithm that could have
been a DSL term" in the file, and it is *self-evidently* so because the correct version is
in a sibling file.

### 1.3 UNJUSTIFIED — `dead-empty` inducts on the external model
`src/Theory/Instances/Monoid/Automaton/Deterministic.agda:278-284`

```agda
    dead-empty : (q : Q) → isDead q Eq.≡ true
      → (w : String) → Trace true q w → Empty.⊥
    dead-empty q d w (roll .w (stop p , x)) = ...
    dead-empty q d w (roll .w (step c , ms , e , f)) =
      dead-empty (δ q c) (dead-δ q c d) (ms (suc zero)) (f (suc zero) .lower)
```

This is a `rec` over `TraceTy true` written as an external recursion, and it is the
load-bearing lemma of the "early exit" optimisation (commit `bc4d6a4`). It is fully
internalisable. **Fix:** define

```agda
    DeadTy : Bool → TheoryTy _ tt
    DeadTy true  = ⊥Ty
    DeadTy false = ⊤Ty

    deadAlg : TraceAlg true (λ ql → DeadTy (isDead (ql .lower)))
```
— the `stop` branch is refuted by `dead-rej`, the `step` branch is
`⊥Ty-elim ∘⊢ π₂ ∘⊢ step-out c` after `dead-δ` rewrites the successor's bit. Then
`deadEmpty : isDead q Eq.≡ true → Trace true q ⊢ ⊥Ty` is `rec` and the consumer at
`GreedyMax.agda:274` (below) becomes internal too.

### 1.4 UNJUSTIFIED — `deadNo`, downstream of the above
`src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:272-275`

```agda
  deadNo D q d m _ (ms , _ , t , _) =
    Empty.rec (dead-empty M D q d (ms zero) t)
```

With 1.3 fixed this is `¬Ty-intro (⊥Ty-elim ∘⊢ (deadEmpty d ,⊗ id⊢))` — a DSL term. As
written it is the *only* raw λ in `scan-cons`, in an otherwise entirely internal file.

### 1.5 UNJUSTIFIED — `Trace→TraceTo`'s algebra
`src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:140-147`

```agda
    alg (lift r) m (stop p , x) = r , p , STOPTo r m x
    alg (lift r) m (step c , ms , e , f) =
      f (suc zero) .lower .fst
      , f (suc zero) .lower .snd .fst
      , STEPTo c r (f (suc zero) .lower .fst) m
          (ms , e , f zero .lower , f (suc zero) .lower .snd .snd , tt*)
```

Compare `TraceTo→Trace`'s algebra 15 lines above (`:127-130`), which *is* a DSL term
(`⊕ᴰ-elim λ where … → STEP c r ∘⊢ ⊗-map lowerTy lowerTy ∘⊢ ⟦⊗e⟧ _ _`). The obstruction is
that the carrier `Ans r = ⊕[ q' ] ⊕[ _ ] TraceTo r q'` puts the recursive `⊕ᴰ` under the
right factor of a `⊗`, so the step branch needs `⊗⊕ᴰ-distR` twice.
**Fix:** `alg (lift r) = ⊕ᴰ-elim λ where (stop p) → σ⊕ r ∘⊢ σ⊕ p ∘⊢ STOPTo r ; (step c) → ⊕ᴰ-elim (λ q' → ⊕ᴰ-elim λ pf → σ⊕ q' ∘⊢ σ⊕ pf ∘⊢ STEPTo c r q') ∘⊢ ⊗⊕ᴰ-distR ∘⊢ ⊗-map id⊢ ⊗⊕ᴰ-distR ∘⊢ step-out c`
(`⊗⊕ᴰ-distR` is already imported at `GreedyMax.agda:41-42`).

### 1.6 UNJUSTIFIED (partially) — `cancel`, the biggest escape in `GreedyMax`
`src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:194-224`

```agda
    cancel-step b q q' c u₁ .(c ∷ u₁) z Eq.refl kont (roll ._ (step d , ns , e , g)) =
      fin d (ns (suc zero)) (flatEq d (ns zero) …) (g (suc zero) .lower)
```

`cancel : TraceTo q q' u → Trace b q (u ++ z) → Trace b q' z` **has an internal
statement**, because the DSL has a left residual: `_⟜_` at
`src/Theory/Instances/Monoid/Residual.agda:70-71`, with
`(C ⟜ B) m = (r : ↓M tt) → B r → C (m ++ r)` and `⟜-intro`/`⟜-intro⁻`/`⟜-app`/`⟜-precomp`.
The statement is

```agda
  cancel : (b : Bool) (q q' : Q) → TraceTo q q' ⊢ Trace b q' ⟜ Trace b q
```

— unfolding `⟜` gives exactly `∀ u, TraceTo q q' u → ∀ z, Trace b q (u ++ z) → Trace b q' z`,
the current type. The proof is `rec (TraceToTy q')` into the carrier
`λ r → Trace b q' ⟜ Trace b r`, with `unrollTrace` inverting the `Trace` at each step and
`Dl-lit⊗`/`Dl-ε` (already used at `Deterministic.agda:183-186`) doing the precision work
that `flatEq` + `L.cons-inj` do by hand here. This is the highest-value internalisation in
the subsystem: it is 31 lines of word-splitting that the residual adjunction exists to
avoid, and it is what makes `GreedyMax→Greedy` (`:482-494`) and `no-longer-match`
(`:504-512`) external in turn.

### 1.7 UNJUSTIFIED — `refuteExt`, 73 lines of hand plumbing
`src/Theory/Instances/Monoid/Automaton/TokenStream.agda:316-388`

```agda
      refuteExt q' m gm t = go t
        where
        u z : String
        u = gm .fst zero
        z = gm .fst (suc zero)
        …
        nk  = gm .snd .snd .snd .fst .fst
        nrest = gm .snd .snd .snd .fst .snd
```

Here `u`, `z`, `eu`, `mt`, `nk`, `nrest`, `u''`, `z''`, `mt''`, `nk''`, `t''` are eleven
manual projections through a `⊗`-of-`&` that the DSL has combinators for
(`⊗⊕-distR`, `&⊕-distR`, `¬Ty-map`, `⊗-assoc⁻`, all already imported in this file).
The genuinely word-level content is only `splitCmp` (`:92`) and the two `no-longer-match`
appeals (`:363`, `:372`). **Fix:** keep the case split on `splitCmp` external, hoist it into
a named lemma with a `⊢` type, and write the surrounding derivation with combinators. Even
a partial refactor removes ~40 of the 73 lines.

### 1.8 UNJUSTIFIED — `consAct` does tuple surgery inside a semantic action
`src/Theory/Instances/Monoid/Automaton/TokenStream.agda:193-197`

```agda
    consAct q' w m x =
      ((winsIdx q' w , semact-text {A = Match Prod q₀ q'} (x .fst zero)
          (x .snd .snd zero .lower) .fst)
        ∷ x .snd .snd (suc zero) .snd .lower .fst)
      , tt
```

`x .snd .snd (suc zero) .snd .lower .fst` is four projections deep into a functor code.
The `⟦⊗e⟧`/`step-out` idiom used everywhere else in the subsystem applies. **Fix:** give
`StreamF`'s `tok` summand a named `tokBranch` functor with `out`/`in` maps, as
`Deterministic.stepBranch`/`step-out`/`step-in` and `NFA/Base.stepBranch` already do, and
write `consAct` against those.

### 1.9 UNJUSTIFIED (minor) — `char⁺-cons`
`src/Theory/Instances/Monoid/Automaton/TokenStream.agda:107-109`

```agda
  char⁺-cons c y = two (c ∷ []) y , Eq.refl , ((c , Eq.refl) , (read y tt , tt*))
```

A DSL introduction (`σ⊕ c ,⊗ readChars`) written as a raw tuple. Low cost to fix.

### 1.10 BORDERLINE — the two state-reindexing lemmas, duplicated
`src/Theory/Instances/Monoid/Automaton/Deterministic.agda:189-190` and
`src/Theory/Instances/Monoid/Automaton/Disjoint.agda:52-54`

```agda
    onState d p m = subst (λ y → Trace b (δ q y) m) p             -- Deterministic
      reState q c d p m t = subst (λ y → Trace b' (δ q y) m) (sym p) t  -- Disjoint
```

Same lemma, twice, both binding `m`. Both are expressible as a `⊢`-level transport:
`subst (λ y → Trace b (δ q y) ⊢ Trace b (δ q c)) p id⊢`. **Fix:** one public
`Trace-reindex : c ≡ d → Trace b (δ q c) ⊢ Trace b (δ q d)` in `Deterministic.agda`, used
by both.

### 1.11 JUSTIFIED escapes — for the record, so a reviewer can skip them
- `Determinization/WeakEquivalence.agda:100-330` — decidable-powerset, ε-closure,
  `SplitSupport-FinOrd` choice. All finiteness/decidability bookkeeping, none of it
  expressible as a `⊢`-term. The *algebras* (`NFA→DFA-alg:386-411`, `DFA→NFA-alg:426-454`)
  are correctly written in the DSL.
- `Automaton/Unambiguous.agda:56-123` and `GreedyMax.agda:376-439` — cubical `PathP`/
  `transport` work proving an hLevel. Unavoidable at the model level.
- `Lexicon.agda:64-142` (`anyFin`/`allFin`/`find`) — a decision procedure on `Fin n → Bool`.
  Correctly external; see §6.1 for where it should live.
- `GreedyMax.agda:164-166` (`δ*`) and `TokenStream.agda:92-104` (`splitCmp`) — spec-level
  functions on `String`/`List`. Correct as external, misplaced (see §6).
- `Lexicon.agda:320-333` (`tokeniseFuel`) and `TokenStream.agda:458` (`tokeniseS`) — the
  display boundary. Explicitly flagged as such in the code; correct.
- `GreedyMax.agda:169-184` (`endState`) — proves a fact about the external model
  (`δ* q w ≡ q'`) that is consumed only by `isPropBridgeTy`. Justified as hLevel
  bookkeeping, but see §3 for the naming.

---

## 2. Structural duplication

### 2.1 CRITICAL — `Greedy` vs `GreedyMax`: the same scan, twice
`src/Theory/Instances/Monoid/Automaton/Greedy.agda:74-130` vs
`src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:243-318, 347-366`

A `diff` of those ranges shows the following are **identical or trivially renamed**:

| Definition | Greedy | GreedyMax |
|---|---|---|
| `accN` | `:56-60` | `:245-249` |
| `noExt-ε` | `:75-76` | `:255-256` |
| `Run` / `Table` | `:69-72` | `:237-241` |
| `scan-nil` + its `go` | `:78-84` | `:258-264` |
| `unmatched` / `noMore` / inner `go` | `:104-114` | `:294-309` |
| `δ-⊸⁻` | `:65-66` | `:297-298` |
| `isSet⊗bin` | `:117-121` | `:348-352` |
| `isSetTable` | `:123-127` | `:359-363` |
| `scan` | `:129-130` | `:365-366` |

That is ~45 of `Greedy.agda`'s 130 lines. The only genuine differences are the match
witness, how a match extends (`extendAt` + `Dl` vs one `STEPTo`), and `GreedyMax`'s
dead-state early exit.

And the match witnesses are *the same connective*. `Greedy/Base.agda:111-112` has
`GreedyAt A R = A ⊗ ¬Ty ((R & char⁺) ⊗ ⊤Ty)`, and `GreedyMax.agda:234-235` writes

```agda
  GreedyMax q q' = Match q q' ⊗ ¬Ty ((L q' & char⁺) ⊗ ⊤Ty)
```

i.e. `GreedyMax q q' = GreedyAt (Match q q') (L q')`, spelled out rather than named. So the
two `Run` types are `⊕[ q' ] GreedyAt (L q) (L q')` and `⊕[ q' ] GreedyAt (Match q q') (L q')`
— literally the same shape at a different first argument. That is the parameter the shared
module wants.

**Fix — pick one:**
(a) *Preferred:* delete `Automaton/Greedy.agda` and `Automaton/GreedyExamples.agda`.
`GreedyMax.agda:2-10`'s own header says GreedyMax "supersedes `Automaton/Greedy` in every
respect", and `GreedyExamples.agda:10` says "If `Automaton/Greedy` is ever retired, this
goes with it." Two files already agree this should happen. Move the four `¬Nullable`
re-exports (`Greedy.agda:36-39`) to their real home (see §2.2).
(b) If `GreedyAt` must survive: extract a
`Automaton/Scan.agda` parameterised over `(Mat : Q → Q → TheoryTy _ tt)` with fields
`accHere : isAcc q Eq.≡ true → εTy ⊢ Mat q q` and
`extend : literal c ⊗ Mat (δ q c) q' ⊢ Mat q q'`, and instantiate it twice.

### 2.2 HIGH — an import laundering chain
`src/Theory/Instances/Monoid/Automaton/Greedy.agda:36-39`

```agda
open import Theory.Instances.Monoid.SequentialUnambiguity.Nullable …
  using (¬Nullable-map ; &-¬NullableR ; ⊕ᴰ-¬Nullable ; char⁺-¬Nullable
        ; ¬Nullable→¬ε ; ¬Nullable→char⁺) public
```

`GreedyMax.agda:53-55` and `TokenStream.agda:61-62` import **`Automaton/Greedy`** solely to
get these six names, which `Greedy` does not define. So `GreedyMax` — which is meant to
supersede `Greedy` — depends on it for nothing. **Fix:** drop the `public`, and have both
consumers import `SequentialUnambiguity.Nullable` directly. This alone unblocks §2.1(a).

### 2.3 HIGH — `accN`, `isSet⊗bin`, `isSetTable` written three times
`Greedy.agda:56/117/123`, `GreedyMax.agda:245/348/359`, `TokenStream.agda:226/267/273`.

The code *admits* it:
- `TokenStream.agda:224-225`: "(`Automaton/Greedy.accN`, restated here rather than exported
  from its private block)"
- `TokenStream.agda:258`: "`GreedyMax`'s own `isSetMatch`/`isSetTable` are private there"

**Fix:** `isSet⊗bin` is not automaton-specific at all — move it to
`Theory/Type/HLevels.agda` next to `isSet⊗`. Make `GreedyMax`'s `isSetMatch`/`isSetTable`
public. Export `accN` from wherever the shared scan ends up.

### 2.4 HIGH — `unambiguous-Trace` and `unambiguous-TraceTo` are the same proof
`src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:53-123` vs
`src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:376-439`

Four clauses each, in the same order, with the same `heads`/`c≡d`/`sp`/`eqP`/`Fam`/`main`/
`tP`/`gP` skeleton and the same `-- the recursive call stands in the clause body` comment
(`Unambiguous.agda:73-74`, `GreedyMax.agda:396`). The *only* difference is the `stop`
payload: `b Eq.≡ isAcc q` (a `Bool` equation) vs `q Eq.≡ q'` (a state equation), both
handled by `isSet→isSetEq`.

**Fix:** generalise `Unambiguous.agda` over the tag's stop-payload:
`module _ {P : Q → Type ℓ} (isSetP : ∀ q → isSet (P q))` with `Tag` taking `P q` in `stop`.
`Deterministic.Tag` and `GreedyMax.TagTo` are then both instances, and so are their
`isSetTag` retract proofs (`Deterministic.agda:200-214` ≡ `GreedyMax.agda:321-335`, which
are *also* identical modulo the payload).

### 2.5 HIGH — `Demo.agda` and `TokenStreamExamples.agda` share 33 byte-identical lines
`src/Theory/Instances/Monoid/Automaton/Demo.agda:42-74` ≡
`src/Theory/Instances/Monoid/Automaton/TokenStreamExamples.agda:36-68`

The same five `module Kw = POSIX "let|in|where"` … declarations plus the four
`Qs`/`Ms`/`Dead`/`sQs` dispatch tables, verbatim. `LexiconExamples.agda:35-59` and
`ScratchPerf.agda:22-44` are the three-rule version of the same boilerplate.

**Fix:** one `Automaton/Examples/POSIXLexicon.agda` exporting `Qs`, `Ms`, `Dead`, `sQs`,
`module Lex`. Better still, a `Lexicon.fromRules : (Fin n → AS.String) → …` helper so the
four dispatch tables collapse to a single `Fin`-indexed function and adding a rule is a
one-line change instead of a five-line change in four files.

### 2.6 MEDIUM — `GreedyExamples` and `GreedyMaxExamples` test the same four behaviours
`GreedyExamples.agda:44-63` vs `GreedyMaxExamples.agda:27-52` — same `munch`, same four
`_ = refl` cases, same comments (`-- ...and it really is *maximal*: it does not stop at the
first accepting state, which would give "a"` appears in both). Resolved by §2.1(a).

### 2.7 MEDIUM — the legacy tree
`src/Automata/**` + `src/Determinization/**`, 2,907 lines, ~70 % re-derived in Theory.
Nothing under `src/Theory/**` imports any of it; it survives only because
`agda --build-library` compiles everything under `src/`.

Worst offenders, in order:
- `src/Determinization/WeakEquivalence.agda` — **414/490 lines byte-identical** to the
  Theory version. One consumer (`src/Examples/RegexParser.agda:13`).
- `src/Automata/Implicit/RegExp.agda` — ~85 % duplicated; the Theory file's own header
  (`Automaton/Implicit/RegExp.agda:2`) says it is a port.
- `src/Automata/Implicit/AsDeterministic.agda` — ~100 % subsumed by
  `Automaton/Implicit.agda:127-143`.
- `src/Automata/Implicit/RegExp/StrongEquivalences.agda` — **imported by nobody**.
- `src/Automata/Implicit/RegExp/WeakEquivalences.agda` (1,024 lines) — ~75 % duplicated
  against `Automaton/Implicit/Soundness.agda`.

**Fix:** this is a scoping decision, not a code change: either (a) port
`src/Examples/RegexParser.agda`, `src/Lex/**`, `src/Thompson/**` onto the Theory modules and
delete the legacy tree, or (b) if the legacy tree is kept as the paper's artefact, say so in
a `src/Automata/README` and exclude it from the default build so a reviewer knows not to read
it. Either way, `StrongEquivalences.agda` can go today.
**Caveat:** `src/Automata/Turing/**` (129 lines) has *no* Theory counterpart — it would be
lost, not deduplicated.

---

## 3. Naming

Meaningless local names, with proposed replacements:

| Location | Current | Proposed |
|---|---|---|
| `Greedy.agda:81` | `go q b p` | `runAt` (dispatches on `isAcc q`) |
| `Greedy.agda:110` | `go b p` | `stopOrReject` |
| `GreedyMax.agda:261` | `go q b p` | `runAt` |
| `GreedyMax.agda:304` | `go b p` | `stopOrReject` |
| `GreedyMax.agda:212` | `fin d v …` | `atSameLetter` |
| `GreedyMax.agda:422`, `Unambiguous.agda:109` | `main h` | `rollPath` |
| `GreedyMax.agda:425` | `h` | `tailPath` |
| `GreedyMax.agda:481` | `body q'` | `atEndState` |
| `GreedyMax.agda:408`,`Unambiguous.agda:94` | `sp` | `splitPath` |
| `GreedyMax.agda:419`,`Unambiguous.agda:106` | `Fam` | `TailOver` (it is documented at `Unambiguous.agda:105` as "the line of types the two tails live over" — put that in the name) |
| `Deterministic.agda:148`, `GreedyMax.agda:109`, `TokenStream.agda:174` | `fromF` | `layerOut` (three files, three copies of the name) |
| `Deterministic.agda:189` | `onState d p` | `reindexBy` |
| `Disjoint.agda:52` | `reState` | same lemma as above — merge (§1.10) |
| `Lexicon.agda:101,110` | `go b e` | `fromHead` |
| `Lexicon.agda:128` | `go b e` | `atHead` |
| `Lexicon.agda:234` | `go` | `unwrapFound` |
| `Lexicon.agda:275` | `go` | `onFound` |
| `TokenStream.agda:318` | `go s` | `refuteStream` |
| `TokenStream.agda:339` | `rival q'' r` | `refuteRivalToken` |
| `TokenStream.agda:377` | `branch` | `onOverlap` |
| `TokenStream.agda:103` | `hd` | `headEq` |
| `Determinization/WeakEquivalence.agda:455` | `step-help` | `stepAlongWalk` |
| `Analysis.agda:65,72,146,152,202` | `go` | (see subagent detail, §8) |
| `Soundness.agda:260,268` | `go x` | (see §8) |

Also:
- `Deterministic.agda:200-214` and `GreedyMax.agda:322-335` both use `to`/`from`/`ret` for
  the retract triple — acceptable as a local idiom, but they are the same proof (§2.4).
- `Lexicon.agda:240` `scanProd = scan Prod isSetProdQ ProdDead` has **no type signature**;
  every other top-level definition in the file has one.
- `GreedyMax.agda:169-184`: `endStop` / `endStep` / `endState` — `endState` is fine;
  `endStop`/`endStep` read as verbs. Prefer `endStateOfStop` / `endStateOfStep`.

---

## 4. Comments

### 4.1 A broken `OPTIONS` pragma swallowed by a merged comment — **fix today**
`src/Theory/Instances/Monoid/Automaton/GreedyExamples.agda:1-23`

```agda
{- The OLD scan, kept honest.
   …
   (original header follows)
# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}
{- Maximal munch, run.
```

Line 13's `# OPTIONS …` is *inside* the `{- -}` block that opens at line 1. The file's only
occurrence of the string `OPTIONS` is that one, so **this module compiles with neither
`--lossy-unification` nor `-WnoUnsupportedIndexedMatch`**, unlike every other file in the
subsystem. This is a botched edit: a new header was prepended and the old one was left
dangling with `(original header follows)` as narration. Either restore the pragma or delete
the file (§2.1a).

### 4.2 Benchmark tables checked into source comments — five of them
- `GreedyExamples.agda:65-72` — `n: 0 50 200 800 3200 12800 / sec: 2.9 3.0 …`
- `GreedyMaxExamples.agda:68-77` — a second table, plus a comparison against the first
- `LexiconExamples.agda:139-150` — a third
- `Implicit/RegExpExamples.agda:117-124` — a fourth
- `TokenStream.agda:461-474` — a fifth, under a `-- COST.` heading
- `ScratchPerf.agda:55` — `-- BENCH 473108713`, a bare magic number

These are measurements of one machine on one day. They will silently rot and a reviewer
cannot tell which are current. **Fix:** one `notes/automata-benchmarks.md` (or a forest tree)
with dates and machine, and a one-line pointer from each file.

### 4.3 Editorial narration that should not be in source
- `GreedyExamples.agda:12` — `(original header follows)`
- `GreedyMaxExamples.agda:6-7` — "This supersedes the `GreedyAt` version these numbers used
  to be compared against, which is why the older timings appear inline below."
- `GreedyMaxExamples.agda:75-77` — "i.e. the same shape as the unproved `GreedyAt` scan
  (0/200/800/3200/12800 = 2.9/3.0/3.4/5.1/12.3), slightly faster"
- `SuffixChain.agda:10` — "This belongs in `Suffix/`, next to the order it is about."
  A TODO disguised as documentation. **Act on it** — the module has one consumer
  (`TokenStream.agda:66`) and no dependency on anything in `Automaton/`.
- `TokenStream.agda:224-225` and `:258` — "restated here rather than exported from its
  private block" / "are private there". Comments documenting a defect instead of fixing it
  (§2.3).

### 4.4 A dangling cross-reference
`src/Theory/Instances/Monoid/Automaton/Lexicon.agda:317-318`

```agda
  -- The tokenising loop.  DISPLAY LAYER, not a `⊢`-term: see the note
  -- at the bottom of this file.
```

There is no note at the bottom of the file; it ends at `:333` with `tokenise`. A second
reference to the same missing note is at `LexiconExamples.agda:139` ("see the note on
`tokenise` in `Lexicon`"). Either restore the note or point at `TokenStream.agda:2-18`,
which is where the explanation actually lives now.

### 4.5 Missing comments where they are genuinely needed
- `Automaton/Implicit/Soundness.agda` — 1,214 lines with **31 comment lines** (2.5 %), the
  lowest density in the subsystem by a factor of five. See §8.
- `Lexicon.agda:298-299`:
  ```agda
  winsIdx f w = Mb.rec (w .fst) (λ i → i) (winner f)
  ```
  The comment above explains *why* `winner` is recomputed (performance), but not the thing a
  reviewer will actually stumble on: nothing proves `winner f ≡ Mb.just (w .fst)`, so the
  two answers are only *believed* to agree. See §5.2.
- `Deterministic.agda:216-221` (`codeIsSet`) — `.snd (step c) (suc zero) = lift tt*` is
  opaque; a one-liner saying the recursive position carries no hLevel obligation would help.
- `TokenStream.agda:396-402` (`atTok`) — a five-stage `∘⊢` chain through `▷⊛r` and the
  payment, with no comment on what each stage does. This is the heart of the guarded
  recursion and the hardest thing in the file to read.

### 4.6 Header essays — mostly good, do not cut
`Deterministic.agda:2-10`, `Lexicon.agda:2-19`, `TokenStream.agda:2-18`,
`Determinization/WeakEquivalence.agda:2-12`, `Unambiguous.agda:2-12`, `Disjoint.agda:2-9`
all explain a *design decision* (why `Trace` is `Bool`-indexed; why a lexicon is not `⊕Aut`;
why the states must sit at `ℓ-max ℓN ℓAlph`; why the direct induction rather than
`Trace≅string`). That is exactly what a header comment is for. Keep them.
The exceptions are the two narration cases in §4.3 and the benchmark tables in §4.2.

---

## 5. Dead / scratch code

No `postulate`, `TERMINATING`, `trustMe`, `NON_COVERING`, or `NO_POSITIVITY` anywhere in the
subsystem (or in the legacy tree). Good.

### 5.1 `ScratchPerf.agda` — delete
`src/Theory/Instances/Monoid/Automaton/ScratchPerf.agda` (63 lines). The name says it. It
contains:
- `:53` `oldScan = G.scan …` — defined, never used, and its only purpose (comparing against
  `Greedy`) is obsolete.
- `:55` `-- BENCH 473108713` — a magic number with no explanation.
- `:61` `_ : E6 (as 3200 ++ (ch '?' ∷ [])) ≡ Mb.just (fs fz)` — a 3,200-character
  computation every full build pays for, duplicating `Demo.agda:147` (also 3,200) and
  `GreedyMaxExamples.agda:82` (also 3,200).
- `:22-44` — a fourth copy of the POSIX product boilerplate (§2.5).

### 5.2 Definitions with no consumers anywhere in `src/`
Verified by grep across the whole tree:

| Definition | Location | Note |
|---|---|---|
| `TraceToLayer` | `GreedyMax.agda:101-104` | used only by `unrollTraceTo` |
| `unrollTraceTo` | `GreedyMax.agda:106-113` | **no consumers at all** |
| `bridge-retract` | `GreedyMax.agda:457-460` | superseded by `isPropBridgeTy`, which `Trace≅TraceTo .ret` uses directly |
| `noDead` | `Deterministic.agda:270-273` | comment claims "Existing users pass this and behave exactly as before" — **no user does** |
| `step-β` | `Automata/NFA/Base.agda:102-103` | a `refl`; no consumer, and `PotentiallyRejecting` has no counterpart (asymmetric API) |
| `GreedyAt-map` | `Greedy.agda:87-89` | `f ,⊗ id⊢`, one use at `:102` — inline it |
| `oldScan` | `ScratchPerf.agda:53` | see §5.1 |
| `subterminalTrace` | `Unambiguous.agda:130-131` | no consumer; keep only if it is intended public API |
| `print-unique`, `parse-print` | `Print.agda:46, 57` | no consumers, but they are *theorems* — keep, they are the point of the file |

`unrollTraceTo`+`TraceToLayer` is the ironic one: `GreedyMax` writes the *correct* DSL
version of `unrollTrace` (§1.2) and then never uses it, while `Deterministic` keeps the
external one and does.

### 5.3 Dead parameters in `Determinization/WeakEquivalence.agda`
- `:410-415` `fold-walk q X q' q∈εX walk` — `X` and `q∈εX` never appear on any right-hand
  side. Drop both; three call sites (`:474`, `:489`, `:492`) simplify.
- `:455-470` `step-help` — `q∈εlitX`, `q'∈litX`, `qt∈x` are all unused in the body. Drop.
  (Note the typo: the binder is `qt∈x`, lowercase, where the declaration says `qt∈X`.)

### 5.4 `Demo.agda` is a test file called `Demo`
`src/Theory/Instances/Monoid/Automaton/Demo.agda` — 148 lines, of which `:88-129` are
twelve `_ = refl` behaviour tests. It is genuinely valuable content (it is the best single
description of what the lexer does), but it is a test file, and its test set is a strict
superset of `LexiconExamples.agda`'s. See §7.

---

## 6. Modularity

### 6.1 `Lexicon.agda:60-172` — 112 lines that have nothing to do with automata
`anyFin`, `anyFin-true`, `anyFin-false`, `allFin`, `allFin-intro`, `allFin-elim`, `Found`,
`find`, `firstFin` (`:60-142`) are `Fin n → Bool` combinatorics; `Tup`, `_!_`, `tab`,
`tab!`, `isSetTup` (`:144-172`) are a strict-tuple type. Neither mentions `Alphabet`,
`Trace`, or `⊢`. They sit above the module's only real content (`module Product`, `:178-333`)
and a reviewer must scroll past all of it.

**Fix:** `Automaton/Lexicon/Priority.agda` (the `Fin`/`Bool` half) and a `Data/Tup.agda` or
`Theory/Instances/Monoid/Tuple.agda` (the tuple half — note the `ℓAlph` pin at `:152` is
purely a `Deterministic`-imposed constraint, worth a comment there). `Lexicon.agda` then
starts at its subject.

### 6.2 `TokenStream.agda:113-459` — one 350-line module, four concerns
`module Stream` contains, in one block: the grammar (`:131-179`), the semantic action
(`:181-202`), an hLevel section (`:237-305`), and the guarded decision (`:307-459`). The
file already numbers them `-- 1.` … `-- 4.` in comments, which is the author telling you
they are separable. **Fix:** split at those numbered boundaries into
`TokenStream/Base.agda` (grammar + constructors + `unrollStream`),
`TokenStream/Emit.agda`, `TokenStream/HLevels.agda`, `TokenStream/Decide.agda`.

### 6.3 `Determinization/WeakEquivalence.agda` — 496 lines, three concerns
`:90-330` is ε-closure/lit-closure infrastructure over decidable finite powersets;
`:330-345` is the subset construction itself (15 lines!); `:386-496` is the trace
equivalence. Only the last third is about weak equivalence, which is the file's name.
**Fix:** `Determinization/Closure.agda` + `Determinization/Subset.agda` +
`Determinization/WeakEquivalence.agda`. This also makes the ε-closure machinery reusable,
which it currently is not.

### 6.4 `SuffixChain.agda` is in the wrong directory
`src/Theory/Instances/Monoid/Automaton/SuffixChain.agda:10` says so itself. It defines the
proper-suffix `Chain` and the memoised Löb over it; nothing in it mentions an automaton.
One consumer (`TokenStream.agda:66`). **Fix:** move to
`Theory/Instances/Monoid/Suffix/Chain.agda`.

### 6.5 The `ℓAlph` pin on state sets
`Greedy.agda:46`, `GreedyMax.agda:64`, `Lexicon.agda:178` all read `{Q : Type ℓAlph}`, while
`Deterministic.agda:55`, `Disjoint.agda:39`, `Print.agda:33`, `Unambiguous.agda:50` are
properly `{Q : Type ℓQ}` polymorphic. Three files force the state type to sit at exactly the
alphabet's level. `Lexicon.agda:183-184` explains why for its own case ("`Fin n` is at level
zero, so the tuple stays at `ℓAlph`"), but `Greedy`/`GreedyMax` carry no such note. If the
restriction is real it should be stated once with a reason; if it is an artefact of
`--lossy-unification` giving up, it should be relaxed.

### 6.6 Private things that should be public
- `GreedyMax.agda:354 isSetMatch`, `:359 isSetTable` — `TokenStream.agda:258-277` re-derives
  both and says so in a comment.
- `Greedy.agda:56 accN` — `TokenStream.agda:226 initNN` re-derives it and says so.
- `Deterministic.agda:200 isSetTag` — `GreedyMax.agda:321 isSetTagTo` is the same proof.

### 6.7 Exports that should be private
- `Deterministic.agda:161 fromCode` and `:156 CodeLayer` are public and consumed only by
  `Disjoint.agda:100` and `Implicit/Disjointness.agda:94-98`, which re-export them again.
  Fine as public, but the re-export at `Disjointness.agda:95 CodeLayer = DA.CodeLayer` is
  pure indirection — use `open … using (CodeLayer ; fromCode) public`.
- `Greedy.agda:39` `public` on the `Nullable` re-exports (§2.2).

### 6.8 `Automata/` vs `Automaton/` — two directories, one letter apart
`src/Theory/Instances/Monoid/Automata/` holds `DFA/Base.agda` (21 lines) and
`NFA/{Base,Properties}.agda`; `src/Theory/Instances/Monoid/Automaton/` holds everything else,
*including* `Deterministic.agda`, which `Automata/DFA/Base.agda:14` re-exports wholesale
(`DFAOver Q = DeterministicAutomaton ⟨ Q ⟩`). A reader has no way to guess which directory a
file is in. **Fix:** one directory. `Automata/DFA/Base.agda` is 8 lines of content and
should just move into `Automaton/Deterministic.agda` or a sibling `Automaton/DFA.agda`.

---

## 7. Test placement

The repo's convention elsewhere is `<X>Tests.agda`: `Regex/Tests.agda`,
`Regex/ParseTests.agda`, `Bags/Quicksort/Tests.agda`, `KleeneStar/GuardedTests.agda`,
`Combinator/Grammars/{Arith,Polynomial,Regex,Dyck}Tests.agda`,
`Backreference/{Regex,Stress}Tests.agda`, `Combinator/Decidable/WidthsTests.agda`.

The automata subsystem uses **four different conventions**, none of them that one:

| File | What it is | Should be |
|---|---|---|
| `Automaton/Demo.agda` | 12 behaviour tests + fixtures | `Automaton/LexiconTests.agda` |
| `Automaton/ScratchPerf.agda` | scratch benchmark | delete (§5.1) |
| `Automaton/GreedyExamples.agda` | 4 tests | delete with `Greedy` (§2.1a) |
| `Automaton/GreedyMaxExamples.agda` | 6 tests + 2 scale tests | `Automaton/GreedyMaxTests.agda` |
| `Automaton/LexiconExamples.agda` | 15 tests | merge into `LexiconTests.agda` |
| `Automaton/TokenStreamExamples.agda` | 13 tests | `Automaton/TokenStreamTests.agda` |
| `Automaton/Implicit/RegExpExamples.agda` | tests **+ the `L2`/`DA` fixture** | split |
| `Automaton/Implicit/AnalysisExamples.agda` | tests **+ `module POSIX`** | split |
| `Automaton/Implicit/SoundnessExamples.agda` | 4 instantiation witnesses | `Implicit/SoundnessTests.agda` |

### 7.1 The serious one: fixtures live inside test files
`Automaton/Implicit/AnalysisExamples.agda:42-70` defines `module POSIX (s : AS.String)`,
which builds `D`, `Q`, `DA`, `isSetQ`, `Dead`, `accepts`, `traceOf` from a POSIX source
string. This is *the* reusable entry point of the whole subsystem, and it is buried at line
42 of a file whose other 170 lines are `_ = refl` assertions — including a `bs 100` scale
test at `:168-171`.

Four modules import it: `Demo.agda:30`, `ScratchPerf.agda:17`, `LexiconExamples.agda:28`,
`TokenStreamExamples.agda:26`. **Every one of them pays the typechecking cost of 170 lines
of unrelated assertions to get a fixture.** Same story for
`Implicit/RegExpExamples.agda`'s `L2`/`_≟L2_`/`DA`/`DADead`/`isSetQ`/`a`/`b`/`bs`, imported
by `GreedyExamples.agda:34` and `GreedyMaxExamples.agda:18`.

**Fix:** `Automaton/Implicit/POSIX.agda` (just `module POSIX`) and
`Automaton/Implicit/Fixtures.agda` (just `L2`, `DA`, `bs`, …), with the assertions left
behind in `*Tests.agda`. This is a pure win: it removes a build-time dependency from four
files and gives the subsystem a named front door.

### 7.2 Redundant scale tests
Three separate 3,200-character `_ = refl` computations —
`ScratchPerf.agda:61`, `Demo.agda:147`, `GreedyMaxExamples.agda:82` — plus a 12,800-row in
the `GreedyMaxExamples.agda:72` comment table. Keep one, in one place, and say in a comment
that it is the build's performance regression guard.

---

## 8. The `Implicit/**` subtree

### 8.1 Internality — nothing to report, and that is correct
`Implicit.agda`, `Implicit/RegExp.agda`, `Implicit/Compile.agda` and `Implicit/Analysis.agda`
contain **zero** `⊢`-terms — no `∘⊢`, `,⊗`, `roll`, `rec`, no `w : String`, no list
splitting. That is the right answer: all four are automaton *data* (`Bool`- and
`FreelyAddFail`-valued transition tables) plus a `Bool`/`Maybe`-valued static analysis. The
grammar-valued layer is correctly quarantined in `Implicit/Disjointness.agda` and
`Implicit/Soundness.agda`. No findings under criterion 1 for these four files.

One style inconsistency: `Analysis.agda:76-78` states the house rule (`with` cannot see
through a definition, so eliminate on a `(v : Bool) → x ≡ v` argument) and follows it
throughout, while `Compile.agda:255, 258` uses a bare `with`. Pick one.

### 8.2 Duplication — a 19-line body written twice, verbatim
`src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:273-291` and `:292-310`

The `altDet {nn = true} {nn' = false}` and `altDet {nn = false} {nn' = true}` clauses have
**byte-identical right-hand sides** — the same `disj? (d .suppF) (e .suppF)` scrutinee, the
same `Mb.just (false , det (d .¬FL ∩ℙ e .¬FL ∩ℙ d .¬F ∩ℙ e .¬F) …)`, down to the nesting of
the `memb-++-l`/`memb-++-r` chains. The implicit indices do not occur in the body.
**Fix:** one `where`-bound worker, or split on `nn or nn'` instead of on the pair.
`:232-238` vs `:239-253` (`seqDet`) is the same pattern at smaller scale.

### 8.3 Duplication — against the legacy tree
- `Implicit.agda:42-116` ≡ `src/Automata/Implicit.agda:33-114`, verbatim. Not one line
  mentions `Alphabet`, yet it sits inside a module parameterised by
  `(Alphabet) (isSetAlphabet)` and is therefore re-elaborated per alphabet for nothing.
  **Fix:** a parameter-free, level-polymorphic `Automaton/FreelyAdd.agda` imported by both.
- `Implicit.agda:126-141` ≡ `src/Automata/Implicit/AsDeterministic.agda:17-33`, clause for
  clause.
- `Implicit/RegExp.agda:45-141` ≡ `src/Automata/Implicit/RegExp.agda:40-141`, modulo
  `decRec` → `with discAlpha` and the `Q` field/parameter move. Only `satAut` (`:70-74`) is
  new. These are pure data over a `Discrete Alphabet` and should exist once.
- `Compile.agda:63-86` (`ℙ`, `_∈ℙ_`, `⊤ℙ`, `_∩ℙ_`, `⟦_⟧ℙ`, `¬ℙ_`) and `:94-127` (`DetReg`)
  ≡ `src/Grammar/RegularExpression/Deterministic.agda:70-121`, character for character in
  the index expressions. The new copy drops the regex index and adds `satdr`, so the two
  *will* drift.

### 8.4 Duplication — small helpers that exist twice within the Theory tree
- `Analysis.agda:49-51 discAlphabet` ≡ the anonymous `Sum.rec (λ p → yes …) …` inside
  `Theory/Instances/Monoid/Types.agda:27-30`. `Analysis.agda:32` already imports from that
  module. **Fix:** `Types.agda` should export `discAlphabet` and define
  `isSetAlphabet = Discrete→isSet discAlphabet`.
- `Analysis.agda:54-60 eqbOf`/`eqb` ≡ the private `eqb` at
  `Theory/Instances/Monoid/Regex/Notation.agda:28-29`.
- `Analysis.agda:375-380 IsDet`/`theDet` ≡ `Theory/Instances/Monoid/Regex/Parse.agda:268-277`
  `IsJust`/`get`, renamed. `AnalysisExamples.agda:43` has both names in scope, which is
  exactly the confusion this creates.
- `Compile.agda:160-170` (`and-elim-l`, `and-elim-r`, `if-true`) and
  `Analysis.agda:81-91` (`orFalse`, `orTrue`, `notTrue`) — seven private `Bool` lemmas across
  two files, none of them in `Cubical.Data.Bool.Properties`. **Fix:** one
  `Theory/Instances/Monoid/BoolLemmas.agda`.

### 8.5 Dead code
Verified by grep across all of `src/`:
- `Compile.agda:327-329 compileNotNull` and `:331-333 compileNullable` — both are
  `nullOf` under a different name at a fixed index, both unused. The 8-line comment block at
  `:315-325` advertising them "to the semantic layer" is stale; `Soundness.agda` never calls
  them.
- `Analysis.agda:382-383 detOf!` — unused; `AnalysisExamples.agda:46` calls
  `theDet (detOfPOSIX s {p}) q` directly.
- `Implicit.agda:78-81 mapFreelyAddInitial` and `:83-87 mapFreelyAddFail+Initial` — unused
  anywhere in `src/Theory` (only `mapFreelyAddFail` is used). Copied from
  `src/Automata/Implicit.agda:107-114`, where they are *also* unused.
- Likely-unused imports: `Implicit.agda:17, 20-21, 34-35` (`Cubical.Algebra.Theory.Finitary`,
  `open SortedSig`, `open SortedEqns`, `Monoid.Base`, `Monoid.Strings`) — nothing in the file
  is theory- or string-valued; similarly `RegExp.agda:19-21, 34-35` and
  `Compile.agda:24-26, 43-44`; `Analysis.agda:25` imports `_and_` unused; `Compile.agda:36`
  imports `tt*` unused. (Not verified by typechecking.)

### 8.6 Naming

| Location | Current | Proposed |
|---|---|---|
| `Analysis.agda:54` | `eqbOf` | `decToBool` |
| `Analysis.agda:65` | `go` | `decToBool-diag` |
| `Analysis.agda:72` | `go` | `decToBool-inl` |
| `Analysis.agda:146` | `go` | `atQd` (it cases on `Q d`) |
| `Analysis.agda:152` | `go` | `atPe` |
| `Analysis.agda:202` | `go` | `bySupportP` |
| `Analysis.agda:195-199` | `sP sQ oP oQ dj` | `suppP suppQ outP outQ disj` |
| `Analysis.agda:97-99` | `Cls`, `one`, `cls` | `Class`, `letter`, `class` — `one`/`cls` read as abbreviations of each other |
| `Analysis.agda:104, 108` | `holdsB`, `memb` | `∈Class?`, `∈Supp?` |
| `Compile.agda:209` | `seqOf` | `seqUnambigOf` (matches `seqUnambig`, `RegExp.agda:105`) |
| `Compile.agda:219` | `firstsOf` | `disjointFirstsOf` (matches `disjointFirsts`, `RegExp.agda:82`) |
| `Compile.agda:285` | `stepInl` | `leftFactorStep` — `Inl` names a constructor, not the situation |
| `Compile.agda:308` | `stepLoop` | `loopBackStep` |
| `Implicit.agda:127, 131` | `isAcc'`, `δ'` | `IDA-isAcc`, `IDA-δ` — the prime is inherited from `AsDeterministic.agda:20` and means nothing here |

`Implicit/RegExp.agda` has no `where` helpers and its names are fine.

### 8.7 Comments
**Slop.** The "no subset construction" claim appears **four** times:
`Implicit.agda:11-13`, `Implicit.agda:139`, `RegExp.agda:8-9`, `Compile.agda:337-338`.
Keep one, in `RegExp.agda`'s header where the compositionality argument lives.
Five content-free `-- ...and` continuations: `Implicit.agda:89`, `RegExp.agda:66`,
`Compile.agda:322`, `:336`, `:345`, `Analysis.agda:193`.
`Compile.agda:22` — "Everything here is automaton *data* … so nothing in this file is
grammar-valued and nothing is a `⊢`-term" — meta-commentary defending the file against a
charge no reader made; delete.
`Compile.agda:57-61` — port narration about `Powerset.More` not being in this cubical;
belongs in the commit message. Keep only "nothing below inspects a membership proof, so a
bare predicate does".
`Compile.agda:2-22` (21 lines) and `RegExp.agda:2-17` (16 lines) restate their files' type
signatures in prose. Cut to ~6 lines each.

**Missing, where it genuinely matters.**
- `RegExp.agda:88`:
  ```agda
    ⊕Aut .null = Sum.rec (λ _ → M' .null) (λ _ → M .null) notBothNull
  ```
  The branches are **swapped** — the `inl` proof that `M` is not nullable yields `M' .null`.
  This is the subtlest line in the file and has no comment.
- `RegExp.agda:111`: `⊗Aut .acc (Sum.inl q) = M .acc q and M' .null` — a left-factor
  position accepts only when the right factor can be skipped. Uncommented.
- `Compile.agda:107-111, 115-121` — the follow-last index expressions
  `(if b' then ¬FL' else ¬FL ∩ℙ ¬F' ∩ℙ ¬FL')` and
  `(if (b and b') then ⊤ℙ else ¬F ∩ℙ ¬F')` are uncommented *here*, where they are declared;
  the explanation exists at `Analysis.agda:254-256`, four hundred lines and one module away,
  next to the code that consumes them.
- `Compile.agda:143`: `States (dr *DR[ _ ]) = States dr` — the star adds no position because
  the loop re-enters the body's own initial transition. One line would do.

### 8.8 Modularity
- **`Compile.agda` (349 lines), four concerns.** Split: `Implicit/Powerset.agda` ← `:56-86`
  (or delete in favour of the existing `Powerset`, §8.3); `Implicit/DetReg.agda` ← `:88-154`
  (`DetReg`, `States`, `isSetStates` — the *syntax*, which every downstream client imports
  transitively and which is not about compilation); shared `BoolLemmas` ← `:156-178`;
  `Compile.agda` keeps `:180-349`.
- **`Analysis.agda` (383 lines), five concerns.** `Implicit/Support.agda` ← `:93-176`
  (`Cls`, `Supp`, `holdsB`, `memb`, `memb-++-*`, `Disj`, `disjCls?`, `disjClsSupp?`,
  `disj?`) — a self-contained decision procedure on letter sets with no dependency on
  `DetReg`, and where the interesting incompleteness lives; alphabet helpers `:45-74` →
  `Types.agda` (§8.4); `IsDet`/`theDet` `:370-383` → delete (§8.4); `erase` `:361-368` is a
  `DetReg → RE` map with nothing to do with first/follow analysis — move next to `DetReg`.
- **Chained `public` re-exports.** `RegExp.agda:37` re-exports `Implicit` publicly,
  `Compile.agda:48` re-exports `RegExp` publicly, `Analysis.agda:34` re-exports `Compile`
  publicly. Importing `Analysis` therefore dumps `FreelyAddInitial`, `↑i_`, `ℙ`, `⊤ℙ`,
  `DetReg`'s constructors, `States`, all six `*Aut`s and `IDA→DA` into scope.
  `Analysis.agda:38-39` already documents having been bitten by exactly this with `RE`'s
  constructors ("not `public`: a client reaches `RE` through `Regex.Base` itself"). Narrow
  each `public` to a `using (…)` list.
- **Should be private:** `Implicit.agda:93 FreelyAddFail+Initial≅Unit⊎Unit⊎` (used only two
  lines below); `Implicit.agda:127, 131 isAcc'`/`δ'` (used only by `IDA→DA`);
  `Analysis.agda:104, 108, 113, 120` `holdsB`/`memb`/`memb-++-l`/`memb-++-r` (`Disj` is the
  intended interface and is already public); `Analysis.agda:359 νOf`.
- `Implicit/Disjointness.agda:94-98` re-exports `CodeLayer`/`fromCode` by *redefinition*
  (`CodeLayer = DA.CodeLayer`) rather than `open … using (…) public`. Pure indirection.

### 8.9 `Implicit/Soundness.agda` (1,214 lines) and `Implicit/Disjointness.agda` (313)

These two are the grammar-valued half, and they are the largest files in the subsystem.
Both are overwhelmingly DSL-internal — the algebras are all `⊕-elim`/`⊕ᴰ-elim`/`∘⊢`/`,⊗`/
`⟜-intro`/`σ⊕`/`fold*r` terms. The problem here is not internality; it is that **one lemma
is written nineteen times**.

#### 8.9.1 The two lemmas that should exist and do not

**The transition coercion, ×19.** `Soundness.agda:293, 311, 343, 361, 402, 410, 425, 447,
521, 574, 672, 702, 717, 754, 825, 874, 971, 996, 1009` all have the shape

```agda
  help c with δ … 
  ... | fail  = ⊥Ty↑-elim
  ... | ↑f q  = id⊢
```

(`⊥Ty↑-elim` occurs 23 times in the file.) The `with` itself is justified — `δ` is external
data — but it is one lemma. **Fix:** put it once in `Disjointness.agda` next to
`ParseAlgCarrier`:

```agda
  alongδ : {A : FreelyAddInitial Q → TheoryTy ℓA tt} {C : Q+ → TheoryTy ℓB tt}
    (d : FreelyAddFail Q) → ((q : Q) → A (↑i q) ⊢ C (↑q q))
    → ParseAlgCarrier A (↑f→q d) ⊢ C (↑f→q d)
  alongδ fail  _ = ⊥Ty↑-elim
  alongδ (↑f q) k = k q
```

Nearly every use instantiates `k = λ _ → id⊢`. The `⟜-app` variant
(`Soundness.agda:602, 623, 902, 922`; `Disjointness.agda:279-282, 302-305`) is the same
lemma with `⊗ RHS` on the source and `⊥Ty-elim ∘⊢ ⊗⊥↑-annihL` in the `fail` branch.

**The `STOP` transport, ×15.** `Soundness.agda:279-281, 306-309, 329-331, 356-359, 388-394,
419-423, 441-445, 515-519, 568-572, 694-700, 732-734, 749-752, 820-823, 992-994, 1021-1023`
all read `subst (λ v → Lε ⊢ Trace v q) (… Eq.eqToPath …) (STOP q)`. **Fix:** one
`STOPᵇ : {b : Bool} (q : Q) → true Eq.≡ b → LiftTheoryTy (ℓF ℓM) εTy ⊢ Trace b q` in
`Automaton/Deterministic.agda` next to `STOP`, plus an `εTy`-sourced variant.

These two alone account for well over a hundred lines.

#### 8.9.2 Copy-paste that the code documents instead of fixing
`src/Theory/Instances/Monoid/Automaton/Implicit/Soundness.agda:1069-1071`

```agda
-- The three side conditions `compile` builds, replayed.  `Compile` keeps
-- them private, and the compiled automaton is only *definitionally* the
-- one these produce, so they have to be written again here.
```

`notBoth'` (`:1074-1079`), `seqOf'` (`:1081-1089`), `firstsOf'` (`:1091-1096`) are
character-for-character `Compile.agda:174-178, 209-217, 219-226` modulo `compile dr` →
`Aut dr` and the `disc` argument. **Fix:** drop the `private` at `Compile.agda:208` and
export `seqOf`/`firstsOf` — `notBoth` at `:174` is *already* public. Then delete 22 lines
and the comment.

#### 8.9.3 Three re-proved library lemmas
- `Soundness.agda:74-79 ≈→≅` ≡ `unambiguous→≅` at
  `Theory/Type/Unambiguity/Disjoint.agda:117-121`, same four copattern clauses. Soundness's
  copy even calls the same `unambiguous→subterminal` it would get for free.
- `Soundness.agda:1064-1067 map*` ≡ `*-map` at
  `Theory/Instances/Monoid/KleeneStar/Map.agda:41-42`, which the file simply does not import.
- `Disjointness.agda:143-151` and `Soundness.agda:778-786` (`star-nil⁻`/`star-cons⁻`) —
  defined **twice**, and both are copies of `KleeneStar.agda:82-89` with the carrier fixed
  to `A *`. **Fix:** generalise the carrier in `KleeneStar.agda` (the nil branch does not
  mention it at all) and delete both.

#### 8.9.4 Whole modules that are one module written twice
- `Soundness.agda:273-322 Alt.MAlg` vs `:324-368 Alt.M'Alg` — a diff modulo
  `q↔q'`, `Sum.inl↔Sum.inr`, `nullFromL↔nullFromR` is empty. Same for
  `nullFromL` (`:257-263`) vs `nullFromR` (`:265-271`) and for
  `⊕Alg (↑q (Sum.inl q))` (`:417-437`) vs `⊕Alg (↑q (Sum.inr q'))` (`:439-459`). ~110 lines.
  **Fix:** one `module Side (inj : Q → Q ⊎ Q') …`, instantiated twice.
- `Soundness.agda:594-656 Seq.MAlg` vs `:893-955 Kleene.MAlg` — differ only in the state
  injection and in `stopM`'s continuation (`:618` vs `:917`). ~62 lines.
  **Fix:** a `LeftFactorAlg` module parameterised by the injection and by
  `atAccept : (q) → true Eq.≡ M .acc q → RHS ⊢ Trace true (↑q (inj q))`.
  `Seq.⊗Alg (↑q (Sum.inl q))` (`:679-746`) vs `Kleene.*Alg (↑q q)` (`:978-1043`) is the same
  story with `Parse M'` ↔ `Parse M *`.
- `Soundness.agda:494-500 and-l`/`and-r` are the `Eq.≡` twins of
  `Compile.agda:160-166 and-elim-l`/`and-elim-r` (see §8.4).
- `Soundness.agda:1111-1120, 1133-1142, 1195-1200` — three `⊕DR` clause pairs whose
  `{b = true}` and `{b = false} {b' = true}` bodies are identical, split only so `notBoth'`
  reduces.

#### 8.9.5 Internality — four small unjustified escapes, all in `Disjointness.agda`
- `:49-51` `&⊕ᴰ-distR m (a , (y , b)) = y , (a , b)` — a **verbatim copy of
  `Residual.agda:365-367`**, in a file that already imports from `Residual` at `:34`, and it
  is **never used**. Delete.
- `:53-54` `⊗⊥↑-annihR m (ms , e , (a , (b , _))) = b .lower` — derivable as
  `⊸-app ∘⊢ (id⊢ ,⊗ ⊥Ty↑-elim)` (`⊸-app`: `Residual.agda:164`; `⊥Ty↑-elim`:
  `Theory/Type/Bottom/Base.agda:36`).
- `:56-57` `⊗⊥↑-annihL` — derivable as `⟜-app ∘⊢ (⊥Ty↑-elim ,⊗ id⊢)`; both are already in
  scope and used elsewhere in the same file.
- `:59-60` `⊤Ty↑-intro m a = tt*` — this *is* the introduction rule for a connective, so the
  raw definition is fine; it is in the wrong file. `⊤Ty↑` is defined at
  `Theory/Type/Top/Base.agda:25` and that module ships no intro rule. Move it there.

Justified escapes, for the record: `Soundness.agda:1056-1062 unambiguous-satTy` and
`:1191 unambig-erase` (hLevel); `:161` (`J` along a decision-procedure result), `:177`, `:216-220`
(transporting a morphism along `disc`/`P c`); `Disjointness.agda:226-229` (index transport).

#### 8.9.6 Dead code
- `Disjointness.agda:49-51 &⊕ᴰ-distR` — never used (§8.9.5).
- `Disjointness.agda:178-189` — the whole `module _ (isSetQ : isSet Q)`: `parseTrace`
  (`:181`) has no use anywhere in `src/`; `AcceptingTraceParser` (`:188`) is
  `TraceDisj⊥ true false true≢false`, does not use `isSetQ` at all, and has no callers (the
  only other `AcceptingTraceParser` is in the legacy `src/Automata/Implicit.agda:356`).
- `Disjointness.agda:76-83` — the private aliases `isAcc = isAcc' M`, `δ = δ' M`: neither is
  referenced; the file uses the record fields opened at `:69`.
- Unused imports, `Disjointness.agda`: `:22` (`[]`/`_∷_`), `:23` (`List.Properties as L`),
  `:26` (`Sum`), `:35` (`⊗⊕ᴰ-distR` — only `-distL` is used, at `:162`), `:36` (`flat`), and
  `Tag`/`stop`/`TraceLayer`/`unrollTrace`/`ℓT` from the `open … using` at `:71-72`.
- Unused imports, `Soundness.agda`: `:22` (`false≢true`), `:25` (`++-unit-r`), `:28`
  (`Σ-syntax`, `_×_`), `:41` (`SeqUnambig`), `:43-44` (`splitAgree`), `:46` (`#→disjoint`),
  `:49` (`⊗⊕ᴰ-distL`, `⊗⊕ᴰ-distR`), `:58` (`unambiguous-Trace`), and from `Regex.Base`
  (`:60-61`) everything but `⟦_⟧` and `satTy`. Also the unused level variable `ℓX` (`:68`).
  (Not verified by typechecking.)

#### 8.9.7 Naming

| Location | Current | Proposed |
|---|---|---|
| `Soundness.agda:260, 268` | `go` | `nullOfOtherBranch` |
| `Soundness.agda:402, 410` | `helpR`, `helpL` | `atδᵢ-inr`, `atδᵢ-inl` |
| `Soundness.agda:425, 447, 574, 754` | `help` (four different things) | `atδq` |
| `Soundness.agda:672, 971` | `helpInit` | `atδᵢ` |
| `Soundness.agda:702, 996` | `helpStay` | `atδq` |
| `Soundness.agda:717, 1009` | `helpJump` | `atδᵢ-ofRight` / `atδᵢ-ofBody` |
| `Soundness.agda:839` | `base` | `stepBeforeAcc` |
| `Soundness.agda:694, 732, 992, 1021` | `tA` | `acceptHere` |
| `Soundness.agda:698` | `tN` | `nullRight` |
| `Soundness.agda:1046, 1050`; `Disjointness.agda:156, 160` | `nilB`, `consB` | `stopBranch`, `stepBranch` |
| `Soundness.agda:1059` | `xy` | `sameLetter` |
| `Soundness.agda:1076-1077` | `p`, `q` | `notNullL`, `notNullR` — `q` shadows the state name used throughout the file |
| `Disjointness.agda:216` | `help` | `firstTransitionOn` |

The nine copies of `conv`/`stay`/`contra` become moot once §8.9.1 lands.

#### 8.9.8 Comments
Provenance chatter to delete: `Soundness.agda:71-72` ("this is the old `≈→≅`, and it is why
the whole development can stay logical" — editorialising about a definition that should not
exist), `:81` ("The compiler's discrete alphabet, once." on a two-line alias), `:222`
("Ported from `Automata/Implicit/RegExp/WeakEquivalences`'s `⊕Aut≈`" — keep only `:223-224`
on levels, which is useful), `Disjointness.agda:2-3` (same, `:4-9` is good and should stay),
`:175-176` (provenance, documenting two dead definitions).

Inaccurate: `Disjointness.agda:46` — "Generic facts, all about `literal`: none of them
mention an automaton." Only `same-first` (`:63`) is about `literal`.

Missing where it matters:
- `Soundness.agda:535-556` (`nextBase`/`next`) and `:839-861` (`base`/`conv`) — the `subst`
  over `if v then Sum.rec … else …` reconstructing `⊗A .δq (Sum.inl q) c` from the
  accepting-state flag. The hardest step in each module; no comment.
- `Soundness.agda:506-507` — `⟦ initial ⟧M' = &[ q ∈ Q ] &[ _ ∈ true Eq.≡ M .acc q ] …`,
  i.e. a run of `M'` reinterpreted as "startable at *every* accepting state of `M`". `:502`
  gestures at this; it needs an explicit line on why the `&` over `q` is there (the join
  state is not known when the algebra is written).
- `Soundness.agda:1121, 1143, 1201` — the absurd `{notBothNull = ()}` clauses are unremarked.

#### 8.9.9 Modularity — `Soundness.agda` is 3.5× its largest sibling
1,214 lines, six independent concerns. Split at the existing module boundaries:
`Implicit/Soundness/Leaves.agda` ← `module Leaves` (`:92-220`);
`Implicit/Soundness/Alt.agda` ← `module Alt` (`:226-467`);
`Implicit/Soundness/Seq.agda` ← `module Seq` (`:473-772`);
`Implicit/Soundness/Kleene.agda` ← `module Kleene` (`:788-1053`);
`Implicit/Soundness.agda` keeps `fromAut`/`toAut` (`:1099-1146`), `unambig-erase`
(`:1187-1203`), `compile-sound` (`:1207-1214`) — about 150 lines.

Misplaced definitions:
- `unambiguous-satTy` (`Soundness.agda:1055-1062`) → `Theory/Instances/Monoid/Sat.agda`,
  beside `satTy`/`isSetSat` (`Sat.agda:23-31`).
- `⊤Ty↑-intro` (`Disjointness.agda:59`) → `Theory/Type/Top/Base.agda:25`.
- `⊗⊥↑-annihR`/`⊗⊥↑-annihL` (`Disjointness.agda:53-57`) → `Residual.agda`, beside
  `⊗⊕ᴰ-distL`/`&⊕ᴰ-distR` (`:351-367`).
- `same-first` (`Disjointness.agda:63-65`) → `Precise.agda`, beside the `sameHead` it wraps.
- `Disjointness.agda:68-162` (`Parse`, `CodeLayer`, `fromCode`, `ParseAlgCarrier`,
  `ParseAlg`, `recParse`, `ParseAlgFail`, `failTrace`) is not disjointness — it is the
  algebra API that `Soundness` depends on. Move to `Implicit/ParseAlgebra.agda`, leaving
  `Disjointness.agda` with `TraceDisj`, `¬FirstAut`, `¬NullableAut`, `¬FollowLastAut`
  (~120 lines).

Should be private in `Soundness.agda`: `≈→≅` (`:74`), `disc` (`:83`), `Aut` (`:86`),
`map*` (`:1064`) — three of the four should not exist at all (§8.9.3).

---

## 9. Sections that are fine

- `src/Theory/Instances/Monoid/Automata/NFA/Properties.agda` (72 lines) — entirely internal,
  no duplication, well named, and a strictly better proof than the 139-line legacy version
  it replaces. Nothing to change.
- `src/Theory/Instances/Monoid/Automaton/Disjoint.agda` — the reference for how this code
  should look: `stepStep`/`stepStop`/`stopStep`/`stopStop` are named for the case they
  handle and every one is a `∘⊢` chain. Only `reState` (§1.10) escapes.
- `src/Theory/Instances/Monoid/Automaton/Print.agda` — 60 lines, fully internal, two
  theorems, no cruft.
- `src/Theory/Instances/Monoid/Automata/NFA/Base.agda` — `Accepting` and `PotentiallyRejecting`
  are near-duplicates by construction, but that is the point (`NFA/Properties` proves them
  isomorphic), and the shared `stepBranch`/`step-out`/`step-in`/`map-step` idiom is already
  factored. Only `step-β` (§5.2) is dead.
- `src/Theory/Instances/Monoid/Automaton/SuffixChain.agda` — 67 clean lines; the only issue
  is that it is in the wrong directory, which it says itself (§6.4).
- `src/Theory/Instances/Monoid/Automaton/Implicit/SoundnessExamples.agda` — 64 lines, one
  instantiation per constructor, correctly scoped. Just needs the `Tests` rename.

---

## 10. Suggested order of work

1. Fix the broken `OPTIONS` pragma (§4.1) — one line, and the file is currently building
   under different flags from everything around it.
2. Drop the `public` at `Greedy.agda:39` and repoint `GreedyMax`/`TokenStream` at
   `SequentialUnambiguity.Nullable` (§2.2) — unblocks step 3.
3. Delete `Automaton/Greedy.agda`, `Automaton/GreedyExamples.agda`,
   `Automaton/ScratchPerf.agda`, and the dead definitions in §5.2, §5.3, §8.5, §8.9.6.
   (≈ 350 lines, two files, zero risk.)
4. Drop `private` at `Compile.agda:208`, delete `Soundness.agda:1069-1096`; delete
   `Soundness.agda`'s `≈→≅`, `map*`, and both `star-*⁻` copies (§8.9.2, §8.9.3). ~60 lines,
   entirely mechanical.
5. Name `alongδ` and `STOPᵇ` and use them at the 34 sites (§8.9.1). This is the single
   biggest readability win in the subsystem and needs no new mathematics.
6. Extract fixtures from the two `Implicit/*Examples.agda` files (§7.1) and rename all test
   files to `*Tests.agda` (§7).
7. `STEP`/`unrollTrace`/`fromCode` → `step-in`/`step-out` (§1.1, §1.2). Small, mechanical,
   and removes the two worst "why is this a λ?" moments in `Deterministic.agda`.
8. Internalise `dead-empty` (§1.3) and `deadNo` (§1.4).
9. Move `Lexicon`'s `Fin`/`Tup` prelude out (§6.1) and `SuffixChain` to `Suffix/` (§6.4);
   split `Soundness.agda` at its four module boundaries (§8.9.9).
10. Generalise `Unambiguous.agda` over the stop payload and delete
    `GreedyMax.unambiguous-TraceTo` (§2.4). ~60 lines.
11. Factor `Alt.MAlg`/`M'Alg` and `Seq.MAlg`/`Kleene.MAlg` (§8.9.4). ~170 lines.
12. Internalise `cancel` via `_⟜_` (§1.6), then `refuteExt` (§1.7). Largest and most
    interesting; do it last, when the rest is quiet.
13. Decide the fate of `src/Automata/**` (§2.7).
