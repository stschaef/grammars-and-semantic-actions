# `theory-core` cleanup notes

**Status (verified, not predicted).** The batch typechecks; the cut is made;
the greedy spike came back positive. Build recipe — the trap is the library
file, since `~/.agda/libraries` points at a cubical that is *not* the flake
pin. Use a file listing local `cubical` (`92166033`, which *is* the pin),
local `cubical-categorical-logic` (`82334ff`, also the pin), and
`src/grammar.agda-lib`:

    agda --library-file=<that file> Theory/Instances/Monoid/Combinator/Decidable/Dyck.agda

All five keep-set roots plus `Greedy/Base` exit 0, no unsolved metas.

Working notes for landing `theory-core` (6 commits, 100 files, 14,533 lines vs
`origin/main`). Not a plan of record — a list of things to keep in mind while
fixing. Nothing here has been typechecked; the numbers are from reading and
from import/reachability analysis.

## 1. Scope: what is actually in this batch

The batch is the combinator layer. Seed set:

```
Combinator.Decidable.{Base, Dyck, Star}
Combinator.Incomplete.{Base, Dyck, Star}
```

Transitive import closure of that seed = **59 of the 100 files**. The other
**35 files / 7,010 lines (48%)** are unreachable from it.

Unreachable, so out of this batch:

| group | modules | lines |
|---|---|---|
| LL / lookahead examples | `Decidable.{Arith, Arrow, Bracket, Widths, WidthsTests, Window, Routed, Productions, Polynomial, Lookahead}` | ~2,400 |
| STLC / Lambda | `Decidable.{STLC, Lambda}`, `Instances.STLC.Base`, `Instances.Lambda.*` | ~2,600 |
| `RecursiveDescent.{Base, Leaves, List}` | subsumed — see §4 | 419 |
| `Monoid.Lookahead.{Window, Tests}` | prospective | 193 |
| `Monoid.{Rank, Unicode.Base, Suffix.Memo}` | see §4 | 175 |
| `Type.{Category, Later.Base, Monad.NonDet, Top.Initial, Decidable.Ordered, Decidable.Route}` | see §4 | 546 |
| `Free.{Term, Closing}`, `Bags.Base`, `Decidable.ListLit`, `Incomplete.ListLit` | other presentations / extra examples | ~750 |

`Lambda` and `STLC` we probably want eventually, but they need the cleanup in
§5 first. The LL work goes to its own branch.

### Cut first

Verified closed: no file outside this set imports anything in it, so deleting
all ten at once cannot break the build. 1,090 lines.

```
Type.Monad.NonDet                     173   orphan
Type.Later.Base                       130   orphan (stack runs through Indexed/Tabulated/Derivative)
Type.Top.Initial                       95   orphan
Type.Decidable.Ordered                 83   orphan
Monoid.RecursiveDescent.List          185 ┐
Monoid.RecursiveDescent.Base          146 ├ closed cluster, subsumed by Incomplete
Monoid.RecursiveDescent.Leaves         88 │
Monoid.Rank                            47 ┘ sole importer is RecursiveDescent.Base
Monoid.Suffix.Memo                     62   orphan
Monoid.Lookahead.Tests                 81   goes with the Lookahead deferral
```

`Rank` is the only non-obvious entry — it looks live to a naive grep, but its
sole importer is itself in the cut.

**Kept by decision, both orphans today:**

`Type.Category` stays as the *migration target*: `TheoryTyCat` (`:33`) is a
genuine `LocallySmall.Category`, and the intent is to move off `THEORYTY`
(`Base.agda:63`), which is a `WildCat`. So the two packagings are not rivals
to choose between — one is where we are, the other is where we are going.
Keep both until the migration, and drop `SetTheoryTy:24` in favour of
`TheorySet` (HLevels is already imported at `:18`).

The Unicode lexer stays, and stops being an orphan once §2.5 lands. In the
interim — after `Lookahead/Tests` is cut and before the test rewrite — it has
no importer. That is expected; do not re-flag it as dead.

Then, needing a decision rather than a check: `Bags.Base` (321) is an orphan
and the only importer of `Free.Closing` (29), so cutting it removes the
quotient presentation of the free model. `List` is what we build on, but the
quotient is the canonical construction — keep-as-documentation call.

Not in the cut: `Instances.STLC.Base` and `Instances.Lambda.*` are orphans but
are the two-sorted *theory* instances, distinct from the
`Combinator.Decidable.{STLC,Lambda}` we may want. Parked. Same for the LL
suite — branch, not delete.

## 2. The central structural fact

**`Decidable` and `Incomplete` are one construction at two parameters.**

```agda
Maybe A = A ⊕ ⊤Ty        -- Monad/Maybe.agda:25, via ExceptMonad ⊤Ty
DecTy A = A ⊕ ¬Ty A      -- Decidable/Base.agda:41, ¬Ty A = A ⇒ ⊥Ty
```

Both are `A ⊕ E A` for a *failure-evidence* functor `E`. Maybe takes
`E = const ⊤Ty`; Dec takes `E = ¬Ty`. Every single difference between the two
files traces back to the variance and cost of `E`:

| the parser needs | which needs | Maybe (`E = ⊤`) | Dec (`E = ¬`) |
|---|---|---|---|
| `mapP` | an action of `E` on maps | `⊤` ignores it → one direction | contravariant → needs `g : B ⊢ A` too |
| `⊗`-strength `A ⊗ R B ⊢ R (A ⊗ B)` | `A ⊗ E B ⊢ E (A ⊗ B)` | free, `⊗⊕-distR` | **all of `Monoid.Precise`** |
| `<|>` via `R A & R B ⊢ R (A ⊕ B)` | `E A & E B ⊢ E (A ⊕ B)` | `orElse`, biased | `¬-⊕`, needs both |
| `fail` | `E A` inhabited | `⊤Ty-intro`, free | a refutation at that point |

### Answering "should Incomplete use `Monad.Maybe`?"

It already does, partially — `fmapM = Monad.fmap MaybeMonad`, `orElse`. But
pushing further along the *monad* axis will not dedup anything, because
**`DecTy` is not a monad — it is not even a functor** on theory types. `¬Ty`
sits in a contravariant position, so `dec-map` (`Decidable/Base.agda:110`)
demands maps both ways. `DecTy` is a functor only on the **groupoid** of
theory types.

So the shared interface is not a monad. It is:

```agda
record Failure where
  field
    E    : TheoryTy ℓ s → TheoryTy ℓ s
    Emap : A ≅ B → E A ⊢ E B      -- groupoid action: both instances have it
    E⊗   : A ⊗ E B ⊢ E (A ⊗ B)    -- the ⊗-strength
    E⊕   : E A & E B ⊢ E (A ⊕ B)  -- alternation
```

`R A = A ⊕ E A`, and `Rmap`/`R⊗r`/`R⊕&`/`Rfail` are derived once. Dec is
`E := ¬Ty` (paying `Precise`), Incomplete is `E := const ⊤Ty` (free).

The groupoid restriction is not a compromise — it is what the call sites
already pass. `Star.agda` Dec-side passes `mapP roll↑ unroll↑`, Incomplete-side
passes `mapP roll↑`: the same iso, with one half discarded.

### What this buys

Measured duplication between the two directories today:

| pair | lines | lines that differ |
|---|---|---|
| `Star.agda` | 89 | **9** (2 of which are the module name and one import) |
| `ListLit.agda` | 83 | 19 |
| `Dyck.agda` | 79 | 35 |
| `Base.agda` | 214 / 231 | the entire `Parser` record, `mkP`, `pAt`, `pApp`, `pless`, `pmore`, `seq`, `<|>`, `tok`, `anyTok`, `nil`, `fail`, `runP`, `fix` — structurally identical, `DecSet` → `MaybeSet` throughout |

Factoring over `Failure` makes `Star` and `Dyck` one file each and removes
~700 lines.

## 2.5 The lexer — BUILT

Three new modules, all green, all 0 holes / 0 postulates / no `TERMINATING`.

**`Unicode/Base.agda` — Unicode as an internal type.** This replaces the old
1:1 character table entirely, and it removes a postulate rather than routing
around one.

`String.Unicode` decides character equality through a *postulated* path
oracle (`mkUnicodeCharPath-yes`), so `DiscreteUnicodeChar 'a' 'a'` is
`yes ⟨stuck⟩`, `Eq.pathToEq ⟨stuck⟩` never becomes `Eq.refl`, and the
parser's `Sum.inl Eq.refl` branch can never fire. **No parser over
`String.Unicode`'s alphabet can ever run at `refl`-time.** That is why every
parser example in the repo uses a small enum alphabet, and why JSON on
`theory` maps Unicode into a finite `Ch` before parsing.

A code point is below 0x110000, so 21 bits carry one:

```agda
UChar = Bits 21          -- structural, so `_≟U_` reduces to Eq.refl
ch    : Char → UChar     -- via primCharToNat, a real primitive that reduces
text  : String → List UChar
```

`fromNat` uses `div-helper`/`mod-helper`, which are `BUILTIN NATDIVSUCAUX`
and GMP-backed, so a conversion is 21 machine steps, not 21 unary divisions.
Measured: the whole module, including a round-trip at `'\x10FFFF'`, checks in
0.9s.

**`Lex/Base.agda` — a lexer is `many` over a one-token parser.** No new
machinery at all:

- **rule priority** is `<|>`'s left bias (both branches run, first success
  wins) — so keywords listed before the catch-all identifier rule win;
- **skipping** is the action returning `nothing`; whitespace never has to
  become a grammar object, so we avoid the quadratic `Ws` guard that shrank
  JSON's suite on `theory`;
- **multi-character keywords** are just `seq`ed `tok`s.

`lex` is the sole boundary at which a token list leaves the theory.

**`Lex/Demo.agda` — it runs on real text.** A lexicon with `let`, `in`, a
skipped space and a catch-all variable, checked by `refl` in **2.8s**:

```agda
_ : lexDemo "let"    ≡ M.just (KLet ∷ [])
_ : lexDemo "le"     ≡ M.just (Var (ch 'l') ∷ Var (ch 'e') ∷ [])   -- not the keyword
_ : lexDemo "let x"  ≡ M.just (KLet ∷ Var (ch 'x') ∷ [])           -- space skipped
```

### Honest limit: ordered choice, not leftmost-longest

`<|>` gives PEG-style *ordered choice*. With keywords before identifiers that
is the standard practical lexer and handles every case above, but it is not
the classical leftmost-longest rule. Genuine longest-match is what
`Greedy/Base` is for, and that is still partial (below).

### Retracted

Two recommendations from earlier revisions were wrong and are withdrawn:

- *"push keywords into the grammar, keep the lexicon dumb."* That is what you
  are forced into when the lexer has no rules and no priority. With `<|>` and
  actions, none of it is necessary.
- *"port `Lex/Det` from main."* Unnecessary — see §2.6, the combinator route
  worked.

## 2.6 `Greedy` on our combinators — partial, and the automata port is dead

`Greedy/Base.agda`, green, 0 holes. The point was to avoid porting
`Grammar.Greedy` + `Parser.Base` + `Automata.Implicit`. It worked.

**The type transcribes with no new machinery**, with one correction: the
connective is `⊸`, not `⟜`. Ours is `(C ⟜ B) m = (r) → B r → C (m ++ r)` —
missing something on the *right* — whereas `Greedy` needs
`(A ⊸ C) m = (l) → A l → C (l ++ m)`, "what, appended after `w`, still makes
an `A`".

```agda
Greedy A = ⊕[ w ∈ String ] ((⌈ w ⌉ & A) ⊗ ¬Ty (((⌈ w ⌉ ⊸ A) & char⁺) ⊗ ⊤Ty))
```

`Greedy→leftmost` and `disjointGreedy-GreedyCompl` port unchanged.

**Hole (B) is proved.** `noExt-step` is `no-nonempty-extension-step` from
`Grammar/Greedy/Regex.agda` with the automaton deleted — `Trace … q` becomes
any `A`, `δ r disc q c` becomes the derivative `literal c ⊸ A`:

```agda
noExt-step : (c : Alphabet) {A : TheoryTy ℓA tt}
  → literal c ⊗ ¬Ty ((literal c ⊸ A) ⊗ ⊤Ty)
  ⊢ ¬Ty ((A & char⁺) ⊗ ⊤Ty)
```

The proof is `Precise`'s `flat` plus `cons-inj₁`/`cons-inj₂`. So **hole (A),
the residual step-inversion, is discharged by the precision of `literal c`**
rather than by inverting a `Trace` step. That is the whole dodge: precision
is a fact about `literal`, available to every grammar, where step-inversion
was a fact about one automaton's transition function.

It also confirms §2's prediction that greedy must live on the Decidable
branch — the certificate is a `¬Ty`, and `E = ¬Ty` is what buys refutations.

**Still owed:** the `löbG`-over-suffixes recursion that assembles the scan,
and hole (C)'s nullability side condition. The Grammar file's own comment
says everything past (A)–(C) is "composition with the standard linear-logic
combinators", so this is the remaining piece, not a new obstacle. Until it
lands, the lexer uses ordered choice (§2.5).

## 2.7 Guarded recursion vs initial algebras — one principle, and it wins

### There is already exactly one löb

`Justification.agda:46` has `löbFrom : IPtOrder → (R → order) → A → isSetA →
Löb R A`. Everything else in that file is `löbFrom` at a different order —
`löbByRank` (:102), `löbByLex` (:122), `löbBySuffix` (:145), `löbByFuel`
(:309) — and `löbMemo≡löbFrom` (:89) *proves* the memoised variant equals the
plain one. The apparent zoo is a family of well-founded orders, not a family
of induction principles.

At the grammar level it surfaces as one combinator plus one payment rule:

```agda
löbG : (ty (▷ A) ⊢ ty A) → ⊤Ty ⊢ ty A                              -- Suffix/Base:241
▷⊗r : (c : Alphabet) → ty (▷ A) & (literal c ⊗ C) ⊢ literal c ⊗ (ty A & C)  -- :238
```

Anything guarded should be written with these two and nothing else.

### `hylosFromGuard` is the unification — but it cannot be applied here

**Correction to an earlier claim.** I wrote that the guarded route to the
recursor was "built and unused", implying it was ready. It is not, and the
reason is precise.

`Guard`'s tensor clause quantifies over *all* splittings:

```agda
Guard (⊗e o G) m root = (sp : Split o m) (a) → Guard (G a) (parts sp a) root
Split o m = Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m)   -- Code/Container:29
```

`Split` is blind to what the slots contain. So for the Kleene cons branch
`⊗e _⊙_ (two (k A) (Var tt))`, `Guard` demands `(tt , parts sp 1) < (tt , m)`
*for every* split — including `([] , m)`, which asks for `m < m`. False by
irreflexivity, for every `A`, nullable or not.

**So `Guard` cannot guard a Kleene star.** `hylosFromGuard` is unused because
it is inapplicable to the codes this library actually uses, not because nobody
got round to it. `Inductive/Base.rec`'s `{-# TERMINATING #-}` is load-bearing.

`fold` itself is fine — it takes `Hylos F` as a hypothesis. What is missing is
a *producer* of `Hylos` for star-like codes.

### The fix already exists in miniature: `PayR`

`GuardedSplit.agda:54` is the content-*aware* version of the same idea:

```agda
PayR {X = X} = (m : ↓M tt) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
  → X (ms zero)                                    -- ← the content of the left slot
  → R (tt , ms (suc zero)) (tt , m)
```

It receives the left slot's inhabitant and only then owes the order fact, which
is exactly how `◂-lit` discharges it for a literal head. `Guard` is its
content-blind cousin. Generalising `Guard`'s `⊗e` clause to `PayR`'s shape —
quantify over splits, take the non-recursive slots' contents as hypotheses —
should make `hylosFromGuard` apply to every LL-shaped code, and then `fold`
replaces `rec` and the pragma goes.

That is the concrete next task for §4, and it is one clause of one definition.

### (superseded) `hylosFromGuard` as drop-in

`Justification.agda:195`:

```agda
hylosFromGuard : (F) → (∀ x m → Guard (F x) m (x , m)) → Hylos F
```

`Guard` (:150) is local contractivity, defined by recursion on the *code*:

```agda
Guard (Var x)   m root = (x , m) < root          -- a recursive position drops
Guard (⊗e o G)  m root = (sp : Split o m) (a) → Guard (G a) (parts sp a) root
Guard (k A)     m root = Unit*                   -- constants are free
```

and `hy` (:218) is literally `löb` at the family `Fn A B x m = A x m → B x m`,
with `hylo-unfold` = `löb-unfold` + `mapG≡map`. So **contractivity ⟹
hylomorphisms, by löb, with no initial-algebra semantics anywhere.**

### The experiment: the recursor, by löb, without the pragma

Added to `Guarded/Base.agda` (green, downstream green):

```agda
fold : (∀ x m → isSet (A x m)) → (∀ x → ⟦ F x ⟧TheoryTy A ⊢ A x) → ∀ x → μ F x ⊢ A x
fold isSetA α = hylo isSetA (unroll F) α

fold-unfold : ∀ x → fold isSetA α x ≡ α x ∘⊢ map (F x) (fold isSetA α) ∘⊢ unroll F x
fold-unfold isSetA α = hylo-unfold isSetA (unroll F) α
```

Compare the two routes to the same recursor:

| | `Inductive/Base.rec` | `Guarded/Base.fold` |
|---|---|---|
| side condition | none | `Hylos F`, i.e. `Guard` |
| termination | `{-# TERMINATING #-}` (§4) | none — `löb` is a term |
| β-law | `refl` | `fold-unfold`, a proof |
| descent | through `map (F x)`, invisible to Agda | through the order |

The `refl` β-law of the pragma version is worth less than it looks: it is
`refl` only because the definition was *asserted* to terminate. So the answer
to "can recursors be defined by guarded recursion instead" is: completely, and
here it is strictly better. What makes `μ F` *initial* is then `löb-uniq`, not
a separate induction principle — that is where the unification actually lands.

**Caveat.** `hylo` forces `A B : (x : X) → TheoryTy ℓB (xs x)` at the *same*
level, so `fold` only lands in families at μ's own level. Level-polymorphic
folds need `Hylos` generalised first.

### Why the automaton was really there

Earlier I said the automaton in `Grammar/Greedy` was there for step-inversion,
and that precision replaces it (§2.6). Half right. It was also supplying the
thing the löb recurses *on*: the state.

`löbG` descends the suffix; at each step `noExt-step` hands back a fact about
`literal c ⊸ A` — the derivative. For the löb to close, that derivative has to
be a grammar of the family you started in. An automaton makes this free: `δ q c`
is another state. Without one, the family must be closed under derivatives —
Brzozowski. So the missing piece is not a lemma but a structure:

```agda
∀ c → Σ[ A' ∈ … ] (literal c ⊸ A ≅ A' c)
```

And this is the same condition as `Guard`: a code whose recursive positions sit
under a `⊗` with a literal head is contractive *and* derivative-closed. One
condition, two uses — which is the sharpest form of the guarded/inductive
coincidence in this setting, and the reason `cfg-derivative`'s syntactic δ is
the natural next step rather than a detour.

### Point-free `noExt-step`: not done, and what it needs

The transposed goal is `(literal c ⊗ N) & ((A & char⁺) ⊗ ⊤Ty) ⊢ ⊥Ty`.
Composing to it needs three lemmas that do not exist yet, all element-level in
the `Precise` tier:

1. positive precision — `(literal c ⊗ X) & (literal c ⊗ Y) ⊢ literal c ⊗ (X & Y)`;
   only the ¬-form (`lit⊗-precise`) is there
2. residual uncons — `(literal c ⊗ Y) & A ⊢ literal c ⊗ (Y & (literal c ⊸ A))`
3. residual/tensor distribution **under non-nullability** —
   `literal c ⊸ ((A & char⁺) ⊗ B) ⊢ (literal c ⊸ A) ⊗ B`

(3) is false without the `char⁺`: if `A` matches `ε` the split cannot be
shifted. That is *why* `char⁺` appears in `Greedy`'s statement — a detail I had
read as bookkeeping.

## 2.8 Scale: measured, and it is roughly linear

The open question after §2.5-2.7 was whether `refl`-evaluation survives past
toy inputs. It does. Baseline (module loading, no test) is 2.5s; the marginal
column subtracts it.

**Lexer** — `Lex/Demo`, input `"let x "` repeated, 4 alternatives, 21-bit
alphabet:

| chars | tokens | total | marginal |
|---|---|---|---|
| 96 | 32 | 2.5s | ~0 |
| 768 | 256 | 3.8s | 1.3s |
| 1536 | 512 | 5.6s | 3.1s |
| 3072 | 1024 | 8.6s | 6.1s |
| 6144 | 2048 | 17.3s | 14.8s |

**Dyck** — `Incomplete/Dyck`, fully nested `((((…))))`, so the parse tree is as
deep as the input is long:

| tokens | depth | total | marginal |
|---|---|---|---|
| 128 | 64 | 2.7s | 0.2s |
| 512 | 256 | 3.3s | 0.8s |
| 1024 | 512 | 4.8s | 2.3s |

Marginal cost roughly doubles as input doubles in both, i.e. linear to mildly
superlinear. **6144 characters is about 150 lines of source, checked in 17s.**
Nesting is not the problem: depth 512 is cheaper than 1024 flat tokens.

### What the numbers actually say

Dyck at 1024 tokens costs 2.3s where the lexer at 1024 tokens costs 6.1s. The
difference is not structure — it is that `oneTok` offers four alternatives and
`<|>` evaluates *both* branches, and that each `tok` compares a 21-bit
character. So the constant is **per-alternative, per-token**.

Extrapolating honestly: a real lexicon with ~40 rules rather than 4 would pay
roughly ten times the per-character constant, putting 6144 characters near
150s. That is the wall, and it is a constant-factor wall, not a complexity one.

**Which makes the parked LL(1) work the fix, not a luxury.** `look⊗`/`Λ₁`
dispatch on the first character instead of trying every alternative; that is
exactly the constant this measurement exposes. §1 sends the LL suite to its own
branch on scope grounds — that stays right for *this* batch, but it is now on
the critical path for anything real, rather than being speculative.

## 2.9 The guarded Kleene fold — BUILT

`KleeneStar/Guarded.agda` + `GuardedTests.agda`, green, 0 holes, 0 postulates,
no pragma. `fold*g` is the same fold as `KleeneStar.fold*r` but by `löb`.

The route is *not* fixing `Guard`. §2.7's correction stands: `Guard`'s `⊗e`
clause quantifies over all splits and so cannot see that a cons consumes. But
generalising it does not help either, because `hylosFromGuard` serves `hylo`
at an *arbitrary* coalgebra, and a coalgebra into an arbitrary carrier really
can fail to terminate — that is a property of the coalgebra, not of the
functor. Asking `Guard` to supply it was the category error.

What the star actually needs is the one missing hypothesis — the head
consumes — and `PayR` already has exactly that shape:

```agda
NonNull A = (m : String) (ms : interpIn _⊙_ ↓M) → op _⊙_ ms Eq.≡ m
  → A (ms zero) → ms (suc zero) ◂ m
```

**Non-nullability is stated internally.** `NonNull` above is the *external*
reading — it quantifies over model elements and names the order. Clients state
the internal one and never see either:

```agda
¬Nullable A = A & εTy ⊢ ⊥Ty                        -- a ⊢-term
¬Nullable→NonNull : ¬Nullable A → NonNull A        -- the only place they meet
literal-¬Nullable : (c : Alphabet) → ¬Nullable (literal c)
```

which matches `Grammar/SequentialUnambiguity/Nullable`'s
`¬Nullable A = uninhabited (A & ε)`, so the vocabulary agrees with the older
tree. `fold*g` now takes `¬Nullable`; `NonNull` and `◂` stay internal to the
proof. Given it, the fold is three lines of composition and one löb:

```agda
step   = cons ∘⊢ (id⊢ ,⊗ (⇒-app ∘⊢ &-swap)) ∘⊢ ▷⊛r GB.suffixLöb pay
body   = ⊕-elim& (step ∘⊢ &-swap) (nil ∘⊢ π₂) ∘⊢ (id& unroll↑)
fold*g = ⇒-app ∘⊢ ((GB.löb (λ _ → ⇒-intro body) tt ∘⊢ ⊤Ty-intro) ,& id⊢)
```

The family being fixed is the fold itself as an internal function,
`A * ⇒ ty B` — which is `hylosFromGuard`'s `Fn` trick, done at one grammar
instead of a whole system. Everything draws from `Guarded▷.löb`; there is no
second induction principle.

`GuardedTests` confirms it *computes*: `countAs (a ∷ a ∷ a ∷ []) ≡ just 3` by
`refl`, and `countAs (b ∷ []) ≡ nothing`.

**`◂-lit` is already the `NonNull` witness for a literal**, so every
literal-headed production gets its payment for free — which is the LL fragment
(§2.8).

### The lexer is off the pragma

`semact-*g` and `semact-skip*g` are the two star actions built on `fold*g`,
and `Lex/Base.lex` now uses the second. The lexer's live path no longer runs
through `Inductive/Base.rec`. Measured: `Lex/Demo` checks in 2.5s, against
2.8s on `rec` — the same, so löb costs nothing here.

Two prices, both real:

- **`isSet X`.** Löb fixes a family and wants it set-valued; `rec` did not.
  `Lex/Demo` pays it by retracting `Tok` onto `Unit ⊎ (Unit ⊎ UChar)`.
- **the non-nullability witness**, which is the point — it is what stops a
  lexer looping on ε, and `rec` was simply not asking.

Non-nullability composes, so a token grammar states it the way it is built:

```agda
⊗-¬Nullable    : ¬Nullable A → ¬Nullable (A ⊗ B)
⊕-¬Nullable    : ¬Nullable A → ¬Nullable B → ¬Nullable (A ⊕ B)
char-¬Nullable : ¬Nullable char
```

and `Lex/Demo`'s obligation is six lines of exactly that shape, with no order
and no model element in sight.

### What this leaves

`semact-*` and `semact-skip*` remain, still on `rec`. They are the
low-ceremony option — no `isSet`, no `¬Nullable` — exactly as `fold*r` sits
beside `fold*g`, so the pair is deliberate rather than dead. But
`semact-skip*` now has no client, so if the ceremony proves cheap in practice
it should go.

The pragma is still under `semact-*`, hence under `Grammars/Dyck`'s action and
the Dyck test suites. Retargeting those is the same wiring again, and needs
`¬Nullable` for the Dyck body — which is `⊗-¬Nullable (literal-¬Nullable lp)`.

## 3. Per-module verdicts

Each of these was checked by import graph plus symbol-level grep, not by eye.

**`Monoid.GuardedSplit` — external, and by a whole layer.** Its module
parameters are `(σeq : SortedEqns MonSig ℓ'') (V) (vs) (𝒫)` — it is generic
over any theory whose *signature* is `MonSig`. Every other file in
`Instances/Monoid/` takes `(Alphabet) (isSetAlphabet)`. This one takes nothing
from the instance layer: not `Alphabet`, not `Strings`, not
`listPresentation`. It is a `Type/`-level module with a signature constraint,
filed under `Instances/` because it mentions `MonSig`.

Two symptoms confirm it. `_⊛_` (`:43`) is a *third* name for the binary tensor
— alongside `⊗ᵘ[_]`/`⊗[_][_]` in `Operation/Base` and `_⊗_` in `Strings` —
and exists only because the file cannot name whichever concrete tensor its
caller uses. And its header justifies the `MonSig` restriction by citing two
clients, bags and strings; bags is leaving this batch, and neither client
needed it at the instance layer in the first place.

It is genuinely used — `Suffix/Base.agda:163,170` take `PayR` and `▷⊛r` to
build the `▷⊗r` both combinator `Base`s call — but "is it used" was not the
question. Move it beside `Type/Guarded/Base` as the arity-2 case, or fold the
one lemma into `Suffix/Base`.

**`Monoid.Precise` — used, and it is exactly the Dec/Maybe cost gap.** Imported
`public` by `Decidable/Base.agda:26` (`dec-lit⊗↑`, `dec-char⊗↑`) and *not* by
`Incomplete/Base` — the Incomplete header says so in as many words ("no
precision lemma is spent"). In the §2 framing, `Precise` is the `E⊗` field of
the `Dec` instance. Keep, and say that in its header.

**`Monoid.Suffix` — `Base` yes, `Memo` no.** `Suffix/Base` is imported `public`
by both combinator `Base`s; it is where `▷`/`□` come from. `Suffix/Memo` has
zero importers.

**`Monoid.Rank` — no.** Zero importers.

**`Monoid.RecursiveDescent` — agreed, subsumed.** All three files are
unreachable from the seed set, and `Base`/`List` re-declare `Parser`, `seqP`,
`mapP`, `onSuccess`, `Maybe⊗r` — the `Incomplete` versions of exactly these.
Drop; if anything in `Leaves` is wanted, port it onto `Incomplete`.

**`Monoid.Lookahead` — `Window`/`Tests` off, but `Base` blocks.** `Window` and
`Tests` are unreachable and go. `Base` cannot: `Λ₁`, `M₁`, `look⊗`,
`Λ-disjoint`, `Λ-total`, `σ⊕`, `tk`, `ε₁` are load-bearing in *both*
combinator `Base`s — `look⊗` is how each one dispatches on the first token, so
without it the batch does not compile.

That is a fact about the current combinator design, not an argument for
keeping the file. The live option is to restructure the combinators so
first-token dispatch does not route through the lookahead-class machinery, and
then all of `Lookahead` leaves together. That is a bigger call than a scope
cut; flagging it rather than deciding it.

**`Type.Guarded` — `Base` yes; `Justification` is ~15% used.** `Guarded/Base`
has real clients. `Guarded/Justification` is 321 lines of which the batch uses
three definitions: `löbFrom` (`Suffix/Base:153`), `löbBySuffix` (`:268`), and
one use each of `löbF`/`decSuffix`. Unused by anything reachable: `löbMemo`,
`löbMemo≡löbFrom`, `hylosFromGuard`, `löbByLex`, `löbByFuel`, `löbByMeasure`,
`mapG`, `mapG≡map`, `uniqAux`, `unf`, `nextF`, `▷F`, `Fn`, `isSetFn`. Its own
header asks "how much of this is actually used?" — that is the answer. Keep the
three, sequester the rest.

**`Type.Decidable.Base` — yes.** `DecTy` is the Dec combinator's result type.

**`Type.Decidable.Ordered` — no.** Zero importers.

**`Type.Decidable.Route` — no, and it leaves cleanly.** Only imported by the LL
files that are going. Every `DiscreteEq` user is also in the drop set
(`Widths`, `Arrow`, `Routed`, `Window`, `Bracket`, `Arith`), so nothing has to
be extracted for this batch. `DiscreteEq` (`:45`) is still in the wrong home —
it has nothing to do with routing — but that problem travels with the LL
branch.

**`Type.Later` — `Base` no, the rest yes.** `Later/Base.agda` (130 lines) has
zero importers; the stack runs through `Indexed`, `Tabulated`, `Derivative`,
`Poset`, `Tag`, `Lex`. Also: all six `Later/*` files carry the same
copy-pasted four-line `WARNING for now I have been treating this as a place to
sequester…` banner. One README, not six headers.

**`Type.SemanticAction` — yes.** `Base` reaches the batch via
`Monoid.SemanticAction`, `Pipeline` via `Strings.agda:37`.

**`Monoid.Examples` vs `Monoid.Grammars` — one directory, and the names are
backwards.** `Examples.agda` (49 lines) holds alphabet-*generic* grammar
definitions (`LiteralStar`, `dyckBranch`, `DyckCode`, `Dyck lp rp`);
`Grammars/Dyck.agda` (110 lines) is the concrete instantiation at
`Br = {lp, rp}` plus its semantic action, and it imports `Examples`. So the
file called "Examples" holds the reusable library and the one called
"Grammars" holds the actual example. `Grammars/` becomes the directory
throughout, the generic part moving to `Grammars/Base.agda` or into each
`Grammars/<Name>.agda`; no top-level `Examples.agda`.

**`Monoid.Types` — confused, agreed.** Three unrelated things in one file:
(a) a `public` re-export wall over ten modules (`:32-44`), (b) leftover h-level
lemmas that `Strings` "does not state" (`:53-97`), (c) `_≟M_`, deciding
lookahead-class equality (`:103`). Its own header records that it was carved
out of `RecursiveDescent.List` — which is now leaving, so the original reason
for the file is going away. Suggest: the re-export wall becomes
`Monoid/Prelude.agda` and is honest about being one; the h-level lemmas go to
the connectives they are about (see §5); `_≟M_` goes to `Lookahead/Base`.

Note the re-export wall is also why naive reachability overstates usage — a
`public` open drags a module into the closure whether or not any name is
consumed. The per-module verdicts above are symbol-level, not closure-level.

**`Monoid.Residual` — five things in one file, agreed.** Sections:

| lines | content | should be |
|---|---|---|
| 36-66 | `castEq`, `castEqPathP`, `two-η` | `Eq`/`Fin` plumbing — `two-η` beside `two` in `FinData.More`, `castEq` in `Theory.Base` |
| 67-213 | `⟜` and `⊸` written out at `_⊙_`'s two slots | the real content; this is the `Type/Residual/Base` generic `Resid`/`FocusedOperation` specialized to arity 2 |
| 214-370 | `⟦⊗e⟧`, `⟦⊗e⟧⁻` and the four triangles | code/functor plumbing → `Type/Code/` |
| 371-381 | `Konst`, `Konst-map`, `Konst-pt` | the constant grammar — unrelated to residuals, parked here. `Type/`-level. (The LL work renamed this `Leaf`; pick one name.) |

**`Monoid.Strings` — cleanup, and it is four tiers interleaved.** Not merely
long. The file's own header claims one tier ("every definition here introduces
a *connective* by matching on its own elements"). What is actually in it:

| tier | examples | belongs |
|---|---|---|
| connectives by matching | `⊗⊕-distL:100`, `⊗⊥-annihL:117`, `⊗-assoc:137`, `⊗-unit-l:169` | here — the declared purpose |
| free-monoid list facts in `Eq` | `++-assocEq:127`, `++-unit-rEq:131` | a `List`/`Eq` More module; nothing to do with grammars |
| cubical plumbing | `two≡:214`, `⊗PathP':222`, `transportEq:237`, `unit-l≡:246`, `transportEq-nat:268` | `transportEq` is a general `Eq.transport`-vs-`transport` fact, not string-specific at all |
| h-levels | `isSetString:206`, `isPropEqString:209` | with the other h-levels (§5.7) |

And one law is written two ways in adjacent definitions: `⊗⊕-distL:100`
matches the splitting directly, while its mirror `⊗⊕-distR:108` goes through
`⊗-elim`/`⊗-intro` with explicit level annotations (`{ℓs = two ℓA ℓB}`). Same
tier, same shape, two idioms, twelve lines apart.

Separately, `⊗-assoc:137` restates by hand what the generic `eqn→Iso` in
`Type/Operation/Base` exists to produce. The comment at `:119-126` explains
why — `eqn→Iso` gives the *flat* convolution over one valuation, which is a
different type from the nested `(A ⊗ B) ⊗ C`, and the result has to land in
`Eq` so it reduces on canonical strings. That reason is sound, but it means
the generic equation-lifting machinery does not serve the one law every parser
composes. Worth treating as a gap in `Operation/Base`, not as a Strings
problem.

**`Monoid.Unicode.Base` — the conflation is real.** Two layers glued together:
lines 24-53 are a metalanguage `UnicodeChar → Maybe Alphabet` table with
`with`-matching on `DiscreteUnicodeChar` — that is *lexing-for-Unicode*, an
external convenience for literal test cases. `module Internal` (55-66) is the
actual idea — a lexicon is a semantic action from the free monoid on
characters — and it is twelve lines. The general notion is buried inside the
concrete one. Split into `Lexer/Base.agda` (generic: a lexicon is
`Σ → Maybe Τ`, a lexer is its `scanAction`, parameterized over *both*
alphabets) and `Lexer/Unicode.agda` (the instantiation plus the external
entry point). The file has zero importers, so this can wait until it comes
back — but check the older branches first, which had this separation.

## 4. Correctness item

**Six `{-# TERMINATING #-}` pragmas**, against the standing rule:
`Type/Inductive/Base.agda:41,51`, `Type/Inductive/HLevels.agda:154,169`,
`Type/Coinductive/Base.agda:44,54`. They sit on `rec`, `μ-η'`, `corecHomo`,
`ν-η'` — the initial-algebra recursor and its uniqueness proof — so every
`μ`-based parser in the batch inherits an unchecked recursion.

The recursion is structural; Agda cannot see through `map (F x)`. The repair is
to fuse: define `rec` and `map` mutually, recursing on the `Functor` code so
the descent is visible. This is the one finding that touches the guarantees the
library advertises, and `Inductive/Base` is in the keep-set.

## 5. Cross-cutting cleanups

Cheap and mechanical, independent of the scope decisions above.

1. **`Decidable/STLC.agda:33-993` is a hand-written 31×31 `_≟T_` table** — 961
   lines, 48% of that file, ~7% of the whole diff. Derivable in ~4 lines from
   `Tok ≅ Fin 31` and `discreteFin`. This is most of what "STLC needs to be
   cleaned up" means.
2. **The `DiscreteEq → isSet` incantation appears 7×**, verbatim, each with its
   own `where open import … using (yes ; no)`: `Types:28`, `Routed:104`,
   `Widths:127`, `Arrow:57`, `Arith:77`, `Productions:53`, `Lookahead:54`. One
   `DiscreteEq→isSet` beside `DiscreteEq` removes all seven.
3. **`DiscreteEq` already exists** but 7 `_≟T_` signatures spell the type out
   inline anyway (`Widths:29`, `ListLit:26` ×2, `Bracket:30`, `Arith:26`,
   `STLC:32`, `Lambda:23`) while neighbouring files in the same directory do
   use it.
4. **`Code = Functor ℓM NT (λ _ → tt) tt` and `_⊗c_ = ⊗e _⊙_ (two F G)`**
   copy-pasted verbatim into `Arith:51,54`, `Arrow:63,66`, `Widths:68,71`.
   Belongs in one place, parameterized over `NT`. (All three files are leaving,
   but the same paste will recur on the LL branch.)
5. **`SetTheoryTy` (`Type/Category.agda:24`) is a verbatim redefinition of
   `TheorySet` (`Type/HLevels.agda:47`)** in a module that already imports
   HLevels at line 18 — replace it with the import. The file also duplicates
   `THEORYTY` from `Base.agda:63`; since `Type/Category` is being kept (§1),
   that is a choice to make rather than a duplicate to drop.
6. **`&≡` (`Product/Binary/Base.agda:59`) and `&-η'` (`:64`) have identical
   types**, proved two different ways. `&-η'` is not an η law.
7. **`Type/HLevels.agda` is a central h-levels hub** importing 14 sibling
   modules, while `Type/Inductive/HLevels.agda` keeps μ's h-levels local. Two
   conventions; locality is the one we want. This is also where `Monoid.Types`'
   stray `isSet⊗2`/`isSetεTy`/`isSetLiteral` should land.
8. **Layout is a third convention.** `src/Grammar/` uses
   `Bottom.agda` + `Bottom/{Base,Properties}.agda`. `Theory/Type/` has
   `Bottom/Base.agda` with no re-export, 10 of 21 directories holding a single
   `Base.agda`, and three flat modules (`Category`, `Distributivity`,
   `HLevels`) beside them. Also `src/Theory/Type/Cont/` is an empty leftover
   directory.
9. **`Theory/Base.agda:13` names the presentation `P`**; the other 42 modules
   name it `𝒫`, and `FreePresentation`'s own field is `P`, so `Theory.Base`
   shadows it.
10. **Eight files ship `-- TODO is/how much of this actually used?` as their
    first line.** §3 answers all of them; the answers should replace the
    headers rather than ship as them.
11. **`Cubical/WildCat/LocallySmall/Base.agda:1` says `TODO put in ccl`**, and
    this branch already bumps the c-c-l pin in `flake.lock`. Good moment to
    land it, along with `Cubical.Algebra.Theory.Finitary` (83 importers — the
    actual foundation of the branch) and `Cubical.Data.Nat.WFOrder`.
12. Minor: `Sum/Binary/Base.agda:42` `inr : A ⊢ B ⊕ A` reads as injecting on
    the left; `_,&_`/`_,&p_` (`Product/Binary:41,72`) are alias definitions
    with no type signature; imports inside `where` blocks at `Arith:80`,
    `Arrow:60`, `Widths:130`, `Types:59`, `Routed:106`, `Lookahead:56`; and
    mid-body imports at `STLC:1232,1255`.

Also: `STLC.agda:1257` defines a private `_>>=_` for `Cubical.Data.Maybe` while
`Type/Monad/Maybe.agda`'s `MaybeMonad` already exists; and `STLC.agda:1334`
`eqTok : Tok → Tok → Bool` discards the `_≟T_` evidence, which is precisely why
that file has to write pass 2 twice — once as `Maybe` (`:1343`) and again
"completed" as a decision (`:1513`). Passes 1-3 there are plain Agda functions
over inductive `Tree`/`ATm`, not `⊢`-terms — a metalanguage front end inside
`Instances/`.

## 6. Deferred: the categorical cleanup

Held for a separate conversation, but §2 is already a down payment on it — the
`A ⊕ E A` framing says the Dec/Maybe split is a choice of failure-evidence
functor, and it predicts exactly which lemmas each instance has to pay for
(`Precise` on one side, nothing on the other). Two threads worth pulling when
we get to it:

- `E` is a functor on the groupoid, not the category. That is the same
  restriction that forces `dec-map` to take two maps and `mapP` to take an
  iso. Worth asking whether the right home for the parser combinators is a
  category whose maps are already isos, in which case the restriction stops
  being a special case.
- `Type/Residual/Base` gives `Resid`/`FocusedOperation` for an arbitrary
  operation and arity, and `Monoid/Residual` is that at arity 2. Most of §3's
  "too much in one file" is the specialization not being written *as* a
  specialization. Same shape as the `Grammars/` vs `Examples` mix-up: the
  generic thing and its instance sharing a file.

Plus whatever the new ideas are — that discussion should come after the
scope cuts in §1 land, since half of what is in the tree today will not be
there to refactor.
