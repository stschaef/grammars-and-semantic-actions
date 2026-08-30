# Audit: parser-combinator / LL / Routed subsystem

Scope: `src/Theory/Instances/Monoid/Combinator/**`, `.../Lookahead/**`,
`.../Residual.agda`, `.../Residual/Laws.agda`, `src/Theory/Type/Decidable/{Base,Route}.agda`.
7795 lines across 40 files.

Headline: the *core* is in excellent shape. `Combinator/Core.agda`,
`Type/Decidable/Route.agda`, `Combinator/Syntax.agda`, `Grammars/{Arith,Dyck,Polynomial,Regex}.agda`
and the three `Base.agda` answer instances are essentially pure DSL terms,
answer-generic, and well factored. Everything below is about the periphery:
the `Decidable/*` client directory, which is where the old (pre-`Route`,
pre-`AnswerFunctor`) development still lives, half-migrated, and where all
the duplication, all the forbidden tests, and all the unjustified escapes are.

Findings ranked by severity.

---

## S1. `Decidable/STLC.agda` is four files welded into one (2008 lines)

`src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda`

Four unrelated developments in one module:

| lines | content | belongs |
|---|---|---|
| 29–993 | `data Tok` (31 ctors) + `_≟T_` — **962 lines** of `Sum.inr λ ()` | derived, see S2 |
| 997–1222 | the table, the parser, and 29 forbidden-shape tests | `Grammars/STLC/{Ty,Parser}.agda` + `Tests.agda` |
| 1225–1500 | metalanguage compiler front end (`Tree → Maybe ATm`, `scope`, `infer`) | not this subsystem at all |
| 1501–2008 | external `Scoped`/`Typed` inductive families + `scoped?`/`typed?` | a `Theory/Examples/STLC/Typing.agda` |

### S1a. 962 lines of quadratic `≟` boilerplate

```agda
32  _≟T_ : (a b : Tok) → (a Eq.≡ b) Sum.⊎ ((a Eq.≡ b) → Empty.⊥)
33  kbool ≟T kbool = Sum.inl Eq.refl
34  kbool ≟T knat = Sum.inr λ ()
    …960 more lines…
993 vxs ≟T vxs = Sum.inl Eq.refl
```

**Fix.** Give `Tok` a `Fin 31` code/decode pair (31 + 31 lines, every clause
`Eq.refl`) and add one generic lemma next to `DiscreteEq` in
`src/Theory/Type/Decidable/Route.agda:265`:

```agda
decEqRetract : {X : Type ℓX} {Y : Type ℓY}
  → (c : X → Y) (d : Y → X) → (∀ x → d (c x) Eq.≡ x)
  → DiscreteEq Y → DiscreteEq X
```

`Eq`-based so the resulting proof is `Eq.refl` on canonical input — this is
what the comment at `Grammars/PolyGrammar.agda:53-57` correctly warns about
(`Eq.pathToEq` yields a stuck proof and `dec-lit⊗-at` never computes), and it
is exactly why the boilerplate exists everywhere. Do it once, in the DSL's
own decidability module, not eight times by hand.

### S1b. The compiler front end is entirely outside the DSL

`STLC.agda:1271–1424` is a `Maybe`-monadic pass over an *untyped rose tree*:

```agda
1249  _>>=_ : {A B : Type ℓ-zero} → M.Maybe A → (A → M.Maybe B) → M.Maybe B
1271  toTy : Tree → M.Maybe ATy
1283  toTm : Tree → M.Maybe ATm
1336  scope : List Tok → ATm → M.Maybe BTm
1382  infer : List ATy → BTm → M.Maybe ATy
```

Unjustified. The parse already *is* a `μ`; `SemanticAction (S Tm) ATm` built
with `semact-rec`/`semact-⊗`/`semact-⊕ᴰ` (all in
`src/Theory/Type/SemanticAction/Base.agda`) would produce `ATm` directly with
no `Tree`, no `Maybe`, and no partiality — `toTy`/`toTm`'s `M.nothing`
fall-through cases are *unreachable*, they exist only because `Tree` has
thrown away the tag the parse carried. This is precisely the escape the
project exists to avoid: an algorithm that should be a DSL term, written by
matching on external model data.

Compare `Grammars/Regex.agda:79-85`, which does the same job correctly:

```agda
regAct : (r : Reg t) → SemanticAction (ty ⟦ r ⟧) (Tree r)
regAct (r ⊗r s) = semact-⊗₂ (regAct r) (regAct s)
```

**Fix.** Replace `Tree`+`toTy`/`toTm` by `SemanticAction`s. Delete the local
`_>>=_` (1249). This also removes the only client of `Productions.toTree`
(S1c).

### S1c. `Productions.toTree` matches the convolution by hand

`Decidable/Productions.agda:228-256`

```agda
229    Kst : X → TheoryTy ℓAlph tt
230    Kst _ _ = Tree                      -- raw λ over the semantics
235    kids (tm c ∷ β) m (ms , e , g) = kids β (ms (suc zero)) (g (suc zero))
```

`Kst _ _ = Tree` is `Δ Tree` written by hand, and `kids` splits the `⊗ᵘ`
tuple externally. The DSL has both: `Δ` (`SemanticAction/Base.agda`) and
`Δ-⊗`/`semact-⊗`. Unjustified — the whole block is `semact-rec` over a
`⊕ᴰ`-elim, and the `Empty.rec*` cases at 241/246 disappear.

### S1d. 508 lines of ordinary Agda typechecker

`STLC.agda:1501–1935`: `_∈_`, `_∈?_`, `Scoped`, `scoped?`, `_≟ty_`, `Typed`,
`unique`, `ArV`/`PrV` views, `typed?`. Nothing to do with parsing. `theD`
/`theNotD` (1938–1952) re-derive `theYes`/`theNo` for the external `Dec`.
Move to its own module; the parsing subsystem should not carry it.

---

## S2. 1138 lines of duplicated `≟` boilerplate in the subsystem

Counted as `Sum.inr λ ()` clauses:

| file:line | type | lines |
|---|---|---|
| `Decidable/STLC.agda:32` | `Tok` (31) | 962 |
| `Grammars/PolyGrammar.agda:71` | `Tok` | 92 |
| `Decidable/Bracket.agda:30,78,89` | `Tok`, `Maybe Tok`, `Cls` | 87 |
| `Decidable/Lambda.agda:23` | `Tok` (5) | 26 |
| `Decidable/ListLit.agda:26` | `Tok` (4) | 17 |
| `Incomplete/ListLit.agda:26` | `Tok` (4), **verbatim copy of the above** | 17 |
| `Grammars/ArithGrammar.agda:33,76` | `Tok`, `Tag` | 20 |
| `Decidable/Arrow.agda:41` | `Tg` | 14 |
| `Decidable/Widths.agda:29,59` | `Tok`, `Tg` | 12 |
| `Grammars/PolynomialTests.agda:22` | `Bool` — **already exists** as `Cubical`'s | 5 |
| `Grammars/RegexTests.agda:24` | `Two` | 4 |

**Fix.** The generic pieces already written in one client belong in
`src/Theory/Type/Decidable/Route.agda` beside `DiscreteEq`:
`dec⊎Eq`, `⊎injL`, `⊎injR`, `decUnitEq`, `decℕEq`
(`Grammars/PolyGrammar.agda:430–462`); plus `decEqRetract` (S1a) and
`decMaybeEq` (currently `decMTok`, `Decidable/Bracket.agda:78`) and
`decWindow` (`Decidable/Window.agda:37`, already generic). Every client's
`≟` then becomes a `Fin`-code plus one line.

---

## S3. Two parallel LL abstractions; the older, weaker one is still load-bearing

There are **two** implementations of "commit to the branch a lookahead class
names":

1. `Decidable/Lookahead.agda:44–106`, `module Predictive` — `Dec`-only
   (mentions `DecTy`, `dec-yes`, `dec-no`), indexed by *cover cells*.
2. `Type/Decidable/Route.agda:286–320` `routeIn` + `Core.agda:491–520`
   `Choice.choose` — answer-generic (the `Dec`-specific half is one field,
   `CommittingAnswer`), indexed by *alternatives*.

`Decidable/Routed.agda:4-16` states, correctly, why (1) is worse:

> `Decidable/Lookahead`'s `Predictive.choose` demands one branch per cell,
> so cells with no production need a `⊥Set↑` pad, and a nullable branch
> cannot pay `lead` at all -- which is why `Decidable/Productions` bolts a
> `nul : X → Bool` field and a trailing `<|>` on top.

Yet (1) is what `Decidable/Productions.agda:162` uses, and `Productions` is
what `Decidable/Lambda.agda:50` and `Decidable/STLC.agda:995` use. So the
deprecated abstraction is still what two of eight client grammars run on,
and it forces `Productions` to be `Dec`-only — `Lambda` and `STLC` cannot be
run at `Maybe` or `ND`, unlike Arith/Dyck/Polynomial/Regex.

Worse, the `nul` escape hatch it was built for is **never exercised**: both
clients set `lamTable .Table.nul _ = false` (`Decidable/Lambda.agda:59`) and
`stlc .Table.nul _ = false` (`Decidable/STLC.agda:1041`). So
`nulCode`/`isSetNul`/`nulSet`/`nulP`/`readNul` and the trailing `<|> nulP x`
(`Productions.agda:87-89,111-113,143-144,207-213,244-246,218`) are all paid
for and unused.

**Recommendation, which should survive.** `Route`/`Choice` survives.
Concretely:

1. Split `Decidable/Productions.agda` in two.
   * `Combinator/Grammars/Spine.agda` (answer-generic, no `Predictive`):
     `Item`, `itemCode`, `bodyCode`, `isSetItem/Body`, `itemSet`, `bodySet`,
     `itemP`, `tailP`, `prodP`. This is the *generic* right-nested-body
     machinery (`Productions.agda:75–105,185–204`) that four other clients
     re-hand-write (S4).
   * `Combinator/Grammars/Table.agda`: the `Table` record with `nul`
     dropped, `at : (x : X) (o : M₁) → Prod X o` turned into a plain
     `r : M₁ → Maybe (Tag x)` route table, and `step` written with
     `Choice.choose` instead of `Pred.choose`.
2. Delete `module Predictive` (`Decidable/Lookahead.agda:44–106`) together
   with `⊥Set↑`, `leadLit`, `leadNone`, `noBranch` (114–131, all dead —
   see S7).
3. `Decidable/Lambda` and the STLC parser then instantiate at any answer,
   like every other client.

### S3a. `Decidable/Routed.agda` is now a two-line re-export

`src/Theory/Instances/Monoid/Combinator/Decidable/Routed.agda:38-39`

```agda
open import Theory.Instances.Monoid.Combinator.Decidable.Base Alphabet _≟_ ℓ public
  hiding (Maybe ; just ; nothing)
```

Its own header (line 17-22) admits it: *"Everything that was once defined
here … now lives in `Core` … What is left is the name and the header."*
Its only importer is `Decidable/Window.agda:20`. **Fix.** Delete the file;
point `Decidable/Window` at `Decidable/Base`; move the header's first two
paragraphs (which are genuinely the best explanation of why routing beats
`Predictive`) to `Type/Decidable/Route.agda`.

---

## S4. Uniformity of the routing abstraction across clients

| client | style | answer-generic? | route |
|---|---|---|---|
| `Grammars/Arith` + `ArithGrammar` | `Choice`+`Route`, `FixAll` | yes | `gExp` on `Push` |
| `Grammars/Polynomial` + `PolyGrammar` | `Choice`+`Route`, `FixAll`, 4 `Choice`s | yes | `gE/gK/gQ/gN` |
| `Grammars/Dyck` | `_<|>_` only (2 branches) | yes | n/a |
| `Grammars/Regex` + `Syntax` | combinators only | yes | n/a |
| `Decidable/Widths` | `Choice`+`Route` via `PushW` | **no** (`Decidable/Window`) | `gS` |
| `Decidable/Arrow` | `Choice`+`Route` via `PushOf`/`PushW` | **no** | `gE/gQ` |
| `Decidable/Lambda` | `Table`→`Predictive` | **no** | `lamTable` |
| `Decidable/STLC` | `Table`→`Predictive` | **no** | `stlc` |
| `Decidable/ListLit`, `Incomplete/ListLit` | `sepBy`/`between` | duplicated per answer | n/a |

So: routing *is* pulling its weight — `Route` is used by five of eight —
but it is not uniform. Two clients (`Widths`, `Arrow`) use `Route` correctly
but are needlessly welded to `Dec` (they import `Decidable/Window` rather
than a hypothetical `Combinator/Window`); two use the deprecated `Predictive`.

**Fix.** Add `Combinator/Window.agda` (answer-free: `decWindow` + `PushW`,
which is all `Decidable/Window.agda:28–56` actually is — nothing in it
mentions `Dec`), then move `Widths` and `Arrow` to
`Grammars/{Widths,Arrow}.agda (𝒯 div com)` + `Decidable/{…}.agda` +
`Grammars/{…}Tests.agda`, matching Arith/Polynomial exactly.

### S4a. `Grammars/Arith` vs `Grammars/ArithGrammar` vs `Decidable/Arith`

The three-file split is right and should survive; the *names* are not. The
same split is spelled two different ways:

* `Grammars/ArithGrammar.agda` (type + route) / `Grammars/Arith.agda` (parser)
  / `Grammars/ArithTests.agda` / `Decidable/Arith.agda`
* `Grammars/PolyGrammar.agda` (type + route) / `Grammars/Polynomial.agda` (parser)
  / `Grammars/PolynomialTests.agda` / `Decidable/Polynomial.agda`

`Arith`/`ArithGrammar` and `Polynomial`/`PolyGrammar` are not the same
convention, and `…Grammar` inside a directory called `Grammars/` is stale
"grammar" vocabulary for what the project now calls a theory type.

**Fix.** One convention: `Grammars/Arith/Ty.agda`, `Grammars/Arith/Parser.agda`,
`Grammars/Arith/Tests.agda`, `Grammars/Arith/Dec.agda`; same for Polynomial,
Dyck, Widths, Arrow, ListLit, Lambda, STLC. Nothing named `…Grammar`.

`Decidable/Arith.agda` and `Decidable/Polynomial.agda` (25–34 lines each,
picking `DecAnswer` and naming three deciders) then become
`Grammars/*/Dec.agda`, and `Decidable/` shrinks to the four answer-instance
modules it should be: `Base`, `Star`, plus (post-S3) nothing else.

---

## S5. Duplication across clients: four hand-written copies of the same code plumbing

Every non-`Productions` client re-writes, by hand:

| what | ArithGrammar | Widths | Arrow | PolyGrammar |
|---|---|---|---|---|
| `Code = Functor ℓM NT (λ _ → tt) tt` | 60–61 | 65–66 | 62–63 | 226–227 |
| `_⊗c_ F G = ⊗e _⊙_ (two F G)` | 63–65 | 68–70 | 65–67 | 229–231 |
| `lit↑ c = LiftTheoryTy ℓG (literal c) , …` | 120–121 | 138–139 | 148–149 | — |
| `bodyIn` / `bodyOut` (`⟦⊗e⟧` shuffling) | 129–143 | 162–170 | 159–177 | 344–382 |
| `rollN` / `unrollN` | 145–149 | 172–176 | 179–183 | 384–401 |
| `isSet…` for the body (`λ where zero → …`) | 92–112 | 110–121 | 80–111 | 264–298 |
| `tokL c = mapP± liftTy lowerTy ∘⊢ tok c` | `Grammars/Arith.agda:37-39` | 221–223 | 230–232 | (`Productions.agda:185`) |
| `GuideOf C = (K : …) → Route (λ y → ty (C y) ⊗ ty K) ℓG` | 161–162 | — | — | 541–542 |
| `isSetTag = Discrete→isSet λ t u → Sum.rec …` | 86–90 | 123–128 | 56–60 | — |

`Arrow.agda:161-177` is the worst instance — six lines of nested
`⟦⊗e⟧⁻ _ _ ∘⊢ ((liftTy ∘⊢ lowerTy) ,⊗ …)` per production, written twice
(in and out) for five productions.

**Fixes, concretely.**

1. **`bodyIn`/`bodyOut` are derivable.** `Decidable/Productions.agda:79-81`
   already has `bodyCode : List (Item X) → Functor …` and `:192-196` already
   has the generic `tailP` that traverses it. Hoist `Item`/`bodyCode`/
   `bodySet`/`bodyIn`/`bodyOut`/`itemP`/`tailP` into the new
   `Combinator/Grammars/Spine.agda` (S3, item 1); then `ArithGrammar`,
   `Widths`, `Arrow` and `PolyGrammar` write their bodies as
   `List (Item NT)` and get `Cb`, `bodyIn`, `bodyOut`, `isSetBody`, `rollN`,
   `unrollN` and the branch parser for free. This alone removes on the order
   of 250 lines across four files.
2. **`GuideOf` already exists.** `Core.agda:502-503`:
   ```agda
   Guide : Type _
   Guide = (K : TheorySet ℓC tt) → Route (λ y → ty (C y) ⊗ ty K) ℓC
   ```
   It mentions no answer, but it is trapped inside
   `RoutedCombinators 𝒯 div com` → `module Choice`. Hoist it to `Core`'s top
   level as `GuideOf (C : Y → TheorySet ℓC tt)` and delete
   `ArithGrammar.agda:161-162` and `PolyGrammar.agda:541-542`.
3. **`lead` already exists three times.** `PolyGrammar.agda:545-547`
   (`lead c = (id⊢ ,⊗ ⊤Ty-intro) ∘⊢ ⊗-assoc`) is verbatim
   `Decidable/Lookahead.agda:119-121` (`leadTok`), and
   `ArithGrammar.agda:167-171` open-codes it with extra `⊗-assoc`s. Put one
   copy next to `Push` in `Core.agda`.
4. **`DiscreteEq→isSet` already exists** at `Core.agda:106-108` and is
   inlined five more times: `Productions.agda:43` (`isSetM₁`),
   `Lookahead.agda:53` (`isSetY`), `Arrow.agda:57`, `Widths.agda:124`,
   `ArithGrammar.agda:87`. Replace all five with the `Core` definition.
5. **`decM₁` is a verbatim re-implementation of `_≟M_`.**
   `Core.agda:110-119` reimplements `Types.agda:114-119`, which `Core`
   already imports at line 49 (`open import …Monoid.Types … public`).
   Delete `decM₁`, use `_≟M_`.
6. **`Λ-cover` is a verbatim duplicate of `lookaheadCover`.**
   `Decidable/Lookahead.agda:110-112` = `Lookahead/Base.agda:76-78`, and
   `Core.agda:123` already uses the latter. Delete the former.
7. **`Decidable/ListLit.agda` and `Incomplete/ListLit.agda` are the same
   file.** 78 and 83 lines, identical `Tok`, `_≟T_`, `items`, `listP`,
   `accepts`, `rejects`; only `Decidable/Star` vs `Incomplete/Star` and
   `semact-dec` vs `semact-Maybe` differ — the exact pair
   `Grammars/Dyck.agda:4-8` already says was collapsed for Dyck. Collapse to
   `Grammars/ListLit.agda (𝒯 : AnswerFunctor)` + `Grammars/ListLitTests.agda`.
   (Incomplete's version additionally spells out the inferred `Parser` type
   at lines 48,52-54,57-60 where Decidable's writes `_`; keep the `_`.)

### S5a. Dyck tests exist three times

`Decidable/Dyck.agda:45-65`, `Incomplete/Dyck.agda:32-52` (byte-identical
tables), and `Grammars/DyckTests.agda:56-85` (the same cases at all three
answers). **Fix.** Keep `Grammars/DyckTests.agda`; reduce `Decidable/Dyck`
and `Incomplete/Dyck` to the two-line answer pick, or delete them (they add
nothing over `DyckTests`' `GDec.dyck`/`GInc.dyck`). `Decidable/Dyck.agda:36-40`
(`dyck-cover`, `nil-not-refuted`) is the only unique content — move it to
`DyckTests`.

---

## S6. Tests: 86 instances of the forbidden shape

The maintainer's target shape (unicode-lexer input, `Suite`'s
`passes`/`_at_`/`_↦_`, expected output from a *display* semantic action)
already exists and is exemplified by `Grammars/RegexTests.agda:75-128` and
`Instances/Monoid/Pipeline/Dyck.agda:104-140`. Against that, the scope has
86 lines of the forbidden shape:

| file | count | example |
|---|---|---|
| `Decidable/STLC.agda` | 29 | `:2001 badApp-refuted = theNotD (typed? [] (App (Lam vx Na (Nm vx)) Tru)) Eq.refl` |
| `Decidable/Arith.agda` | 19 | `:41 yes-add3 = theYes (parse (nm ∷ pl ∷ nm ∷ pl ∷ nm ∷ []) tt) Eq.refl` |
| `Decidable/WidthsTests.agda` | 14 | `:71 k2-nest = theYes (K2.parse (ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ ta ∷ tc ∷ tb ∷ []) tt) Eq.refl` |
| `Decidable/Arrow.agda` | 14 | `:298 theYes (parse (lp ∷ lp ∷ vid ∷ cm ∷ vid ∷ rp ∷ ar ∷ vid ∷ rp ∷ dot ∷ vid ∷ []) tt) Eq.refl` |
| `Decidable/Lambda.agda` | 8 | `:82 yes-omega = theYes (parse (lp ∷ lam ∷ v ∷ dot ∷ …16 tokens…) tt) Eq.refl` |
| `Decidable/Dyck.agda` | 2 | `:31 no-lp = theNo (decDyck (lp ∷ []) tt) Eq.refl` |

Every one of these duplicates its input token list *twice* (once in the type,
once in the term), is unreadable, and says only yes/no.

**Target skeleton** (all three ingredients exist):

```agda
-- Grammars/Arith/Tests.agda
open import Theory.Instances.Monoid.Unicode.Base using (UChar ; _≟U_ ; text)
open import Theory.Instances.Monoid.Phase UChar isSetAlphabet   -- Display
open import Theory.Instances.Monoid.Lex.Regex UChar _≟U_ (ℓ-suc ℓ-zero)

lexicon : Lexicon                       -- (a) unicode input
lexicon = reOf "\\(" ∷ reOf "\\)" ∷ reOf "\\+" ∷ reOf "[a-z]+" ∷ reOf "[ \t\n]" ∷ []

showExp : SemanticAction (Lang Exp) AS.String     -- (c) display action
showExp = …                                       -- or a `Display (Lang Exp)` instance

parse : AS.String → Mb.Maybe AS.String
parse s = pipeline lexPhase (Dec.observe decide (Dec.semact-dec showExp)) s

accepts : passes (parse at                        -- (b) uniform Suite helpers
  ( "n"            ↦ Mb.just "n"
  ∷ "n + n"        ↦ Mb.just "(n + n)"
  ∷ "(n + n) + n"  ↦ Mb.just "((n + n) + n)"
  ∷ [] ))
accepts = refl

refuses : rejects parse ("" ∷ "n +" ∷ "( n" ∷ "n n" ∷ "( )" ∷ [])
refuses = refl
```

`Suite` is `src/Theory/Type/SemanticAction/Base.agda:34-56`, whose `rejects`
(`:52-54`, newly added) is exactly the negative half — every `M.nothing`
column in the tables at `Grammars/ArithTests.agda:75-81`,
`PolynomialTests.agda:90-96`, `Decidable/ListLit.agda:70-78`,
`Incomplete/ListLit.agda:75-83`, `Decidable/Dyck.agda:58-65` and
`Incomplete/Dyck.agda:45-52` should be rewritten with it, which removes the
repeated `↦ M.nothing` and lets the positive suite carry only real expected
output. `Display` is
`Instances/Monoid/Phase.agda:102-108`; `text`/`untext` are
`Instances/Monoid/Unicode/Base.agda`; the whole composition is already
demonstrated by `Instances/Monoid/Pipeline/Dyck.agda`.

### S6a. Tests sitting at the bottom of a definitions file

Move to a sibling `Tests.agda` (none of these files have one):

* `Decidable/Arith.agda:31-102` — 72 lines of tests in a 103-line module
  whose only real content is `decide = G.answer` (line 26).
* `Decidable/Lambda.agda:69-98` — tests inside the grammar definition.
* `Decidable/Arrow.agda:260-328` — 69 lines of tests after the parser.
* `Decidable/Widths.agda` has a `WidthsTests.agda` sibling — good — but
  `Decidable/Dyck.agda:28-65`, `Incomplete/Dyck.agda:25-52`,
  `Decidable/ListLit.agda:58-78`, `Incomplete/ListLit.agda:63-83`,
  `Decidable/Polynomial.agda` (none) do not.
* `Decidable/STLC.agda:1122-1222` and `:1955-2008`.

### S6b. Locally duplicated test helpers

* `Grammars/PolynomialTests.agda:22-26`: `_≟B_` on `Bool` written by hand;
  `Cubical.Data.Bool` has `discreteBool`, and after S2 this is
  `decEqRetract`-derived in one line.
* `Grammars/ArithTests.agda:54-55` / `PolynomialTests.agda:61-62`: the same
  `sem = Dec.semact-pure tt` placeholder — meaning **neither Arith nor
  Polynomial has a display action at all**; both suites only check
  accept/reject, and the header at `ArithTests.agda:11-13` admits it
  ("what is being compared … is *whether* a string parses … not the tree").
  Only Dyck (`semactS`) and Regex (`regAct`) have real display actions.
  Adding `SemanticAction (Lang Exp) ExpTree` for Arith and Polynomial is the
  main missing test coverage in the subsystem.
* `Decidable/Arith.agda:81-87`: `chain`/`nest` scale generators; `Widths`
  has its own (`aFill`/`aThenC`, lines 43-49) and `STLC` its own
  (`Src` combinators, 1058-1120). Fine to keep local, but the `chain`/`nest`
  ones would be more useful as `Suite` helpers.

---

## S7. Dead code

### `src/Theory/Type/Decidable/Base.agda` — roughly half the file

Line 1 already asks: `-- TODO how much of this is actually used?` Answer:
these have no reference anywhere in `src/`:

* `:66 fromDec`
* `:113 dec-retract`, `:117 dec-retract-id`, `:126 dec-retract-∘`
* `:144 dec⊕`, `:148 dec&`, `:156 decLiftTheoryTy`
* `:162 record DecidableFormers` (and its three fields `dec⊕ᴰ`/`dec&ᴰ`/`dec⊗ᵘ`)
* `:176 record PointwiseDecidableFormers` (and its three fields)
* `:205 coverDecidable`, `:211 dec-cover`

Live: `¬Ty`, `DecTy`, `Decidable`, `DecAt`, `at`, `dec-yes`, `dec-no`,
`¬Ty-map`, `isNo`/`theNo`/`isYes`/`theYes`/`yesFrom`, `isProp¬Ty`, `¬⊕ᴰ`,
`¬-⊕`, `dec-⊕&`, `dec-map`, `dec⊥Ty`, `dec⊤Ty`, `DecCover`, `decisionCover`.
Delete the rest and the TODO with it.

### `src/Theory/Type/Decidable/Route.agda`

* `:102 routeDec` — unreferenced. (`routeIn` is what `DecCommitting` uses.)

### `src/Theory/Instances/Monoid/Residual.agda` — roughly 40% of the file

Unreferenced anywhere: `:99 ⟜Iso`, `:118 ⟜-uncurry`, `:130 ⟜-unitr`,
`:158 ⊸-lamIso`, `:167 ⊸-precomp`, `:171 ⊸-post`, `:183 ⊸-uncurry`,
`:193 ⊸-unitl`, `:198 ⊸⟜-swap`, `:208 ⊸⊕ᴰ`, `:252 ⊗-unit-l⁻-nat`,
`:285 ⊗-tri-l`, `:297 ⊗-tri-l⁻`, `:307 ⊗-tri-r`, `:317 ⊗-tri-r⁻` (and the
four `private` `triL`/`triL⁻`/`triR`/`triR⁻` at 260–282 that exist only for
them), `:329 ⌈⌉-cat`, `:336 ⌈⌉-split`, `:343 ε⌈⌉-unit-l`,
`:376 Konst`, `:379 Konst-map`, `:382 Konst-pt`.

That is ~150 of 383 lines, and it is the file with the most external
model-element binding in the subsystem, so deleting it also shrinks the
"escapes" surface substantially. Keep only what has clients: `castEq`,
`castEqPathP`, `two-η`, `⊗-split-η`, `_⟜_`, `⟜-intro`, `⟜-intro⁻`, `⟜-β/η`,
`⟜-app`, `⟜-precomp`, `⟜-post`, `_⊸_`, `⊸-lam`, `⊸-lam⁻`, `⊸-lam-β/η`,
`⊸-app`, `⊸-curry`, `⊗ᵘ→⊗`, `⊗→⊗ᵘ`, `⟦⊗e⟧`, `⟦⊗e⟧⁻`, `⊗ε-unit-*`,
`⊗⊕ᴰ-dist*`, `&⊕-distR`, `&⊕ᴰ-dist*`.

### Elsewhere

* `Combinator/Core.agda:364 anyTok` — unreferenced. It is the *only*
  consumer of the `AnswerFunctor.Ans-any` field (`:221`), which in turn
  forces three implementations: `Decidable/Base.agda:68 dec-char⊗-at`,
  `Incomplete/Base.agda:68 maybe-char⊗-at`, `NonDet/Base.agda:115
  nd-char⊗-at`. Either give `anyTok` a client or delete the whole chain
  (≈40 lines across four files, plus the `Precise.dec-char⊗↑` import).
* `Combinator/Decidable/Lookahead.agda:115 leadLit`, `:124 ⊥Set↑`,
  `:127 leadNone`, `:130 noBranch` — dead cluster; goes with S3's deletion
  of `Predictive`.
* `Instances/Monoid/Lookahead/Base.agda:67 Λ-ext` — unreferenced.
* `Instances/Monoid/Lookahead/Window.agda:38-41 w1 w2 w3` — unreferenced
  (`WidthsTests` writes `more none` etc. out); `:103 Λw-head` —
  unreferenced, and the header at line 61 advertises it as part of the
  module's interface.
* `Decidable/Productions.agda`: the entire nullability path
  (`:87 nulCode`, `:111 isSetNul`, `:143 nulSet`, `:207 nulP`,
  `:244 readNul`, `:61 Table.nul`, and the `<|> nulP x` at `:218`) — reached
  by no client (both set `nul _ = false`). Drops out with S3.

No `postulate`, `TERMINATING`, `trustMe`, `--safe` violation, or
commented-out code block anywhere in scope. That part is clean.

---

## S8. Internality escapes, classified

**Justified** (axiomatising a connective / external decidability / hLevel):

* `Residual.agda` in its entirety — its header (lines 5-8) states the rule
  correctly: *"Every definition here introduces a connective by matching on
  its own elements"*. But see S8a.
* `Residual/Laws.agda:34,43` — `funExt λ where (ms , Eq.refl , …) → refl`,
  the β-laws for the connective just introduced.
* `Lookahead/Base.agda:98-124`, `Lookahead/Window.agda:62-93` — `Λ-disjoint`,
  `Λ-total`, `win`, `Λw-sound`. Correctly `private` where possible; the
  comment at `Window.agda:58-61` gets the justification exactly right.
* `Type/Decidable/Base.agda:66-88` — `isYes`/`theYes`/`theNo`/`yesFrom`
  match `Sum.inl`/`Sum.inr` on `DecTy A m`: reading a decision at a point is
  the display boundary.
* Every `_≟_ : (x y : Alphabet) → (x Eq.≡ y) Sum.⊎ …` — external
  decidability of the alphabet, a module parameter by design.
* `Core.agda:93-101 PushOf.covers .disjoint`, `Route.agda:296 distR` — one
  line each, building a `Cover`.
* `SemanticAction/Base.agda:130 Δ-⊗` and `NonDet/Base.agda:91 consA` —
  the externalisation boundary. `consA` should nonetheless go through
  `Δ-⊗`/`semact-⊗` rather than `(a m (h .lower) .fst ∷ t .lower .fst) , tt`.

**Unjustified:**

* `Decidable/STLC.agda:1271-1424` — S1b. An entire compiler front end as
  metalanguage functions on external data.
* `Decidable/Productions.agda:228-256` — S1c. `Kst _ _ = Tree` and `kids`.
* `Decidable/Bracket.agda:284-389` — S8b below.

### S8a. `Residual.agda`'s header claim is false as written

`src/Theory/Instances/Monoid/Residual.agda:8`

> Nothing downstream of this file binds a model element.

`Decidable/Bracket.agda:284-389` binds model elements in seven definitions,
and `Decidable/STLC.agda:1271+` in a dozen more. Either weaken the claim to
"nothing downstream *of the connective tier*", or (better) make it true by
fixing S8b and S1b. The maintainer cares about this claim being load-bearing;
a header that asserts an invariant the codebase violates is worse than no
header.

### S8b. `Decidable/Bracket.agda`: 106 lines of hand-split tensors

```agda
284  tr-skip : (c : Tok) → NotBr c → literal c ⊗ TranspG ⊢ TranspG
285  tr-skip c nb m (ms , e , (lc , (t , tt*))) =
286    go (ms fz) (ms (fs fz)) lc e t
287    where
288    go : (u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m
289       → Transparent v → Transparent m
290    go .(c ∷ []) v Eq.refl Eq.refl tv = skipTr c nb tv
```

and the same pattern four levels deep in `tr-wrap` (320-336), `bt-open`
(340-357) and `bt-wrap` (359-382) — `go`/`go2`/`go3`/`go4`.

The file's own header (226-234) argues that the *cover* must be justified
externally, and that is right. But `tr-skip`/`cl-skip`/`tr-open`/`tr-wrap`/
`bt-open`/`bt-wrap`/`bt-vid` are not the cover; they are seven repetitions of
one missing lemma: "eliminate a `literal c ⊗ A` by consuming the letter".

**Fix.** Add one eliminator beside `⊗ᵘ-elim` / in `Strings.agda`:

```agda
lit⊗-elim : {A : TheoryTy ℓ tt} {C : TheoryTy ℓ' tt} (c : Alphabet)
  → (∀ v → A v → C (c ∷ v)) → literal c ⊗ A ⊢ C
```

Then all seven become one-liners and 106 lines collapse to about 25, with
zero `go`s.

---

## S9. Naming

**92** `where`-bound helpers in the subsystem are called `go`, `go2`, `go3`,
`go4` or `br`:

| file | count |
|---|---|
| `Decidable/STLC.agda` | 27 |
| `Residual.agda` | 11 |
| `Decidable/Bracket.agda` | 18 (`go`×10, `go2`×4, `go3`×3, `go4`×1) |
| `Grammars/PolyGrammar.agda` | 9 |
| `NonDet/Base.agda`, `Incomplete/Base.agda` | 4 each |
| `Type/Decidable/Base.agda` | 3 |
| others | ~16 |

Proposed replacements (representative):

| current | file:line | proposed |
|---|---|---|
| `go` (in `decM₁`) | `Core.agda:114` | delete — use `_≟M_` (S5.5) |
| `go` (in `PushOf.covers .disjoint`) | `Core.agda:96` | `onSameCell` |
| `go` (in `dec-retract-id`/`-∘`) | `Decidable/Base.agda:121,132` | delete with the defs (S7) |
| `go` (in `dec-cover.step`) | `Decidable/Base.agda:219` | delete with the def |
| `same` (in `routeIn.kill`) | `Route.agda:315` | fine — keep |
| `br` | 14 sites | `atTag` / `atClass` / `perProduction` |
| `go`/`go2`/`go3`/`go4` | `Bracket.agda:288,315,334,380` | gone with S8b |
| `go` (in `⟜-uncurry`, `⊸-uncurry`, `⊸⟜-swap`) | `Residual.agda:123,188,203` | gone with S7 |
| `go` (in `⊗ε-unit-r`) | `Residual.agda:247` | `onSplit` |
| `go` (in `⌈⌉-cat`/`⌈⌉-split`) | `Residual.agda:332,339` | gone with S7 |
| `go` (in `nulP`) | `Productions.agda:210` | gone with S3 |
| `go` (in `Λw-total`) | `Window.agda:92` | `extendWindow` |
| `go` (in `Λw-sound`) | `Window.agda:77` | `onFirstLetter` |
| `go` (in `toTm`'s helpers) | `STLC.agda`, ×27 | gone with S1b/S1d |
| `f`, `h` in `≅≡`, `⋆≅` | `Core.agda:154-173` | fine (they *are* morphisms) |
| `tail′`, `mid`, `nodeP`, `inner` | `Grammars/Dyck.agda:45,49,53`, `Grammars/Arith.agda:45` | good names — keep, and adopt elsewhere |

**Stale "grammar" vocabulary.** No *identifier* is affected (they all use
`Ty`/`TheoryTy`/`TheorySet` correctly), but the module names
`Grammars/ArithGrammar.agda` and `Grammars/PolyGrammar.agda` are (S4a), and
prose uses "grammar" for "theory type" at `Core.agda:104,144,145,238,269`,
`Syntax.agda:2,10`, `Productions.agda:2,123`, `Bracket.agda:229,249,260`,
`Decidable/Base.agda:10`, `Incomplete/Base.agda:7`. Low priority, but if the
vocabulary has moved, these are the 15 places to sweep.

---

## S10. Comments

The comment quality here is unusually high — most headers say *why* a design
is what it is and would be expensive to reconstruct. Specific problems:

**Stale / wrong:**

* `Grammars/PolyGrammar.agda:17-18` — *"tag decidability is the parser's
  business, in `Dyck`."* Tag decidability is in this very file
  (`decETag`/`decKH`/`decQH`, 461–486), and `Dyck` has nothing to do with it.
* `Residual.agda:8` — S8a, the claim is false.
* `Decidable/Routed.agda:17-22` — describes a module that no longer exists;
  the file is now a re-export (S3a).
* `Lookahead/Window.agda:61` — advertises `Λw-head` as part of the exported
  interface; `Λw-head` has no clients (S7).
* `Type/Decidable/Base.agda:1` — the `TODO` should be resolved, not carried
  (S7 answers it).

**Too long at file top** (>18 lines of prose before the first `open import`):
`Core.agda:4-25` (22 lines), `Productions.agda:2-13`, `Routed.agda:2-22`
(21 lines for a 2-line module), `Grammars/Polynomial.agda:2-23` (22 lines).
`Core.agda`'s is earned — it explains the three-record factoring, which is
the module's whole point. `Routed.agda`'s is not: 21 lines of prose above
2 lines of code.

**Genuinely non-obvious, no comment:**

* `Core.agda:99-100` — `same : {u u' : Maybe Y} → r b Eq.≡ u → r b Eq.≡ u' → u Eq.≡ u'`
  inside `PushOf.covers .disjoint`. Why matching *both* equations is what
  makes the cell equality reduce is the subtle part of `PushOf`; unexplained.
* `Decidable/Widths.agda:210,214` — `Eq.transport (λ v → … ⊢ PW.PB v) (rt-nest kk) …`.
  This is the only `Eq.transport` in a `Route.into` in the codebase, and why
  the route table's *proof* (`rt-nest`/`rt-flat`) has to be transported
  rather than computed is not said.
* `Grammars/PolyGrammar.agda:606,621,625` — `⊗⊕ᴰ-distR` in `rollK`/`rollQ`
  redistributes an inner `⊕[ n ∈ ℕ ]` across the leading letter. The prose
  at 577-580 gestures at it but does not say why `distR` (not `distL`).
* `Core.agda:49-52` — the `Residual` import list is
  `⊗ε-unit-l⁻ ; ⊗ε-unit-r ; ⊗ε-unit-r⁻ ; ⊗⊕ᴰ-distL ; &⊕ᴰ-distR` but
  `⊗⊕ᴰ-distL`/`&⊕ᴰ-distR` are not used in `Core` — they are re-exported
  implicitly through `public` opens elsewhere. Over-broad; narrow it.

**AI-slop / restating the code:** essentially none found. The one borderline
case is `Decidable/Star.agda`, `Incomplete/Star.agda`, `NonDet/Star.agda`,
whose 4-line headers are the same sentence three times over three
two-line modules — but that is duplication, not slop.

---

## S11. Over-broad exports

* `Decidable/Base.agda:35` `open import …Combinator.Core Alphabet _≟_ public`
  re-exports all of `Types`, `Suffix.Base`, `Route`, `Unitor` (transitively,
  since `Core:49-57` opens those `public`). Every downstream client therefore
  sees `Maybe`/`just`/`nothing` shadowing, which is why five files carry
  `hiding (Maybe ; just ; nothing)` (`Routed.agda:39`, `ArithGrammar.agda:44`,
  `PolyGrammar.agda:165`, `Bracket.agda:222`, `Core.agda:47` comment).
  Narrow `Core`'s re-exports.
* `Grammars/Arith.agda:27-30` opens four modules `public`, so
  `Decidable/Arith.agda` inherits the whole combinator library it does not
  use. Same at `Grammars/Polynomial.agda:43-46` and
  `Grammars/Dyck.agda:22-23` (`open C public` — the entire `Core`).
* `Decidable/Productions.agda:37-38` re-exports `Decidable/Lookahead` `public`,
  which re-exports `Decidable/Base` `public`: `Decidable/Lambda.agda` gets
  ~500 names from one import.
* `Combinator/Syntax.agda:34` `open import …KleeneStar … public` — the
  comment at 35 shows the author already thought about this for `Regex`
  (deliberately *not* public); apply the same judgement to `KleeneStar`.

---

## Summary of recommended work, in order

1. Split `Decidable/STLC.agda` (S1); derive its `_≟T_` (S1a/S2); replace its
   `Tree`-based front end with semantic actions (S1b/S1c).
2. Retire `Predictive`; port `Productions` to `Route`/`Choice`; delete
   `Decidable/Routed.agda` (S3).
3. Extract `Combinator/Grammars/Spine.agda` (generic `Item`/`bodyCode`/
   `bodyIn`/`bodyOut`/`tailP`) and hoist `GuideOf`, `lead`,
   `DiscreteEq→isSet` (S5.1–5.4); delete `decM₁` and `Λ-cover` (S5.5–5.6).
4. Collapse `{Decidable,Incomplete}/ListLit` and the three Dyck test copies
   (S5.7, S5a); move `Widths`/`Arrow` to the answer-generic three-file
   layout (S4); adopt one naming convention (S4a).
5. Rewrite the 86 forbidden tests as `Suite` suites over unicode input with
   display actions; add display actions for Arith and Polynomial (S6).
6. Delete the dead code (S7) — ~150 lines in `Residual.agda`, ~120 in
   `Type/Decidable/Base.agda`, the `anyTok`/`Ans-any` chain, and the
   `Predictive`/`nul` remnants.
7. Add `lit⊗-elim` and rewrite `Decidable/Bracket.agda:284-389` (S8b); fix
   `Residual.agda:8` (S8a).
8. Rename the 92 `go`/`br` helpers that survive (S9); fix the five stale
   comments and add the four missing ones (S10); narrow the re-exports (S11).
