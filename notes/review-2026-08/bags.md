# Audit: `src/Theory/Instances/Bags/**`

Read-only review. **I did not run `agda`.** Every type-level claim below was traced by
hand against the definitions in `Theory/Base.agda`, `Theory/Instances/Monoid/Extension.agda`,
`Theory/Type/{Product/Binary,Function,Sum,Operation,Guarded,Inductive,Residual,Subgrammar}/…`.
Where a claim depends on definitional reduction I say so explicitly.

---

## 0. Verdicts on the maintainer's six complaints

| # | Complaint | Verdict |
|---|---|---|
| 1 | "I don't like the View stuff, its external and maybe unnecessary for quicksort" | **Confirmed, and stronger than stated.** `View` is external *and* `Generation.agda` is imported by nothing at all. Delete or finish it. |
| 2 | "Bag.Order also is a bit external" | **Partly refuted.** `bagAll` as the unique monoid hom `M → Ω` is the *correct* DSL move — the DSL already has `Ω` and `Subgrammar`. The genuinely external parts are the five raw-λ lemmas at `Order.agda:87–107` and ~50 lines of dead code. |
| 3 | "Bag.Partition could be better I think too" | **Confirmed.** `sideOf`/`go`/`side` is a `Bool`-indexed external `View` in miniature; `_⊕_` + an internal decision replaces all of it. |
| 4 | "Quicksort looks good … provided we are using ▷ and ▷-split correctly" | **Confirmed: `▷`/`▷-cons`/`▷-split` are used correctly.** Payments verified arithmetically. **But** the claim "no `TERMINATING`" is false: `quicksort` evaluates through `Inductive/Base.rec`, which carries the pragma. |
| 5 | "Look through Rank, Sequence, and Sorted too" | Done. Rank is correct but has dead code and a misplaced export; Sequence/Sorted are ~80% verbatim duplicates. |
| 6 | "be very deliberate … clear justification for stepping outside the DSL" | 11 escape sites catalogued below: 4 justified, 4 avoidable, 3 justified-but-mislocated. |

---

## 1. Findings, ranked by severity

### F1 (HIGH) — `quicksort` runs through a `{-# TERMINATING #-}` recursor, contrary to what the file headers claim

`src/Theory/Type/Inductive/Base.agda:41`
```agda
      {-# TERMINATING #-}
      rec : ∀ x → μ F x ⊢ A x
```

Two nodes of the quicksort pipeline are `rec`:

- `src/Theory/Instances/Bags/Sequence.agda:69` — `recSeq n c = rec (λ _ → SeqCode) (λ _ → seqLayer n c) tt`
- `src/Theory/Instances/Bags/Sorted/Base.agda:71` — `recSorted n c = rec (λ _ → SortedCode) (λ _ → sortedLayer n c) tt`

and both are on the evaluation path:

- `src/Theory/Instances/Bags/Partition.agda:47` — `partSeq x = recSeq nilCase consCase`, called from `Quicksort/Base.agda:53`.
- `src/Theory/Instances/Bags/Sorted/Base.agda:76` — `elements = recSorted …`, called from `Quicksort/Tests.agda:74`.

Additionally `isSetSorted` (`Sorted/HLevels.agda:46`) goes through `isSetμ`, which is
`{-# TERMINATING #-}` at `Theory/Type/Inductive/HLevels.agda:154,169`. That one is an
hLevel obligation, so it is a *proof* and does not affect evaluation — but it means no
part of the pipeline is pragma-free.

**Why this matters.** Three separate headers frame the design around avoiding the pragma:
`Quicksort/Tests.agda:31–36` ("Do not recurse through `μ`'s recursor at a function-typed
motive… so it recurses by `löb`"), `Join.agda:5–8`, and `Guarded/Base.agda:81–84`
("`Inductive/Base`'s `rec` needs `TERMINATING`; here the descent is `löb`, which is a
term, so nothing is asserted"). A reader takes away that the bag algorithms are
löb-justified end to end. Only the *outer* recursions are; the two folds over `Seq` and
`Sorted` are asserted.

**Verdict: avoidable.** The repo already contains the replacement, for exactly this
signature: `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:105–125`,
```agda
    -- ...and Löb closes it.  One combinator, no pragma.
    fold*g : A * ⊢ ty B
    fold*g = ⇒-app ∘⊢ ((GB.löb (λ _ → ⇒-intro body) tt ∘⊢ ⊤Ty-intro) ,& id⊢)
```
That module's header (lines 2–11) even explains why `hylosFromGuard` cannot rescue the
`⊗e` clause (it quantifies over the empty splitting and so demands `m < m`), and that
`PayR` is the right shape because it receives the head's inhabitant before owing the
order fact.

**Fix.** `Rank.Guarded▷` already exports the exact payment (`▷-cons`, `Rank.agda:119`).
Write `recSeq` as a löb, structurally identical to `Join.stepJ`/`Quicksort.step`:
```agda
module _ {C : TheoryTy ℓA tt} (isSetC : ∀ m → isSet (C m))
  (n : ⌈ εᵖ ⌉ ⊢ C) (c : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B C ⊢ C) where
  private
    RS : Fam _ ;  RS _ = Seq ⇒ C
    open Guarded▷ RS (λ _ m → isSetΠ λ _ → isSetC m)

    body : Seq ⊢ ▷ tt ⇒ C
    body = caseSeq (⇒-intro (n ∘⊢ π₁))
             λ y → ⇒-intro (c y ∘⊢ ⊎Bmap id⊢ (⇒-app ∘⊢ &-swap) ∘⊢ ▷-cons y)
  recSeqG : Seq ⊢ C
  recSeqG = ⇒-app ∘⊢ ((löb (λ _ → ⇒-intro (⇒-app ∘⊢ &-swap ∘⊢ (id⊢ ,&p body))) tt
                        ∘⊢ ⊤Ty-intro) ,& id⊢)
```
`partSeq`'s motive `Halves x` is not function-typed, so this is a mechanical swap. Same
for `elements` at `Sorted/Base.agda:76`. The price is an `isSet C` argument — which
`Partition` can supply (`Halves x` is built from `Seq` and two props) and `elements` can
supply from `isOfHLevelList`.

If the pragma is to be kept for now, **at minimum** correct the headers: say that the
divide-and-conquer recursion is löb-justified but the layer folds are still `rec`.

---

### F2 (HIGH) — `Generation.agda` is dead code; `View` is external and unused

`src/Theory/Instances/Bags/Generation.agda:25–26`
```agda
View : Bag → Type ℓM
View m = (m ≡ εᵖ) ⊎ (Σ[ y ∈ El ] Σ[ rest ∈ Bag ] (⌈gen y ⌉ ⊙ᵖ rest ≡ m))
```

`grep -rn "Bags.Generation" src/` returns only the module's own declaration line. Nothing
imports it. Quicksort consumes `Seq` (a `μ`-code, `Sequence.agda:39`) and eliminates it
with `caseSeq`/`recSeq`; it never touches `View`.

**Verdict on the escape: external, and avoidable in the sense that it is not needed.**
`View` is exactly the pattern the brief describes — a metalanguage `⊎`/`Σ` over model
elements (`m : Bag`, `rest : Bag`, paths in the HIT carrier). The internal statement of
the same fact is `Seq` itself: `⌈ εᵖ ⌉ ⊕ (⊕[ y ∈ El ] (⌈ ⌈gen y ⌉ ⌉ ⊎B ⊤Ty))`, or one
unroll of `SeqCode`. `joinView` (`Generation.agda:36–45`) is a hand-written monoid
structure on the total space, `fold-fst` (`74–87`) is a hand-written `recUniq`, and
`TSat`/`Tops` (`47–68`) are a hand-written model — 90 lines of external construction with
no consumer.

**Honest counterpoint, worth recording rather than deleting silently.** There is a real
gap that `Generation` is the raw material for and that nothing else fills: **there is no
map `(m : Bag) → ∥ Seq m ∥₁`.** `Seq m` is inhabited only by `[]ᵍ` and `_∷ᵍ_`
(`Sequence.agda:77–83`), so `quicksort : Seq ⊢ Sorted` sorts *arrangements you already
have*, not bags. Nothing in the tree states or proves that every bag has an arrangement.

**Fix (choose one):**
- (a) Delete `Generation.agda`. State in `Sequence.agda`'s header that `Seq` is the input
  interface and that surjectivity onto `Bag` is not claimed.
- (b) Finish it: replace `View` with `∥ Seq m ∥₁` as the fold's second component
  (`T s = Σ[ m ∈ Bag ] ∥ Seq m ∥₁`), `joinView` with `∥∥₁`-lifted `⊎B`-append on `Seq`,
  and export `arrange : (m : Bag) → ∥ Seq m ∥₁`. Then `View` disappears entirely and the
  file earns its place. The truncation argument in the header (lines 1–4) is correct and
  survives verbatim.

---

### F3 (HIGH) — `Partition.sideOf` is an external decision; `side` is a `Bool`-indexed `View`

`src/Theory/Instances/Bags/Partition.agda:33–44`
```agda
side : El → Bool → El → hProp ℓ-zero
side x true = belowEl x
side x false = aboveEl x

sideOf : (x y : El)
  → ⌈ ⌈gen y ⌉ ⌉ ⊢ ⊕[ b ∈ Bool ] (⌈ ⌈gen y ⌉ ⌉ & bagAll (side x b))
sideOf x y = go (le y x) Eq.refl
  where
  go : (b : Bool) → le y x Eq.≡ b → …
  go true w = σ⊕ true ∘⊢ (id⊢ ,& bagAll-gen (belowEl x) y w)
  go false w = σ⊕ false ∘⊢ (id⊢ ,& bagAll-gen (aboveEl x) y (leTotal y x w))
```

Three problems stacked:

1. `go (le y x) Eq.refl` is the classic external `with`-abstraction on a metalanguage
   `Bool`-valued function, dressed as an auxiliary. The `Eq.refl` is a raw metalanguage
   identity on `le`, not a DSL term.
2. `side : El → Bool → El → hProp` is a `Bool`-indexed family of *semantic* predicates —
   structurally the same "external inductive family indexed by model-adjacent data" the
   maintainer objects to in `View`. It exists only to make the two branches share a type.
3. `⊕[ b ∈ Bool ]` where `_⊕_` is right there (`Theory/Type/Sum/Binary/Base.agda:34`).
   Using the dependent sum over `Bool` forces `⊎B⊕ᴰ-dist` + `⊕ᴰ-elim` (line 56) where
   `⊕-elim&` (`Sum/Binary/Base.agda:50`) would do.

**Verdict: the decision itself is justified** (an unavoidable external decision procedure:
`le` is a module parameter and `leTotal` is its totality). **The packaging is avoidable.**
The DSL's own idiom for this is `Theory/Type/Decidable/Base.agda:38–41` (`DecTy A = A ⊕ ¬Ty A`,
`Decidable A = ⊤Ty ⊢ DecTy A`) and, precisely parallel, `KleeneStar/Guarded.agda:57–63`,
where an external fact (`literal-¬Nullable`) is discharged **once**, behind an internal
interface (`¬Nullable A = A & εTy ⊢ ⊥Ty`), and no downstream file sees the metalanguage
again.

**Fix.** Discharge the decision once, in `Order.agda`, and let `Partition` take it as a
parameter so it never mentions `le` or `Bool`:

```agda
-- Order.agda: the only place `le`'s decidability is used.
splitAtGen : (x y : El)
  → ⌈ ⌈gen y ⌉ ⌉ ⊢ (⌈ ⌈gen y ⌉ ⌉ & Below x) ⊕ (⌈ ⌈gen y ⌉ ⌉ & Above x)
splitAtGen x y with le y x | Eq.refl {x = le y x}      -- the one escape
… inl (id⊢ ,& bagAll-gen (belowEl x) y w)
… inr (id⊢ ,& bagAll-gen (aboveEl x) y (leTotal y x w))
```
```agda
-- Partition.agda: `side` and `sideOf` both vanish; `le`/`leTotal` become one parameter.
module Theory.Instances.Bags.Partition (El : Type ℓ-zero)
  (split : (x y : El) → ⌈ ⌈gen y ⌉ ⌉ ⊢ (⌈ ⌈gen y ⌉ ⌉ & Below x) ⊕ (⌈ ⌈gen y ⌉ ⌉ & Above x))
  where

consCase y = ⊕-elim putBelow putAbove ∘⊢ ⊕-⊎B-dist ∘⊢ ⊎Bmap (split x y) id⊢
```
`⊕-⊎B-dist` is the binary specialisation of `⊎B⊕ᴰ-dist` (`Extension.agda:311`) and is a
two-line addition. `putBelow`/`putAbove` are `put true`/`put false` verbatim, and
`consInto` (line 60–62) keeps its shape.

Net effect on `Partition.agda`: the file drops from 71 lines to roughly 45, mentions no
`Bool`, no `Eq`, and no metalanguage function.

---

### F4 (MEDIUM-HIGH) — dead code across the tree (~150 lines)

| Location | Item | Evidence |
|---|---|---|
| `Order.agda:111–123` | `bagAll-⊓` | referenced only at its own definition and in a comment on line 126 |
| `Order.agda:154–170` | `tmTrue`, `bagAll-⊤` | no external reference |
| `Order.agda:67–75` | `belowElM`, `aboveElM`, `BelowM`, `AboveM` | no reference anywhere in `src/`. The 3-line comment at 64–66 ("`nothing` is +∞… what pins the accumulator to `ε` at the top call") describes an **insertion-sort accumulator that no longer exists** — it is stale documentation for deleted code. |
| `Base.agda:53–58` | `⊙-inter` (the interchange law) | no reference |
| `Rank.agda:84–86` | `pivotDrops` | no reference. Its comment (81–83) says "A caller that has decomposed its input this way is entitled to two recursive calls" — but no such caller exists; `▷-split` is what callers actually use, and it goes through `paySplit`, not `pivotDrops`. Misleading. |
| whole file | `Generation.agda` | see F2 |

**Fix:** delete. If `bagAll-⊓` is kept as the "folds commute with ⊓ by uniqueness of homs"
demonstration the comment at 109–110 advertises, mark it `-- unused; kept as the
uniqueness-of-homs example` so the next reader does not hunt for callers.

---

### F5 (MEDIUM) — `Order`'s five splitting lemmas are raw λ over model elements, and are instance-specific when they should be generic

`src/Theory/Instances/Bags/Order.agda:85–107`
```agda
  bagAll-⊗ : (A ⊎B B) & bagAll p ⊢ (A & bagAll p) ⊎B (B & bagAll p)
  bagAll-⊗ m ((ms , e , (a , b , tt*)) , q) =
    ms , e , ((a , sp .fst) , (b , sp .snd) , tt*)
    where sp = subst (bagAll p) (sym (Eq.eqToPath e)) q

  ⊗-bagAll m (ms , e , ((a , qa) , (b , qb) , tt*)) =
    (ms , e , (a , b , tt*)) , subst (bagAll p) (Eq.eqToPath e) (qa , qb)

  bagAll-ε m Eq.refl = tt*
  bagAll-gen y q m Eq.refl = q
  bagAll-atGen y m (Eq.refl , q) = q , Eq.refl
```

**Verdict: justified in substance, avoidable in form.** These *are* axiomatisations of how
`bagAll` interacts with `⊎B` and `⌈⌉` — the sanctioned category of escape. Two concrete
improvements:

**(a) Route through the framework's designated hatch.** `Theory/Type/Operation/Base.agda:147`
provides `⊗&-overSplit`, whose whole reason for existing (per `GuardedSplit.agda:5–7`,
"`⊗-overSplit` is general for any signature, but its argument is a metalanguage function
on slot contents, so every call site steps out of the DSL. Here that is paid off") is to be
*the* place where a slot-level metalanguage function is handed in. `▷⊛r` uses it
(`GuardedSplit.agda:61`); `bagAll-⊗` open-codes the same destructuring instead:
```agda
  bagAll-⊗ = ⊗&-overSplit λ m ms e (a , b , tt*) q →
    let sp = subst (bagAll p) (sym (Eq.eqToPath e)) q
    in (a , sp .fst) , (b , sp .snd) , tt*
```
Same content, but now the escape is at the one audited site rather than a fresh raw λ.

**(b) Make it generic — this is the real win.** Nothing here is about bags. The
hypotheses are: `Ω` is a model of the theory (`⊓Ops`/`⊓Sat`, `Order.agda:33–43`), and
`bagAllP p = Cl.rec … p` is the induced hom. For *any* such hom into `Ω`, the same five
lemmas hold with the same proofs, because `Cl.rec ρ (node o ts) = α o (…)` reduces on the
nose (`Closing.agda:95`) — which is exactly what the comment at `Order.agda:48–49`
observes. Lift them into a module

```
Theory/Type/Predicate/Fold.agda
  module _ (α : Ops Ω) (sat : …) (p : V → hProp ℓ) where
    allOf   : TheoryTy ℓ s              -- ⟨ Cl.rec … p m ⟩
    all-⊗   : ⊗ᵘ[ o ] As & allOf ⊢ ⊗ᵘ[ o ] (λ a → As a & allOf)
    ⊗-all, all-gen, all-atGen, all-mono
```
Then `Order.agda` shrinks to `aboveEl`/`belowEl` plus `Above x = allOf ⊓Ops ⊓Sat (aboveEl x)`,
the `Strings`/`KleeneStar` side gets the same lemmas for free, and the escape is paid once
for all theories instead of once per instance.

**(c) Present the result internally.** The DSL has a subobject classifier:
`Theory/Type/Subgrammar/Base.agda:34` `Ω {ℓ'} _ = hProp ℓ'`, with
`Subgrammar (p : A ⊢ Ω)` at line 53. `Above x` is definitionally
`subgrammar (λ m _ → bagAllP (aboveEl x) m) : ⊤Ty ⊢ Ω`. Stating it that way makes the
*interface* internal (a predicate is a `⊢`-map into `Ω`; the type is the subgrammar it
classifies) while the fold stays the one external definition. **This is the answer to
"Order is a bit external": it is external at one point, correctly, and the fix is to say
so in the DSL's own vocabulary rather than to restructure the fold.**

`bagAll-mono` (`Order.agda:140–151`) and `tmMono` (`129–136`) are `CE.elimProp` +
recursion on `Tm`, i.e. external induction over the free model. **Justified**, and the
comment at 125–127 gives a real reason ("going through `bagAll-⊓` instead would mean
transporting along a `⇔toPath`, and that transport does not reduce even at a single
generator") — a computational justification, which is the right kind. Keep, but move into
the generic module from (b).

---

### F6 (MEDIUM) — `Sequence.agda` and `Sorted/Base.agda` are ~80% verbatim duplicates

Line-for-line correspondence:

| `Sequence.agda` | `Sorted/Base.agda` | difference |
|---|---|---|
| `25–29` `atSeqF`/`atSeq` | `24–28` `consAtF`/`consAt` | tail slot `Var tt` vs `Var tt &e2 k (LiftTheoryTy ℓM (Above x))` |
| `31–36` `seqBranch`/`SeqCode` | `30–35` `sortedBranch`/`SortedCode` | identical modulo the above |
| `43–44` `slots` | `41–42` `slots` | identical body |
| `48–55` `seqLayer` | `45–53` `sortedLayer` | one extra `lowerTy` in the tail |
| `57–63` `nilSeq`/`consSeq` | `55–61` `nilSorted`/`consSorted` | one extra `liftTy` |
| `66–74` `recSeq`/`caseSeq` | `63–71` `caseSorted`/`recSorted` | identical |
| `86–87` `seqElements` | `74–76` `elements` | one extra `⊎Bmap id⊢ π₁` |

**Fix.** One parameterised module, `Theory/Instances/Bags/ConsList.agda`, taking the tail
side-condition:
```agda
module Theory.Instances.Bags.ConsList (El : Type ℓ-zero) (Q : El → TheoryTy ℓ-zero tt) where
  atF x = two (k ⌈ ⌈gen x ⌉ ⌉) (Var tt &e2 k (LiftTheoryTy ℓM (Q x)))
  …
  cons : (x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (List & Q x) ⊢ List
  rec  : ⌈ εᵖ ⌉ ⊢ C → ((x : El) → ⌈ ⌈gen x ⌉ ⌉ ⊎B (C & Q x) ⊢ C) → List ⊢ C
```
`Seq = ConsList (λ _ → ⊤Ty)` and `Sorted = ConsList Above`. `Sequence.agda` and
`Sorted/Base.agda` become ~15 lines each. `Sorted/HLevels.agda:36–43`
(`isSetValuedSortedCode`) generalises the same way, parameterised by `∀ x → isSetTheoryTy (Q x)`.

Note `seqElements` (`Sequence.agda:87`) is itself dead — nothing references it. Under the
merge it disappears anyway.

---

### F7 (MEDIUM) — `Quicksort/Tests.agda` does not follow the `Suite` skeleton, and its expected output does not go through a semantic action

`src/Theory/Instances/Bags/Quicksort/Tests.agda:73–97`
```agda
sort : {m : Bag} → Seq m → List ℕ
sort {m} s = elements m (quicksort m s)

_ : sort ([]ᵍ) ≡ []
_ = refl
_ : sort (3 ∷ᵍ []ᵍ) ≡ 3 ∷ []
_ = refl
…
```

The maintainer's skeleton is `src/Theory/Type/SemanticAction/Base.agda:34–50` (module
`Suite`: `_↦_`, `_at_`, `passes`), used as in
`src/Theory/Instances/Monoid/Combinator/Grammars/ArithTests.agda:135–170`:
```agda
cases : List (Dec.String × M.Maybe Unit)
cases = ( (nm ∷ []) ↦ M.just tt ∷ … ∷ [] )

dec-arith : passes (parseDec at cases)
dec-arith = refl
```
Two deviations:

1. **No `passes`/`at`.** Ten separate anonymous `_ : … ≡ … ; _ = refl` declarations
   instead of one `cases` list and one `refl`. Nothing is named, so a failure reports an
   anonymous declaration rather than a case.
2. **The expected output does not come from a display semantic action.** `sort` goes
   through `elements : Sorted ⊢ K (List El)` (`Sorted/Base.agda:74`), i.e. `K` from
   `Extension.agda:288`, not `Δ`/`SemanticAction` from `SemanticAction/Base.agda:52–63`.
   `run`/`observe` are the sanctioned readback, and `K` bypasses them. `KleeneStar/Guarded.agda:143–150`
   shows the intended shape (`semact-*g` produces a `SemanticAction (A *) (List X)`).

**Fix:**
```agda
display : SemanticAction Sorted (List ℕ)
display = semact-rec (λ _ → sortedLayer (semact-pure [])
            (λ x → semact-map (x ∷_) ∘ …))         -- or reuse `elements` via Δ

sortOf : {m : Bag} → Seq m → List ℕ
sortOf {m} s = display m (quicksort m s) .fst

cases : List (Σ[ m ∈ Bag ] Seq m × List ℕ)      -- or a `List (Input × List ℕ)` wrapper
cases = ( (2 ∷ᵍ 1 ∷ᵍ []ᵍ)  ↦ (1 ∷ 2 ∷ [])
        ∷ (3 ∷ᵍ 1 ∷ᵍ 2 ∷ᵍ []ᵍ) ↦ (1 ∷ 2 ∷ 3 ∷ [])
        ∷ … ∷ [] )

quicksort-sorts : passes (sortOf at cases)
quicksort-sorts = refl
```
The inputs are already readable (`_∷ᵍ_` notation, aligned columns at lines 109–116) —
that part is good and should be kept.

**No tests are buried in definition files.** `[]ᵍ`/`_∷ᵍ_` (`Sequence.agda:77–83`) are
input *constructors*, not tests, and `Quicksort/Base.agda` ends at `quicksort`. Clean.

---

### F8 (MEDIUM) — the 41-line essay at the top of `Quicksort/Tests.agda`

`src/Theory/Instances/Bags/Quicksort/Tests.agda:1–41` and `118–123`.

This is the only genuine "top-of-file essay" in the tree. It is not slop — the content is
real (two reproducible pitfalls, with measurements: "`elements m s` is 0.7s and
`elements m (subst Sorted refl s)` is over 45s") and it correctly explains why
`Join.nilJ` uses `⊎B-unitL⌈⌉` rather than `⊎B-unitL`. **But it is in the wrong file, and
the essay says so itself** (lines 4–6: "the two pitfalls are recorded here rather than at
the sites, which are spread over `Bags/Base`, `Inductive/Base`, `Join` and
`Quicksort/Base`").

**Fix.** Move pitfall (1) to `Theory/Type/Inductive/Base.agda` (where `μ` and `rec` live —
it is a property of the framework, not of bags) with a one-line back-reference at
`Join.agda:60–62`; move pitfall (2) to `Guarded/Base.agda` beside the `fold` comment at
81–84, which already makes the same point from the other direction. Move the benchmark
paragraph (118–123) to a forest note. Leave in `Tests.agda` a three-line header: what the
tests cover, and that `2 ∷ᵍ 1` / `1 ∷ᵍ 2` must both be kept because they separate under
pitfall (1).

---

### F9 (MEDIUM) — `Quicksort/Base.agda:37` leaks the whole guarded interface publicly

```agda
open Guarded▷ QS isSetQS
```
at top level, outside the surrounding `private` blocks. `Guarded▷` re-exports all of
`Löb` (`Guarded/Base.agda:36–51`: `▷`, `next`, `app`, `löb`, `löb-unfold`, `löb-uniq`,
`app-next`) plus `▷-cons`/`▷-split`. So anything importing `Quicksort.Base` — including
`Tests.agda` — gets `▷` and `app` for the `Seq ⇒ Sorted` family in scope. `Join.agda:48`
does it correctly, inside `module _ (x : El)`.

**Fix:** `private module G = Guarded▷ QS isSetQS` and qualify `G.▷`, `G.löb`, `G.▷-split`;
or move line 37 into the `private` block that begins at line 39.

---

### F10 (MEDIUM) — `Fam` is defined in `Rank.agda`, duplicating `IFam`

`src/Theory/Instances/Bags/Rank.agda:48–49`
```agda
Fam : (ℓA : Level) → Type _
Fam ℓA = (s : Sorts) → TheoryTy ℓA s
```
This is `IFam xs ℓA` from `Theory/Type/Later/Indexed` (used throughout
`Guarded/Justification.agda:48,69,99,119,142`), specialised to `xs = λ s → s`. Both
`Join.agda:40` and `Quicksort/Base.agda:31` import it *from `Rank`* — a module about bag
size — purely to write a löb motive.

**Fix:** re-export `IFam` from `Guarded/Base.agda` next to `Pt` (`Guarded/Base.agda:28`),
and delete `Rank.Fam`. `Rank` should export only `size`, `_◃_`, and `Guarded▷`.

---

### F11 (LOW-MEDIUM) — unreadable projection re-association in `Join`, uncommented

`src/Theory/Instances/Bags/Join.agda:103–104`
```agda
              (((π₂ ∘⊢ π₁) ,& ((π₁ ∘⊢ π₁ ∘⊢ π₁) ,& π₂))
                ,& (π₂ ∘⊢ π₁ ∘⊢ π₁))
```
and `Join.agda:88`
```agda
        ∘⊢ ((π₁ ,& (π₂ ∘⊢ π₂)) ,& (π₁ ∘⊢ π₂))
```

I traced both and they are correct (see §2), but reconstructing that took several minutes
of unwinding `((Sorted & Above y) & JN tt) & Below x` by hand. Neither has a comment. A
reader six months from now will not attempt it.

**Fix:** either a one-line comment naming the target shape —
`-- (JN tt & (Sorted & Below x)) & Above y : the motive's argument, then the tail's bound` —
or, better, introduce named `&`-projections locally:
```agda
      private
        theRec  = π₂ ∘⊢ π₁              -- JN tt
        theLeft = π₁ ∘⊢ π₁ ∘⊢ π₁        -- Sorted (the left half)
        leftBd  = π₂ ∘⊢ π₁ ∘⊢ π₁        -- Above y
        pivotBd = π₂                     -- Below x
```

---

### F12 (LOW) — meaningless local names

| Location | Name | Suggested |
|---|---|---|
| `Partition.agda:39,41` | `go` | `decideSide` — and it disappears under F3 |
| `Join.agda:40` | `JN` | `Joining` or `JoinMotive` |
| `Join.agda:82` | `pre` | `regroup` / `splitBound` |
| `Join.agda:90` | `body` | `consBody` |
| `Join.agda:53,74,90,96` | `w`, `w'` | `y≤x` |
| `Quicksort/Base.agda:43` | `qs` | `qsBody` (it is the guarded body, distinct from `quicksort` at 58) |
| `Quicksort/Base.agda:55` | `step` | `qsStep`, matching `Join.stepJ` |
| `Generation.agda:70,74` | `fold`, `fold-fst` | moot under F2 |
| `Order.agda:129,154` | `tmMono`, `tmTrue` | acceptable; keep |

`Rank`'s names (`oneDrop`, `bothDrop`, `genDrop`, `payCons`, `paySplit`, `ltLeft`,
`ltRight`) are good and say what they mean.

---

### F13 (LOW) — unused imports and a name clash

| Location | Item |
|---|---|
| `Base.agda:5` | `import Cubical.Data.Equality as Eq` — zero uses |
| `Base.agda:6` | `FinData using (Fin ; zero ; suc)` — zero uses (`ℓ-zero` matches are unrelated) |
| `Sequence.agda:15` | `Isomorphism using (Iso)` — zero uses |
| `Sorted/Base.agda:13` | `Isomorphism using (Iso)` — zero uses |
| `Quicksort/Base.agda:16` | `FinData using (Fin) renaming (zero to fzero ; suc to fsuc)` — none of `Fin`/`fzero`/`fsuc` used |
| `Quicksort/Base.agda:17` | `tt*` unused |
| `Rank.agda:11` | `Fin` unused; **and `zero`/`suc` are imported here *and* from `Cubical.Data.Nat` at line 12** — an ambiguity Agda resolves by type, but a trap |
| `Rank.agda:14` | `open import Cubical.Data.Nat using (+-suc)` — unused, and a redundant second import of the same module |
| `Rank.agda:15,17` | `Nat.Order.Recursive` imported twice (once `renaming (_<_ to _<ℕ_) using ()`, once `as R`); collapse to one `as R` and write `R._<_` |
| `Rank.agda:19` | `tt*` unused |

---

### F14 (LOW) — stale and restating comments

- `Order.agda:64–66` — describes a `Maybe`-bounded accumulator ("what pins the accumulator
  to `ε` at the top call") for code that no longer exists. **Stale; delete with F4.**
- `Rank.agda:81–83` — "A caller that has decomposed its input this way is entitled to two
  recursive calls" — no such caller. **Stale; delete with `pivotDrops`.**
- `Order.agda:104–105` — "at a generator the fold *is* `p`, so the witness can be read back
  out as a constant" restates the one-line body. Mild.
- `Partition.agda:6–7` — "it is a map into a sum, so the algebra below eliminates it rather
  than casing" is slightly self-congratulatory given that `sideOf` *does* case (line 39).

**Comments that are good and should be kept verbatim:** `Join.agda:1–8` (why löb and not
structural), `Generation.agda:1–4` (why the truncation makes the total space a model),
`Order.agda:109–110` and `125–127` (uniqueness-of-homs, and why it is not usable),
`Rank.agda:101–104` ("These are proofs, not terms, and necessarily so: they relate the
point `ms a` to the point `m`, and a `⊢`-map preserves its index"), `Order.agda:138`
("opaque: its result is a bound, never something an answer is read from").

**Non-obvious math with no comment:**
- `Base.agda:38–45` `fromTm` — the `swap`/`var` reshuffle is unexplained. One line: *"the
  `comm` equation's rhs, read as a two-slot tuple: the payload is permuted, nothing is
  transported."* Note it mirrors `Extension.agda:157–168` `fromTmA` and should say so.
- `Base.agda:53–58` `⊙-inter` — the interchange law, unlabelled. (Dead; delete.)
- `Sequence.agda:81–83` `_∷ᵍ_` — the hand-built `(two ⌈gen x⌉ m , Eq.refl , (Eq.refl , s , tt*))`
  tuple is the raw `⊗ᵘ` shape, contradicting the file header's promise (lines 3–4) that
  "downstream files never see the code's `⊗ᵘ` shape". It should be
  `consSeq x _ (⊗ᵘ→⊎B … )` or, better, `consSeq x ∘⊢ …` applied to a `⌈⌉`-intro.

---

### F15 (LOW) — `sortHalf` hardcodes a level

`src/Theory/Instances/Bags/Quicksort/Base.agda:40`
```agda
  sortHalf : {P : TheoryTy ℓ-zero tt} → (Seq & P) & QS tt ⊢ Sorted & P
```
Works because `Below x`/`Above x` land in `ℓ-zero` (`Order.agda:60`), but there is no
reason to pin it. `{ℓP} {P : TheoryTy ℓP tt}` costs nothing.

---

## 2. `▷` and `▷-split`: verification

**Definitions.** `▷` comes from `Löb` (`Guarded/Base.agda:36–51`), instantiated in
`Rank.agda:92–98` by
```agda
    bagLöb = löbByMeasure isSetUnit ℕWFRec (λ p → size (p .snd)) (λ r → r) A isSetA
```
`löbByMeasure` (`Guarded/Justification.agda:95–102`) reduces to `löbFrom (irankOrder …)`,
which builds `▷` from a direct category's downsets. **No `TERMINATING` anywhere in
`Later/Indexed`, `Later/Tabulated`, or `Guarded/Justification`** — I grepped the whole of
`src/Theory/`; the only pragmas are in `Coinductive/Base`, `Inductive/Base`, and
`Inductive/HLevels`. So the löb fixed point is genuinely well-founded, on `ℕWFRec` over
`size`. No circularity: `size` (`Rank.agda:46`) is `Cl.rec` on the free model, which is
structural, and the order `_◃_` (`Rank.agda:53–54`) is `<ℕ` on it.

**`▷-split`.** `Rank.agda:124–127`
```agda
  ▷-split : ∀ {ℓB} (y : El) {B C : TheoryTy ℓB tt}
    → (⌈ ⌈gen y ⌉ ⌉ ⊎B (B ⊎B C)) & ▷ tt
    ⊢ ⌈ ⌈gen y ⌉ ⌉ ⊎B ((B & A tt) ⊎B (C & A tt))
  ▷-split y = ▷⊛r² bagLöb (paySplit y)
```
against `GuardedSplit.agda:71–73`
```agda
  ▷⊛r² : PayR² {X = X} → (X ⊛ (B ⊛ B')) & ▷ tt ⊢ X ⊛ ((B & C tt) ⊛ (B' & C tt))
```
`_⊛_` (`GuardedSplit.agda:44`) is `⊗[ _⊙_ ][ two ℓA ℓB ] (A , B , tt*)` — **syntactically
identical** to `_⊗ₑ_` (`Extension.agda:86`), which `Bags/Base.agda:28` renames to `_⊎B_`.
So the two signatures line up on the nose. ✔

**The payment is arithmetically correct.** `Rank.agda:105–116`:
```agda
    genDrop y m ms e hd =
      sym (cong size (Eq.eqToPath e))
      ∙ cong (_+ size (ms (suc zero))) (cong size (Eq.eqToPath hd))
    paySplit y m ms ns e e' hd =
      bothDrop (genDrop y m ms e hd ∙ cong suc (sym (cong size (Eq.eqToPath e'))))
```
- `e : op _⊙_ ms Eq.≡ m` ⟹ `size m ≡ size (op _⊙_ ms)`, and `size (op _⊙_ ms)` reduces
  definitionally to `size (ms 0) + size (ms 1)` because `Cl.rec ρ (node o ts) = α o …`
  (`Closing.agda:95`) and `+Ops _⊙_ f = f zero + f (suc zero)` (`Rank.agda:35`).
- `hd : ms 0 Eq.≡ ⌈gen y ⌉` ⟹ `size (ms 0) ≡ 1` (the `var` clause, `Rank.agda:46`,
  `λ _ → 1`). So `genDrop : size m ≡ suc (size (ms 1))`. ✔
- `e' : op _⊙_ ns Eq.≡ ms 1` ⟹ `suc (size (ms 1)) ≡ suc (size (ns 0) + size (ns 1))`.
  Composed: `size m ≡ suc (size (ns 0) + size (ns 1))`, which is exactly `bothDrop`'s
  hypothesis (`Rank.agda:75`), and `bothDrop` returns the pair `PayR²` demands
  (`GuardedSplit.agda:66–69`). ✔
- The two order facts: `ltLeft a b : a <ℕ suc (a+b)` reduces (recursive `≤`) to `a ≤ a+b`,
  discharged structurally; `ltRight a b : b ≤ a+b` by `≤-suc`. `oneDrop` uses
  `R.≤-refl (size n) : size n ≤ size n`, which *is* `size n <ℕ suc (size n)` definitionally.
  All correct, no transport in the ordering. ✔

**`▷-split`'s use site type-checks.** `Quicksort/Base.agda:44–53`, traced right to left:

| step | type after |
|---|---|
| input to `⇒-intro` | `(⌈⌈gen y⌉⌉ ⊎B Seq) & ▷ tt` |
| `(⊎Bmap id⊢ (partSeq y) ,&p id⊢)` | `(⌈⌈gen y⌉⌉ ⊎B ((Seq & Below y) ⊎B (Seq & Above y))) & ▷ tt` |
| `▷-split y` | `⌈⌈gen y⌉⌉ ⊎B (((Seq & Below y) & QS tt) ⊎B ((Seq & Above y) & QS tt))` |
| `⊎Bmap id⊢ (⊎Bmap sortHalf sortHalf)` | `⌈⌈gen y⌉⌉ ⊎B ((Sorted & Below y) ⊎B (Sorted & Above y))` |
| `⊎B-assoc⁻` | `(⌈⌈gen y⌉⌉ ⊎B (Sorted & Below y)) ⊎B (Sorted & Above y)` |
| `⊎Bmap ⊎B-comm id⊢` | `((Sorted & Below y) ⊎B ⌈⌈gen y⌉⌉) ⊎B (Sorted & Above y)` |
| `⊎B-assoc` | `(Sorted & Below y) ⊎B (⌈⌈gen y⌉⌉ ⊎B (Sorted & Above y))` |
| `join y` | `Sorted` ✔ (`Join.agda:114`, `Pivot y = ⌈⌈gen y⌉⌉ ⊎B (Sorted & Above y)`) |

Level side-condition: `▷⊛r²` requires `B B' : TheoryTy ℓB tt` at the **same** level. Here
`B = Seq & Below y` and `C = Seq & Above y`, both `ℓ-max (ℓF ℓM) ℓ-zero`. ✔

**`▷-cons`'s use site type-checks.** `Join.agda:82–88` (`pre`), traced: the pairing at
line 88 delivers `((⌈⌈gen y⌉⌉ ⊎B (Sorted & Above y)) & ▷ tt) & Below x`; `▷-cons y ,&p id⊢`
with `B = Sorted & Above y`, `A = JN` gives `(⌈⌈gen y⌉⌉ ⊎B ((Sorted & Above y) & JN tt)) & Below x`;
`bagAll-⊗ (belowEl x)` gives exactly `pre`'s declared codomain. ✔

I also traced `nilJ` (60–69), `consJ` (71–94), `tailJ` (96–105), `pivotAbove` (53–58),
`stepJ` (107–111) and `join` (114–116). **All type-correct.** In particular `nilJ`'s use of
`⊎B-unitL⌈⌉` (`Extension.agda:257`) rather than `⊎B-unitL` is genuine and important: the
latter is `subst A path a` (`Extension.agda:238`), which would transport a `Sorted`
payload, whereas `⊎B-unitL⌈⌉` produces an `Eq.pathToEq` in `Bag` — the representable's
index moves, the `μ`-payload does not. That is exactly what `Tests.agda:20–24` describes,
and it is correct.

Likewise `⊎B-comm` (`Bags/Base.agda:43–45`) genuinely repackages rather than transports:
`fromTm` (`Base.agda:41`) permutes the tuple `(y , x , tt*)` with no `subst`, and
`eqn→fun` (`Operation/Base.agda:241`) only rebuilds the `Eq.≡` witness. The Tests header's
claim on line 24–25 holds.

**Caveat.** All of this is hand-tracing. Level unification under `--lossy-unification`,
implicit-argument inference in the long `∘⊢` chains, and the `two`/`three` tuple
η-expansions are exactly where a hand trace can be wrong. I did not run the typechecker,
so treat "type-correct" as "consistent with every definition I read", not as proof.

---

## 3. Catalogue of DSL escapes

| # | Site | What escapes | Verdict |
|---|---|---|---|
| 1 | `Base.agda:38–45` `fromTm` | raw λ over `⟪ … ⟫` tuples | **Justified** — axiomatising `⊗`-commutativity from the `comm` equation; mirrors `Extension.agda:157` |
| 2 | `Base.agda:47–58` `⊙-comm`, `⊙-inter` | `M .snd .snd`, paths in the carrier | **Justified** (`⊙-comm`; it *is* the equation). `⊙-inter` dead |
| 3 | `Generation.agda:25–90` | `View`, `Tops`, `TSat`, `Cl.rec`, `Cl.recUniq` over model elements | **Avoidable / dead** — F2 |
| 4 | `Order.agda:33–46` `⊓Ops`/`⊓Sat`/`bagAllP` | a model of the theory in `hProp` | **Justified** — this is how a predicate is defined; should be generic (F5b) and presented via `Subgrammar` (F5c) |
| 5 | `Order.agda:87–107` (five lemmas) | raw λ, `Eq.refl` on the model, `subst` | **Justified in substance, avoidable in form** — F5a |
| 6 | `Order.agda:129–151` `tmMono`/`bagAll-mono` | `CE.elimProp`, recursion on `Tm` | **Justified** — documented computational reason at 125–127 |
| 7 | `Order.agda:154–170` `tmTrue`/`bagAll-⊤` | same | **Dead** — F4 |
| 8 | `Partition.agda:33–44` `side`/`sideOf`/`go` | external `Bool` match, `Eq.refl` on `le` | **Avoidable packaging** of a justified decision — F3 |
| 9 | `Rank.agda:30–46` `+Ops`/`+Sat`/`size` | a model of the theory in `ℕ` | **Justified** — the measure; `Guarded/Justification.agda:93–94` names this "the *only* place a consumer's size argument has to go" |
| 10 | `Rank.agda:56–86, 105–116` payments | proofs relating `ms a` to `m` | **Justified**, and correctly explained at 101–104 — a `⊢`-map preserves its index, so this cannot be internal |
| 11 | `Sequence.agda:77–83` `[]ᵍ`/`_∷ᵍ_` | raw `⊗ᵘ` tuple, `Eq.refl` | **Justified in purpose** (concrete test inputs) but contradicts the file's own header — F14 |

Nothing in the tree matches on `List` as model data, uses `Discrete`, or takes a raw λ over
`μ`. The discipline is broadly good; the failures are concentrated in `Generation`,
`Partition`'s decision, and `Order`'s five lemmas.

---

## 4. Recommended order of work

1. Delete `Generation.agda` (or finish it into `arrange : (m : Bag) → ∥ Seq m ∥₁`) — F2.
2. Delete the dead code in F4 (`bagAll-⊓`, `bagAll-⊤`, `tmTrue`, `*ElM`/`*M`, `⊙-inter`,
   `pivotDrops`, `seqElements`) and the stale comments that document it.
3. Fix `Partition` per F3: `Order.splitAtGen`, `_⊕_` instead of `⊕[ b ∈ Bool ]`, `side`/`go`
   gone, `le`/`leTotal` out of `Partition`'s parameters.
4. Correct the headers about `TERMINATING` (F1), then replace `recSeq`/`recSorted` with
   löb folds following `KleeneStar/Guarded.fold*g`.
5. Merge `Sequence` and `Sorted/Base` into `ConsList` (F6).
6. Rewrite `Quicksort/Tests.agda` on the `Suite` skeleton with a `Δ`-valued display action;
   relocate the essay (F7, F8).
7. Lift `Order`'s splitting lemmas into a generic `Predicate/Fold` module (F5b), present
   `Above`/`Below` as `Subgrammar`s (F5c).
8. Cleanups: F9 (`private` the `Guarded▷` open), F10 (`Fam` → `IFam`), F11–F15.
