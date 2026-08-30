# Audit: the DSL core

Scope read in full: `src/Theory/Base.agda`, `src/Theory/Free/{Base,Closing,Term}.agda`,
all 46 files of `src/Theory/Type/**`, `src/Cubical/Algebra/Theory/Finitary{,/Free/Closing,/Free/ClosingElim}.agda`.
~5100 lines. No `agda` was run.

Note: `ClosingElim.agda` was edited at 13:45 today, mid-review. The general dependent
eliminator now exists there; §3 below reviews the *new* version and says what is still
missing around it.

---

## 1. Coherence and completeness of the connective API

### 1.1 `Δ` means two different things, and clients pay for it — SEVERITY: HIGH

`src/Theory/Type/Product/Base.agda:48`

```agda
  Δ : A ⊢ &[ y ∈ Y ] A
```

`src/Theory/Type/SemanticAction/Base.agda:52`

```agda
Δ : {s : S} → Type ℓX → TheoryTy ℓX s
Δ X = ⊕[ x ∈ X ] ⊤Ty
```

One is the diagonal `A → Aᵞ`; the other is the discrete/constant type former `K X`.
Both are core connectives on the task's own list. The collision is already load-bearing
downstream:

- `src/Theory/Instances/Monoid/Types.agda:36-37` — `open import ... SemanticAction ... public hiding (Δ)`
- `src/Theory/Instances/Monoid/SemanticAction.agda:17` — `hiding (Δ)`
- `src/Theory/Instances/Monoid/Phase/Display.agda:48` and `:200` — `hiding (Δ)`
- Clients that want the type former must qualify: `SemAct.Δ` (`Grammars/Dyck.agda:173`),
  `Act.Δ` (`KleeneStar/Guarded.agda:145`, `Automaton/TokenStream.agda:192`).

`Product/Base.agda:48`'s `Δ` has **zero** uses anywhere in the repo.

**Fix.** Rename the diagonal to `&ᴰ-Δ` (matching `&-Δ` in `Product/Binary/Base.agda:81`)
or delete it — it is `&ᴰ-intro (λ _ → id⊢)` and nobody calls it. Then `Δ` in
`SemanticAction` is unambiguous, and the four `hiding (Δ)` clauses go away.

Related, same file: `src/Theory/Type/SemanticAction/Base.agda:46` exports `_at_`, which
collides with `src/Theory/Type/Decidable/Base.agda:49`'s `at`. `Types.agda:42-44` carries
the comment ``-- `at` clashes with the `_at_` of `SemanticAction`, which every test uses``
and a `hiding (at)`. Two of the five `hiding` clauses in the instance layer exist only to
patch core-module name collisions.

### 1.2 `Δ` has no intro/elim/β/η at all — SEVERITY: HIGH

`Δ X = ⊕[ x ∈ X ] ⊤Ty` is declared at `SemanticAction/Base.agda:52` and then never given a
rule set. Its universal property (`(⊤Ty ⊢ A) ≅ ... `, or in adjoint form
`Hom(Δ X, A) ≅ (X → Hom(⊤Ty, A))`) is scattered across ad-hoc `semact-*` combinators:

- `semact-pure` (`:65`) *is* `Δ-intro : X → ⊤Ty ⊢ Δ X`
- `semact-map` (`:69`) *is* `Δ-map`, and is implemented by escaping to the model (§2.3)
- `run` (`:58`) *is* the extraction `(⊤Ty ⊢ Δ X) → ↓M s → X`
- `Δ-⊗` (`:120`) is the only lemma named after the connective

**Fix.** Give `Δ` its own module `Theory/Type/Discrete/Base.agda` with
`Δ-intro`, `Δ-elim : ((x : X) → A ⊢ B) → Δ X & A ⊢ B`, `Δ-map`, `Δ-β`, `Δ-η`, `Δ≅`, and
have `SemanticAction/Base.agda` import it and keep only the semantic-action-specific
wrappers.

### 1.3 The β/η/≅/map table, and its holes — SEVERITY: HIGH (aggregate)

| connective | site | intro | elim | β | η | `≡`-ext | `≅` cong | map |
|---|---|---|---|---|---|---|---|---|
| `⊤Ty` | Top/Base:22 | `⊤Ty-intro` | — | — | `⊤Ty-η` | — | `≅⊤Ty` (Properties:37) | — |
| `⊤Ty↑` | Top/Base:25 | **missing** | — | — | **missing** | — | — | — |
| `⊥Ty` | Bottom/Base:22 | — | `⊥Ty-elim` | — | `⊥Ty-η` | — | — | — |
| `⊥Ty↑` | Bottom/Base:25 | — | `⊥Ty↑-elim` | — | `⊥Ty↑-η` | — | — | — |
| `&ᴰ` | Product/Base:25 | `&ᴰ-intro` | `π` | **missing** | **missing** | `&ᴰ≡` | `&ᴰ≅` | `map&ᴰ` |
| `⊕ᴰ` | Sum/Base:22 | `σ⊕` | `⊕ᴰ-elim` | **missing** | **missing** | `⊕ᴰ≡` | **missing** | `map⊕ᴰ`, `mapFst⊕ᴰ` |
| `&` | Product/Binary:33 | `&-intro` | `π₁ π₂` | `&-β₁ &-β₂` | `&-η` | `&≡` | `&≅` | `&par` |
| `⊕` | Sum/Binary:34 | `inl inr` | `⊕-elim` | `⊕-βl ⊕-βr` | `⊕-η` | `⊕≡` | `⊕≅` | `_,⊕p_` |
| `⇒` | Function/Base:27 | `⇒-intro` | `⇒-app` | `⇒-β` | `⇒-η` | — | **missing** | **missing** |
| `⊗` | Operation/Base:56 | `⊗-intro` | `⊗-elim` | **missing** | **missing** | `⊗≡`/`⊗PathP` | **missing** | `⊗map`, `⊗map[_][_]` |
| `⊸` | Residual/Base:198 | `⊸-intro` | `⊸-intro⁻` | `⊸-β` | `⊸-η` | — | `⊸Iso` | **missing** |
| `√` | Later/Derivative:30 | `√-intro` | `√-intro⁻` | `√-β` | `√-η` | — | `√Iso` | **missing** |
| `¬Ty` | Decidable/Base:37 | — | — | — | — | — | — | `¬Ty-map` |
| `Lift` | Lift/Base:22 | `liftTy` | `lowerTy` | **missing** | **missing** | — | **missing** | **missing** |
| `equalizer` | Equalizer/Base:25 | `eq-intro` | `eq-π` | `eq-β` | `eq-η` **in another module** | `eq-ext` (elsewhere) | **missing** | `equalizer-cong` |
| `subgrammar` | Subgrammar/Base:54 | `sub-intro` | `sub-π` | `sub-β` | `sub-η` | `isMono-sub-π` | **missing** | `preimage-map` |
| `μ` | Inductive/Base:25 | `roll` | `rec` | `recHomo` | `μ-η` | `ind` | **missing** | — |
| `ν` | Coinductive/Base:24 | `corec` | `unroll` | `corecHomo` | `ν-η` | `coind` | **missing** | — |
| `▷` | Guarded/Base:40 | `next` | `app` | `app-next` | `löb-uniq` | — | — | `▷map` (Later/Indexed:227) |
| `∥_∥` | PropTrunc:36 | `trunc` | `elim∥∥` | — | — | — | `∥∥idem` | `∥∥-map` |

The individually-actionable holes:

1. **`⊗` has no β/η and no `≅`** — `src/Theory/Type/Operation/Base.agda:111-124`.
   `⊗` is *the* connective of this DSL (it is where the theory's operations become types),
   and it is the one with the weakest rule set. There is no
   `⊗-β : ⊗-elim As f _ (⊗-intro As ms xs) ≡ f xs`, no `⊗-η`, and no
   `⊗≅ : (∀ a → A a ≅ B a) → ⊗ᵘ[ o ] A ≅ ⊗ᵘ[ o ] B` even though `⊗map` is right there at
   `:158`. Every downstream `≅`-chain through a `⊗` therefore has to be built by hand.
   **Fix.** Add `⊗-β`, `⊗-η` (both `refl` / one `⊗PathP`), and `⊗≅`/`⊗ᵘ≅` built from
   `⊗map` + `⊗≡`, next to `⊗map`.

2. **`Lift` has *only* `liftTy`/`lowerTy`** — `src/Theory/Type/Lift/Base.agda:25-29`.
   No `lower-lift : lowerTy ∘⊢ liftTy ≡ id⊢`, no `lift-lower`, no
   `LiftTheoryTy≅ : A ≅ LiftTheoryTy ℓB A`, no `mapLift`. `Code/Base.agda:56,65,79`
   silently relies on `liftTy ∘⊢ lowerTy ≡ id⊢` holding by `refl` (records with eta), i.e.
   the missing lemma is being inlined as `refl` at three sites. **Fix.** State the four
   lemmas; `Code/Base` then reads `map-id (k K) = lift-lower` instead of `i = id⊢`.

3. **`⊤Ty↑` is a former with no rules** — `src/Theory/Type/Top/Base.agda:25`.
   Its sibling `⊥Ty↑` (`Bottom/Base.agda:36-40`) got `⊥Ty↑-elim` and `⊥Ty↑-η` with the
   explicit comment "the same at the lifted empty type, so a client never has to unfold
   it". The lifted unit got nothing, so a client *does* have to unfold it. **Fix.**
   Add `⊤Ty↑-intro` and `⊤Ty↑-η`, mirroring lines 36-40 of `Bottom/Base.agda`.

4. **`&ᴰ`/`⊕ᴰ` have `≡`-extensionality but no β** — `Product/Base.agda:39-45`,
   `Sum/Base.agda:36-42`. `π y ∘⊢ &ᴰ-intro f ≡ f y` and `⊕ᴰ-elim f ∘⊢ σ⊕ y ≡ f y` are both
   `refl` and both unstated, while their binary counterparts `&-β₁`/`⊕-βl` are stated.
   A client doing equational reasoning has to drop to `refl` at exactly the indexed case.

5. **`⊕ᴰ` has no `≅`; `&ᴰ` has no reindexing map** — `Sum/Base.agda` ends at
   `mapFst⊕ᴰ:56` with no `⊕ᴰ≅`, while `Product/Base.agda:62` has `&ᴰ≅`; conversely
   `Product/Base.agda` has no `mapFst&ᴰ`. The two dual modules each have exactly the
   lemma the other is missing.

6. **`&-assoc` has no `≅`** — `Product/Binary/Base.agda:87-91` defines `&-assoc` and
   `&-assoc⁻` and stops; `Sum/Binary/Base.agda:126` packages the dual pair as
   `⊕-assoc≅`. Also `Product/Binary/Base.agda:75` has `id&_` with no `id⊕_` counterpart.

7. **`⇒` has no functoriality and no `≅`** — `Function/Base.agda`. There is no
   `⇒map : B ⊢ A → C ⊢ D → (A ⇒ C) ⊢ (B ⇒ D)` and no `⇒≅`, so `Monad/Cont.agda`'s
   `Cont R A = (A ⇒ R) ⇒ R` cannot be shown functorial without dropping to pointwise λs.

8. **`equalizer`'s β and η live in different modules** —
   `eq-β` at `src/Theory/Type/Equalizer/Base.agda:39`, `eq-η` at
   `src/Theory/Type/Subgrammar/Equalizer.agda:53`, `eq-ext` at `:59`. Discoverability:
   a client who imports `Equalizer/Base` gets β but silently no η. The `Subgrammar/Equalizer`
   header even says this out loud ("which is what buys `eq-η`"). **Fix.** Either move
   `eq-η`/`eq-ext` into `Equalizer/Base` (they need only `isSetB`, not the classifier),
   or make `Equalizer/Base` re-export them.

9. **`⊗&ᴰ-dist` is one-sided and uncommented** — `src/Theory/Type/Distributivity.agda:50`

   ```agda
   ⊗&ᴰ-dist : ⊗ᵘ[ o ] (λ a → &[ y ∈ Y ] A a y) ⊢ &[ y ∈ Y ] ⊗ᵘ[ o ] (λ a → A a y)
   ```

   Its sibling `⊗⊕ᴰ-dist` (`:32`) comes with `⊗⊕ᴰ-dist⁻` and `⊗⊕ᴰ-dist≅` (`:36,:40`).
   `⊗&ᴰ-dist` has neither, and no comment saying *why* — the direction is genuinely not
   invertible (`&` is a limit, `⊗` is not a left adjoint in that variable), and a reader
   cannot tell that from the file. `Theory/Instances/Monoid/Types.agda:47-49` records the
   client-side cost: "distributivity `⊗⊕-distL` is missing an inverse for". **Fix.** One
   comment line stating the non-invertibility, plus the `⊗&ᴰ-dist⁻` in the direction that
   *does* hold when `Y` is inhabited if that is wanted.

10. **`&` over `⊕` distributivity is duplicated outside `Distributivity.agda`** —
    `src/Theory/Type/Sum/Binary/Base.agda:50`

    ```agda
    ⊕-elim& : {D : TheoryTy ℓD s} → D & A ⊢ B → D & C ⊢ B → D & (A ⊕ C) ⊢ B
    ⊕-elim& eA eB _ (d , Sum.inl p) = eA _ (d , p)
    ```

    with 31 call sites. This is the binary `&`/`⊕` distributivity, hand-matched, living
    in the `⊕` module rather than in `Distributivity.agda` where the ⊗-versions live.
    **Fix.** Move it (or a `&⊕-dist≅`) into `Distributivity.agda` and define `⊕-elim&`
    from it, so all distributivity is in one place.

### 1.4 `▷` is the one connective with no `⊢`-level rules — SEVERITY: HIGH

`src/Theory/Type/Later/Indexed.agda:169,175`

```agda
      ▷app : ∀ {x m x' m'} → (x' , m') < (x , m) → ▷ x m → A x' m'
      ▷intro : ∀ {x m} → (∀ x' m' → (x' , m') < (x , m) → A x' m') → ▷ x m
```

Both bind `m`, take a raw element of `▷ x m`, and return a raw element — they are not
`⊢`-arrows. Every other connective's intro/elim is a morphism. This propagates into the
abstract interface: `src/Theory/Type/Guarded/Base.agda:42`

```agda
      app : ∀ {x m x' m'} → R (x' , m') (x , m) → ▷ x m → A x' m'
```

is the only field of `Löb` stated pointwise (`next`, `löb`, `löb-unfold`, `löb-uniq` are
all in `⊢`), and `app-next` at `:49-51` is then forced to state the β-law as a pointwise
equation `app r (next t x m tt) ≡ t x' m' tt` rather than as a composite of arrows.

This is the single biggest reason downstream guarded code drops out of the DSL. **Fix.**
`R` is a relation on `Pt xs = Σ x, ↓M (xs x)`, so the natural arrow forms are
`▷-elim : (r : R p q) → ▷ (q .fst) ⊢ Derivative (const (p .snd)) (A (p .fst))` — i.e. use
`Later/Derivative.agda`'s `Derivative`/`√`, which is exactly the "reindex a type along a
carrier map" former this needs and which already has `√-intro/√-intro⁻/√-β/√-η/√Iso`.
Stating `app` as `▷ x ⊢ √ f (A x')` would make `▷` a normal connective and would connect
the two halves of `Later/` that are currently unrelated.

### 1.5 The residual exists twice under different names — SEVERITY: MEDIUM

- `src/Theory/Type/Residual/Base.agda:189-198` — `Resid o ℓs As i B`, syntax
  `As ⊸⟨ o [ ℓs ] at i ⟩ B`, with `⊸-intro/⊸-intro⁻/⊸-β/⊸-η/⊸Iso`.
- `src/Theory/Type/Later/Derivative.agda:30` — `√ f A`, with
  `√-intro/√-intro⁻/√-β/√-η/√Iso`, plus `√At`/`DerivativeAt` (`:72,:66`) which specialise
  `√` back to exactly the operation-slot case `Resid` handles.

They are the same adjunction (right adjoint to reindexing along a carrier map), stated
twice with different proofs, and the second is filed under `Later/` for no stated reason.
`Later/Derivative.agda:23` even does `open import ... Residual.Base ... public`, so a
client importing "Derivative" gets the whole residual API re-exported.

**Fix.** Make `Resid` a *definition* in terms of `√` (`Resid o ℓs As i B = √ (op o ∘ fillVals …) …`
composed with the hole-context), derive `⊸-β/⊸-η` from `√-β/√-η`, and move `√`/`Derivative`
out of `Later/` into `Residual/`. That deletes ~90 lines and one of the two proofs.

### 1.6 Lemmas that exist twice under different names — SEVERITY: MEDIUM

| A | B | note |
|---|---|---|
| `HLevels.agda:46` `TheorySet ℓA s = Σ[ A ∈ TheoryTy ℓA s ] isSetTheoryTy A` | `Category.agda:23` `SetTheoryTy ℓA s = Σ[ A ∈ TheoryTy ℓA s ] isSetTheoryTy A` | identical; `Category.agda:18` *imports* `HLevels` |
| `HLevels.agda:83` `_&Set_` | `Later/Indexed.agda:201` `_&Set_` | same name, different (indexed) type, sibling modules |
| `Operation/Base.agda:36` `isPropValEq` | `HLevels.agda:121` `isPropModelEq` | byte-identical bodies, both `private` |
| `Unambiguity/Base.agda:59` `unambiguousRetract` | `Unambiguity/Disjoint.agda:106` `isUnambiguousRetract'` | `:108` is literally `isUnambiguousRetract' f g r uB = unambiguousRetract f g r uB` |
| `Product/Binary/Base.agda:59` `&≡` | `Product/Binary/Base.agda:64` `&-η'` | same statement, two proofs, 5 lines apart |
| `Code/Container.agda:42,45,54,62` `Ix`/`Sh`/`Pos`/`nx` | `Inductive/HLevels.agda:59,65,68,77` `Ix`/`FS`/`FP`/`next` | the container encoding of `Functor`, written twice |
| `Cover/Base.agda:30` `Point A = ⊤Ty ⊢ A` | `Later/Indexed.agda:156` `Point = ∀ x → ⊤Ty ⊢ A x` | same name, different arity |
| `Guarded/Base.agda:28` `Pt` | `Later/Indexed.agda:57` `IPt` | same definition `Σ[ x ∈ X ] ↓M (xs x)`, two names |

**Fix.** Delete `SetTheoryTy` in favour of `TheorySet` (or vice versa, but pick one);
delete `&-η'`, `isUnambiguousRetract'`, `isPropModelEq`; make `Later/Indexed` reuse
`Cover`'s `Point` and `Guarded`'s `Pt`; delete `Code/Container.agda` (see §5).

---

## 2. Where the core escapes to the external model

### 2.1 Load-bearing axiomatisation (correct, keep)

These bind `m : ↓M s` or `ms : interpIn o ↓M` because that is *what the connective is*:

- `src/Theory/Base.agda:34` `TheoryTy ℓA s = ↓M s → Type ℓA` — the whole DSL is
  predicates on the carrier.
- `src/Theory/Base.agda:83` `⌈ a ⌉ m = m Eq.≡ a` — the representable.
- `src/Theory/Type/Operation/Base.agda:59-61` — `⊗` is defined by an existential over
  splittings `Σ[ ms ∈ interpIn o ↓M ] (op o ms Eq.≡ m) × Elems …`.
- `src/Theory/Type/Residual/Base.agda:192-196` and `:203-209` — `Resid`/`FocusedOperation`
  quantify over hole-contexts of carrier values.
- `src/Theory/Type/Later/Derivative.agda:28,31` — `Derivative f B m = B (f m)`, `√`.
- `src/Theory/Type/Code/Base.agda`, `Inductive/HLevels.agda` — the container encoding, and
  `isSetμ` which must talk about `↓M` to index the `IW` tree.
- `src/Theory/Type/Guarded/Base.agda:28` `Pt`, `Later/Indexed.agda:57` `IPt` — the
  well-founded order is on (index, carrier) pairs, necessarily.
- `src/Theory/Type/Equivalence/Base.agda:113,126` `isMono→injective`/`injective→isMono` —
  explicitly the bridge lemma, with a good comment at `:105-107` explaining that `yoIso`
  is what makes it cheap.

### 2.2 Escapes that leak into the client-facing API — SEVERITY: MEDIUM-HIGH

**(a) The whole `Decidable` consumption API is pointwise.**
`src/Theory/Type/Decidable/Base.agda:46-50`

```agda
DecAt : ∀ {s} → TheoryTy ℓA s → ↓M s → Type ℓA
at : ∀ {s} {A : TheoryTy ℓA s} → Decidable A → ∀ m → DecAt A m
```

and `:65` `module _ {s} {A : TheoryTy ℓA s} {m : ↓M s} where` containing `fromDec`,
`isNo`, `theNo`, `isYes`, `theYes`, `yesFrom` — six functions all taking a bare `m`.
Worse, `:176-190` `record PointwiseDecidableFormers` makes the escape *part of an
interface a client must implement*:

```agda
    dec⊗ᵘ-at : ∀ (o : σ .ops) {ℓA} {A : interpIn o (TheoryTy ℓA)} (m : ↓M (σ .resultSort o))
      → (∀ (ms : interpIn o ↓M) (e : op o ms Eq.≡ m) (a : arities σ o) → DecAt (A a) (ms a))
      → DecAt (⊗ᵘ[ o ] A) m
```

`DecidableFormers` immediately above (`:162-174`) states the *same three closure
properties* in `⊢`-form. So there is a clean version and a leaky version side by side,
with no comment saying when to use which (the leaky one presumably exists because the
`⊢`-version does not compute — that reason belongs in a comment).

**Fix.** Keep `PointwiseDecidableFormers` but mark it `private`-ish with a comment naming
the computational reason, and expose only `DecidableFormers` plus a
`decidable-fromPointwise` conversion. `isYes`/`theYes` etc. can be phrased as
`DecTy A ⊢ Δ Bool` and `DecTy A & Δ' ⊢ A` once `Δ` has an API (§1.2).

**(b) The Löb interface's `app` field.** `Guarded/Base.agda:42` — see §1.4. This is the
one field of an otherwise-clean `Typeω` record that hands the client `m` and `m'`.

**(c) `Residual/Base.agda` exports twelve model-level helpers publicly.**
`HoleVals:43`, `fillVals:49`, `fillVals-at:57`, `removeVals:64`, `fill-removeVals:70`,
`remove-fillVals:81`, `focusedValsIso:91`, `HoleElems:101`, `fillElems:111`,
`removeElems:120`, `fill-remove:128`, `elem-fill:139`, `remove-fill:148`,
`focusedElemsIso:158` — none is `private`, all are pure plumbing on `interpIn o ↓M`.
They then leak further: `Later/Derivative.agda:67,70,73,76,79,82` and
`HLevels.agda:113-118` all mention `HoleVals`/`fillVals` in *their own* signatures, so a
client writing a `√At` has to construct a `HoleVals` by hand.

**Fix.** Make everything from `HoleVals` through `focusedElemsIso` `private`, and expose
a single opaque `Hole o i` record with `fill`/`focus` and the iso. `√At`/`DerivativeAt`
then take a `Hole`.

**(d) `semact-map` escapes for no reason.**
`src/Theory/Type/SemanticAction/Base.agda:71`

```agda
semact-map f x m p = f (x m p .fst) , tt
```

This is `mapFst⊕ᴰ f (λ _ → id⊢) ∘⊢ x`, or equivalently
`⊕ᴰ-elim (λ v → σ⊕ (f v)) ∘⊢ x` — both already in `Sum/Base.agda`. Same file `:122`

```agda
Δ-⊗ o X m (ms , e , xs) = (λ a → xs a .fst) , tt
```

projects the `⊗` triple by hand rather than going through `⊗ᵘ-elim`/`⊗-overSplit`.
(The projection *is* the right choice for performance — `Operation/Base.agda:126-134`
explains why — but it should be `⊗-overSplit`, not a raw pattern.)
`run`/`observe` (`:58,:61`) are the legitimate extraction boundary and are fine.

**(e) External `List` in the core.** `src/Theory/Type/SemanticAction/Base.agda:15-16`
imports `Cubical.Data.List`, used only by `module Suite` (`:34-50`) — see §4.4.
`Later/Tabulated.agda:28` imports `List` for the memo table, which is legitimate
(the table is a metalanguage object, not a type of the theory).

No `String`, `Char`, or `Data.Nat`-as-payload anywhere in the core. That part is clean.

### 2.3 The `Eq.≡` decision has no comment anywhere — SEVERITY: MEDIUM (comments)

`src/Theory/Base.agda:83-84`

```agda
⌈_⌉ : ∀ {s} → ↓M s → TheoryTy ℓM s
⌈ a ⌉ m = m Eq.≡ a
```

The choice of `Cubical.Data.Equality`'s strict `Eq.≡` over the path type is *the* design
decision of this DSL: it is what makes `⊗-elim` (`Operation/Base.agda:124`),
`⊗ᵘ-elim` (`:109`), `unVar` (`:265`), `focused-⊸-intro⁻` (`Residual/Base.agda:248`),
`√-intro⁻` (`Later/Derivative.agda:42`), `Disjoint` (`Cover/Base.agda:34`) and
`DiscreteEq` (`Decidable/Route.agda:44`) *compute by matching `Eq.refl`*. There is no
comment stating this at the definition, at `Operation/Base.agda:56-61` where it
propagates, or in `Free/Base.agda:36-39` where the presentation is forced to carry a
`satStrict` in `Eq` alongside the model's path-valued equations. The only nearby comment
is `Operation/Base.agda:126-134`, which explains when matching it is *catastrophic* —
so the reader learns the drawback before the reason.

`src/Theory/Free/Base.agda:36` has the comment `-- equations but with Eq`, which restates
the code and explains nothing.

**Fix.** A five-line note at `Theory/Base.agda:82`: representables are `Eq.≡` so that
a splitting proof is a canonical `Eq.refl` on canonical input, which is what lets the
elimination forms reduce; the model is a set, so `Eq.≡` and `_≡_` are equivalent and
`isPropValEq` recovers everything the path type would give. Then delete the
`-- equations but with Eq` line.

---

## 3. `Cubical/Algebra/Theory/Finitary/Free/ClosingElim.agda`

**The file changed at 13:45 today and now contains exactly the general eliminator the
maintainer asked about.** The signature there is right; I reproduce it and confirm each
method, then list what is still missing.

### 3.1 The HIT's constructors

`src/Cubical/Algebra/Theory/Finitary/Free/Closing.agda:33-53`: four points
(`var`, `node`, `clo`, plus the indexed-`Tm` argument to `clo`), three paths
(`cloVar`, `cloNode`, `eqn`), and `trunc : {s : S} → isSet (FreeModel V vs s)`.

### 3.2 The eliminator (as now written, `ClosingElim.agda:28-64`) — correct

```agda
module _ {S : Type ℓS} {σ : SortedSig S ℓ} (σeq : SortedEqns σ ℓ'')
  {V : Type ℓv} {vs : V → S} where

  private
    Free : S → Type _
    Free = FreeModel σeq V vs

    Subst : σeq .eqns → Type _
    Subst e = (w : vars σeq e) → Free (σeq .varSort e w)

  module _
    {P : {s : S} → Free s → Type ℓP}
    (isSetP : {s : S} (m : Free s) → isSet (P m))
    (pvar : (v : V) → P (var v))
    (pnode : (o : σ .ops) (f : (a : arities σ o) → Free (σ .sortOf o a))
      → ((a : arities σ o) → P (f a)) → P (node o f))
    (pclo : (e : σeq .eqns) {s : S}
        (t : Tm σ (vars σeq e) (σeq .varSort e) s) (ρ : Subst e)
      → ((w : vars σeq e) → P (ρ w)) → P (clo e t ρ))
    (pcloVar : (e : σeq .eqns) (w : vars σeq e) (ρ : Subst e)
        (pρ : (w' : vars σeq e) → P (ρ w'))
      → PathP (λ i → P (cloVar e w ρ i)) (pclo e (var w) ρ pρ) (pρ w))
    (pcloNode : (e : σeq .eqns) (o : σ .ops)
        (ts : (a : arities σ o) → Tm σ (vars σeq e) (σeq .varSort e) (σ .sortOf o a))
        (ρ : Subst e) (pρ : (w : vars σeq e) → P (ρ w))
      → PathP (λ i → P (cloNode e o ts ρ i))
          (pclo e (node o ts) ρ pρ)
          (pnode o (λ a → clo e (ts a) ρ) (λ a → pclo e (ts a) ρ pρ)))
    (peqn : (e : σeq .eqns) (ρ : Subst e) (pρ : (w : vars σeq e) → P (ρ w))
      → PathP (λ i → P (eqn e ρ i))
          (pclo e (σeq .lhs e) ρ pρ) (pclo e (σeq .rhs e) ρ pρ))
    where

    elim : {s : S} (m : Free s) → P m
```

Obligation per method:

- `isSetP` — **unavoidable**. `trunc` is a point-level set-truncation, so the motive must
  be fibrewise a set; there is no weaker hypothesis. (The 2-groupoid-valued variant would
  need `trunc` to be a groupoid-truncation, which it is not.)
- `pvar` — the value at a generator.
- `pnode` — the value at an operation node, given the values at the arguments. This is the
  algebra structure, dependently.
- `pclo` — the value at a *closed-up term* `clo e t ρ`: given a term `t` in the equation
  `e`'s variables and values for the substitution `ρ`, produce the value at the whole
  closure. Note the `{s : S}` here: `clo` is the one point constructor whose result sort
  is not determined by the constructor's other data, so the method must be sort-polymorphic.
- `pcloVar` — `clo e (var w) ρ ≡ ρ w` must be respected: the closure of a variable is the
  substituted value. Obligation is a `PathP` over that identification from `pclo`'s answer
  at `var w` to `pρ w`.
- `pcloNode` — `clo e (node o ts) ρ ≡ node o (λ a → clo e (ts a) ρ)`: closing distributes
  over operations. Obligation is a `PathP` from `pclo` at the node to `pnode` applied to
  the componentwise closures — i.e. *`pclo` and `pnode` must agree on a node*.
- `peqn` — the equation itself: `pclo`'s answers on `lhs e` and `rhs e` must be identified
  over the path `eqn e ρ`. This is the only method that says anything about the theory's
  axioms.

The `trunc` clause (`:61-64`) is filled with
`isSet→SquareP (λ i j → isSetP (trunc x y p q i j)) (λ k → elim (p k)) (λ k → elim (q k)) (λ _ → elim x) (λ _ → elim y) i j`,
which is correct: `trunc x y p q i j` restricts to `p j`/`q j` at `i = i0/i1` and to
`x`/`y` at `j = i0/i1`, matching `isSet→SquareP`'s `a₀₋ a₁₋ a₋₀ a₋₁` order
(`Cubical/Foundations/HLevels.agda:314-320`). Equivalently
`isOfHLevel→isOfHLevelDep 2 isSetP (elim x) (elim y) (cong elim p) (cong elim q) (trunc x y p q) i j`.

**Constructibility: yes, no awkwardness.** The indexed-match warning is already suppressed
by the file's `{-# OPTIONS -WnoUnsupportedIndexedMatch #-}` (the same one `Closing.agda`'s
`rec`/`recUniq` need). No constructor forces anything beyond `isSetP`.

### 3.3 What is still missing — SEVERITY: HIGH

**(a) `rec` and `recUniq` in `Closing.agda` are still independent hand-rolled recursions.**
`src/Cubical/Algebra/Theory/Finitary/Free/Closing.agda:88-100` (`rec`, 7 clauses) and
`:157-201` (`recUniq`, 7 clauses with `isProp→PathP`/`isProp→SquareP` boilerplate).
The maintainer's "one eliminator and two corollaries" should be *three* corollaries.

`rec` from `elim` at the constant motive `P {s} _ = X s` (so every `PathP` degenerates to
a path in `X s`):

```agda
    rec : {V : Type ℓv} {vs : V → S} (ρ : (v : V) → X (vs v)) {s : S} → FreeModel V vs s → X s
    rec ρ = elim σeq
      (λ {s} _ → isSetX s)                       -- ptrunc
      ρ                                          -- pvar
      (λ o _ ih → α o ih)                        -- pnode
      (λ e t _ pρ → TmRec X α pρ t)              -- pclo
      (λ e w _ pρ → refl)                        -- pcloVar : TmRec α pρ (var w) ≡ pρ w, definitional
      (λ e o ts _ pρ → refl)                     -- pcloNode : TmRec α pρ (node o ts) ≡ α o (…), definitional
      (λ e _ pρ → sat e pρ)                      -- peqn : exactly the model's equation
```

Both path methods are `refl` because `TmRec` (`Finitary.agda:38-41`) computes on `var` and
`node`; `peqn` is literally the `sat` hypothesis. The derived `rec` agrees clause-for-clause
with the existing one (`Closing.agda:94` `rec ρ (cloVar e w ρ' i) = rec ρ (ρ' w)` is the
constant path that `refl` supplies), so `recβ:102` and `Theory/Free/Closing.agda:24-25`'s
`refl`s survive.

`recUniq` from the *prop*-eliminator, at the motive `P m = f _ m ≡ rec ρ m` — which is a
prop because `X` is a set:

```agda
        recUniq = elimProp σeq (λ {s} m → isSetX s (f s m) (rec ρ m))
                    fβ uniqNode (λ e ρ' ih t → uniqClo e ρ' ih t)
```

That deletes `Closing.agda:180-201` entirely (the four `isProp→PathP`/`isProp→SquareP`
cases), about 22 lines.

**(b) `FreePresentation` has no `elim` field, so the eliminator is unreachable from
`Theory.Base`.** `src/Theory/Free/Base.agda:43-64` gives a presentation `rec`, `recGen`,
`recOp`, `recUniq` — and nothing dependent. Consequence: `elimProp` is used at exactly one
site in the whole repo (`src/Theory/Instances/Bags/Order.agda:143,163`), and that site has
to import `Cubical.Algebra.Theory.Finitary.Free.ClosingElim` directly, bypassing the
presentation abstraction. Every other instance (`ListPresentation`, `termPresentation`)
therefore *cannot* do induction over its carrier at all.

**Fix.** Add to `FreePresentation`:

```agda
    elimProp : ∀ {ℓP} {P : {s : S} → Carrier s → Type ℓP}
      → ({s : S} (m : Carrier s) → isProp (P m))
      → ((v : V) → P (gen v))
      → ((o : σ .ops) (ms : (a : arities σ o) → Carrier (σ .sortOf o a))
          → ((a : arities σ o) → P (ms a)) → P (op o ms))
      → {s : S} (m : Carrier s) → P m
```

`closingPresentation` fills it from `ClosingElim.elimProp` (`pclo` is derived by
induction on the `Tm` using `cloTmRec`, `Closing.agda:64`); `termPresentation` fills it
from `elimTerm` (`Theory/Free/Term.agda:120`), which already exists and is otherwise
unused outside its file; `listPresentation` fills it with `List` induction. Then
`Theory.Base` can export a single `elimProp` and instances stop importing `ClosingElim`.

**(c) The file lost its top-of-file explanation.** `git show HEAD:…ClosingElim.agda`
carried a good four-line note about why the eliminator is needed (dependent statements
about folds previously required transporting along `recUniq`, and that transport is
opaque). The new version's inline comments at `:24-27` and `:66-67` are good, but the
"why does this module exist" paragraph is worth keeping.

---

## 4. Modularity

### 4.1 `Theory/Type/HLevels.agda` is a grab-bag with maximal fan-in — SEVERITY: MEDIUM

`src/Theory/Type/HLevels.agda:26-39` imports **thirteen** connective modules in order to
state one `isSetX` lemma per connective (`:55-161`). It additionally holds a second,
unrelated API (`TheorySet:46`, `ty:49`, `isSetTy:52`, `_&Set_:83`, `&ᴰSet:86`,
`⊕ᴰSet:89`, `_⊕Set_:93`) and one lemma with nothing to do with the DSL at all:

```agda
-- a proposition at one end of a line of types fills the whole line
isPropPathP : ∀ {ℓ} (T : I → Type ℓ) → isProp (T i0) → (x : T i0) (y : T i1) → PathP T x y
```
`src/Theory/Type/HLevels.agda:163-167` — pure `Cubical.Foundations` material, and used in
6 files.

**Fix.** (i) Move each `isSetX` into its connective's own module (`isSet&` into
`Product/Binary/Base`, `isSet⊗` into `Operation/Base`, …), which is where a reader looks
for it and which removes the 13-way fan-in. (ii) Keep `HLevels.agda` for
`isSetTheoryTy`/`TheorySet`/`&Set` only. (iii) Push `isPropPathP` upstream into
`Cubical.Foundations.HLevels` or `Cubical.Foundations.Path`.

### 4.2 Two connective "Base" modules depend on `μ` — SEVERITY: MEDIUM

- `src/Theory/Type/Equalizer/Base.agda:20` `open import Theory.Type.Inductive.Base` — used
  only by `equalizer-ind` (`:54-85`); lines `24-52` (the equalizer itself, `eq-π`,
  `eq-intro`, `eq-β`, `equalizer-section`) need nothing.
- `src/Theory/Type/Subgrammar/Base.agda:28` — same shape: lines `34-105` (the classifier
  and the subobject) need nothing; only `subgrammar-ind` (`:109-131`) needs `μ`.

Result: `Inductive/Base` (which is the module with the `TERMINATING` pragmas and
`--lossy-unification`) is a transitive dependency of anything that wants an equalizer or a
subobject, including `PropositionalTruncation/Base` and `Monad/NonDet`.

**Fix.** Split `Equalizer/Induction.agda` and `Subgrammar/Induction.agda` off.

### 4.3 `≅` composition is private to `Theory.Base`, and the workaround is in the tree

`src/Theory/Base.agda:72-73`

```agda
private
  module THEORYTY {s} = WildCatNotation (THEORYTY s)
```

`src/Theory/Type/Equivalence/Base.agda:131-132` documents the consequence:

```agda
-- Composition and inversion of `≅`.  `THEORYTY`'s `⋆WildCatIso` does this
-- too, but that module is private to `Theory.Base`.
```

and then re-derives `_≅∙_`, `sym≅`, `id≅` (`:135-155`). **Fix.** Drop the `private`, or
export `THEORYTY.⋆WildCatIso`/`invWildCatIso` from `Theory.Base` and delete `:135-155`.

### 4.4 A test harness is exported from a core connective module — SEVERITY: MEDIUM

`src/Theory/Type/SemanticAction/Base.agda:34-50`

```agda
module Suite where
  Case : Type ℓX → Type ℓX
  _↦_ : {W : Type ℓY} {X : Type ℓX} → W → X → W × X
  passes : {X : Type ℓX} → List (Case X) → Type ℓX
  _at_ : {W : Type ℓY} {X : Type ℓX} → (W → X) → List (W × X) → List (Case X)
open Suite public
```

This is a golden-test DSL (`f at [ input ↦ expected , … ]`, `passes`), it is the sole
reason `Cubical.Data.List` is imported into the core (`:15-16`), and its `_at_` collides
with `Decidable/Base.agda:49`'s `at` — see the `hiding (at)` and its comment at
`Theory/Instances/Monoid/Types.agda:42-44`.

**Fix.** Move `module Suite` to `src/Theory/Test/Suite.agda` (or
`Theory/Instances/Monoid/TestSuite.agda`), drop the `open … public`, drop the `List`
import from the core, and the `hiding (at)` disappears.

### 4.5 There are no aggregator modules — SEVERITY: LOW-MEDIUM

The old `src/Grammar/**` tree has `Grammar/Top.agda` re-exporting `Top/Base` + `Top/Properties`,
and so on for every connective, plus `src/Grammar.agda`. `src/Theory/Type/**` has *none* —
no `Theory/Type/Top.agda`, no `Theory/Type.agda`, no `Theory.agda`. Every client must
repeat the four module arguments per connective:
`src/Theory/Instances/Monoid/Strings.agda` has 18 such imports;
`src/Theory/Instances/Monoid/Types.agda:33-44` is an ad-hoc aggregator written in the
*instance* layer rather than in the core.

**Fix.** Add `Theory/Type/<Connective>.agda` re-export modules and a
`Theory/Type/Core.agda` that opens the whole connective API in one go, parameterised the
same way. The instance layer then instantiates once.

### 4.6 Module-parameter and generalisation conventions differ between siblings

`Product/Binary/Base.agda:24-31`, `Sum/Binary/Base.agda:25-32`, `Function/Base.agda:19-25`,
`Unambiguity/Disjoint.agda:35-42` declare
`private variable … s : S ; A : TheoryTy ℓA s ; …` and state lemmas with generalisation.
`Product/Base.agda:23`, `Sum/Base.agda:20`, `Top/Base.agda:20`, `Bottom/Base.agda:20`,
`Lift/Base.agda:18-20` declare only levels and open explicit `module _ {s} {Y} {A}` blocks.
The consequence is visible in the API: `&-intro : A ⊢ B → A ⊢ C → A ⊢ B & C` vs
`&ᴰ-intro : (∀ y → A ⊢ B y) → A ⊢ &[ y ∈ Y ] B y` inside a `module _ {s : S} {Y : Type ℓY} {A} {B}`,
so implicit-argument shapes differ between the indexed and binary forms of the same
connective. **Fix.** Pick the `private variable` style (it is the majority and the
shorter one) and apply it in the six `Base` modules that do not use it.

---

## 5. Dead code, pragmas, `TERMINATING`

No `postulate`, no `trustMe`, no `--no-positivity`, no `--type-in-type`, no `REWRITE`,
no commented-out code blocks anywhere in scope. Good.

### 5.1 Four `{-# TERMINATING #-}`, two of them on proofs — SEVERITY: HIGH

| site | on | comment at site? |
|---|---|---|
| `src/Theory/Type/Inductive/Base.agda:41` | `rec` | no |
| `src/Theory/Type/Inductive/Base.agda:51` | `μ-η'` (**a proof**) | no |
| `src/Theory/Type/Coinductive/Base.agda:44` | `corecHomo` | no |
| `src/Theory/Type/Coinductive/Base.agda:54` | `ν-η'` (**a proof**) | no |
| `src/Theory/Type/Inductive/HLevels.agda:154` | `encode` | no |
| `src/Theory/Type/Inductive/HLevels.agda:169` | `isRetract` (**a proof**, inside `opaque`) | no |

Six, not four. The two `-η'` ones and `isRetract` are *proofs*: an asserted-terminating
proof is not a proof, and `μ-η'` is what `ind`, `ind-id`, `equalizer-ind`,
`subgrammar-ind` and hence every induction principle in the DSL rest on.

There is one explanation in the tree, at a distance —
`src/Theory/Type/Guarded/Base.agda:80-84`:

> ``Inductive/Base``'s `rec` needs `TERMINATING` because its descent runs through
> `map (F x)`, which Agda cannot see into; here the descent is `löb`, which is a term,
> so nothing is asserted.

**Fix (ranked).** (i) At minimum, put that paragraph, and a note that `μ-η'`/`ν-η'`/`isRetract`
are asserted, at each of the six sites. (ii) `Inductive/HLevels.agda` already builds the
`IW` encoding — `encode`/`decode`/`isRetract` should be structurally recursive on the `IW`
side, or `μ` should simply *be* `μIW` (`:86`) with `roll`/`unroll` derived, which removes
`Inductive/Base`'s two pragmas and `Inductive/HLevels`' two at once. (iii) `Guarded/Base`'s
`fold`/`fold-unfold` (`:85-97`) is the pragma-free `rec`; if every client can be moved onto
it, `Inductive/Base.rec` can go.

### 5.2 Definitively dead (only their own file mentions them)

- `src/Theory/Type/Reify/Base.agda` — **the entire module**. `Reify` is defined at `:25`
  and no file imports `Theory.Type.Reify`. (The old `src/Grammar/Reify/` is its ancestor.)
- `src/Theory/Type/Code/Container.agda` — file header is literally
  `-- TODO is this actually used?` (`:1`). Only `Split`/`parts` (`:29,:32`) are used, by
  `Guarded/Justification.agda:32`. `Ix:42`, `Sh:45`, `Pos:54`, `nx:62` are dead *and*
  duplicate `Inductive/HLevels.agda:59,65,68,77`. **Fix.** Move `Split`/`parts` into
  `Operation/Base.agda` and delete the file.
- `src/Theory/Type/Coinductive/Base.agda` — the whole `ν` connective. Its only importer is
  `Top/Properties.agda:27`, for `⊤≅ν` (`:115`), which is itself unused. So two
  `TERMINATING` pragmas are being carried for dead code. Same for `⊤≅μ` (`Top/Properties.agda:81`).
- `src/Theory/Type/Inductive/Base.agda:95` `unroll'` (a `rec`-based duplicate of
  `unroll:86`); `src/Theory/Type/Coinductive/Base.agda:89` `roll-ν`.
- `src/Theory/Type/Cover/Base.agda:55-77` — `Covering`, `ofCover`, `Cases` (three records
  and a constructor, all unused) and `trivialCover:51`.
- `src/Theory/Type/Distributivity.agda:50` `⊗&ᴰ-dist` — unused.
- `src/Theory/Type/Representable/Base.agda:32` `precompIso` — unused.
- `src/Theory/Type/Monad/Cont.agda:33,37` `callCC`, `abort` — unused.
- `src/Theory/Type/Operation/Base.agda:262` `unVar`, `:250` `⊗⌈⌉Iso`, `:63-74`
  `same-inputs`/`same-elements` (only `⊗PathP` uses them, internally).
- `src/Theory/Type/Residual/Base.agda:238,245,250,255,293` `focused-⊸-intro`,
  `focused-⊸-intro⁻`, `focused-⊸-η`, `focused-⊸-β`, `⊸Iso` — the "focused" layer is
  entirely internal to deriving `⊸-β`/`⊸-η`; make it `private`.
- `src/Theory/Type/Later/Derivative.agda:58` `√Iso`, `:44` `√-β` — unused outside.
- `src/Theory/Type/Equivalence/Base.agda:47` `id≈`, `:84` `isMonoId`, `:87` `Mono∘⊢`,
  `:74` `≅→isRetractOf` — unused.
- `src/Theory/Type/Coinductive/Base.agda:65` `coind'`;
  `src/Theory/Type/Decidable/Base.agda:117,126` `dec-retract-id`, `dec-retract-∘`;
  `:205` `coverDecidable`; `Unambiguity/Disjoint.agda:87` `Δsection→unambiguous`.

That is roughly 400 lines. **Fix.** Delete `Reify/Base.agda` and `Code/Container.agda`;
`private` the focused-residual layer and `Residual`'s hole plumbing; decide whether `ν` is
wanted (if yes, use it and comment the pragmas; if no, delete it and `⊤≅ν`).

### 5.3 Six files carry a "TODO how much of this is actually used?" header

`Later/Poset.agda:1-5`, `Later/Lex.agda:1-5`, `Later/Derivative.agda:1-5`,
`Later/Indexed.agda:1-5`, `Later/Tabulated.agda:1-5` carry the *identical* five lines:

```
-- TODO how much of this actually used?
-- WARNING for now I have been treating this as a place to sequester the
-- semantic reasoning about guarded recursion so that importers of this
-- module can work with a clean interface
-- The implementation are subject to change per experiments w Cass
```

plus `Guarded/Justification.agda:2`, `Decidable/Base.agda:1`, `Monad/Base.agda:1`,
`Code/Container.agda:1`.

Answer from the tree: `Later/Poset`, `Later/Lex`, `Later/Indexed`, `Later/Tabulated`,
`Guarded/Justification`, `Decidable/Base`, `Decidable/Route` are all live (used by
`Instances/Monoid/Suffix`, `Automaton/SuffixChain`, `Bags/Rank`, `Combinator/Core`,
`Combinator/Decidable/Bracket`). `Monad/Cont` is used only by `HLevels.agda`;
`Monad/NonDet` only by `Combinator/NonDet/Base`. `Code/Container` is 5/7 dead.

**Fix.** Delete the five copied headers, replace with one sentence per file saying what
that file provides (`Poset`: the direct structure on a well-founded order; `Lex`: the
lexicographic product; `Indexed`: `▷` from a well-founded order on `IPt`; `Tabulated`:
the memoised `▷`), and keep the "subject to change per experiments w Cass" note in one
place — `Later/Indexed.agda`, the interface everything else goes through. Grammar:
"The implementation are subject to change" → "The implementations are".

---

## 6. Naming

### 6.1 Meaningless names

- `src/Theory/Type/Guarded/Justification.agda:209` `st`, `:218` `hy`, `:226` `hy-unfold`,
  `:259` `go`, `:266` `go-irr`, `:284` `unf`, `:293` `uniqAux`. Suggested: `stepAlg`,
  `hyloOf`, `hyloOf-unfold`, `descend`, `descend-fuel-irrelevant`, `descend-unfold`,
  `descend-uniq`.
- `src/Theory/Type/Decidable/Base.agda:121` `go` and `:132` `go` (two different `where`-bound
  `go`s in adjacent lemmas, both `(m : ↓M _) (z : DecAt A m) → …`). Suggested: `onDec`.
- `src/Theory/Type/Monad/NonDet.agda:127` `q`, `:149` `p₂` (both are `eq-π …`; call them
  `π-eq`), `:50` `cons` (unqualified, while every sibling is `nilND`/`consND`/`ηND`/`bindND`
  — call it `consWith`).
- `src/Theory/Type/Later/Tabulated.agda:197` `key`, `:203` `bridge`; `:143` `buildView`
  is fine.
- `src/Theory/Type/Product/Binary/Base.agda:97,100,103,106` `the-fun`/`the-inv`/`the-sec`/
  `the-ret`, repeated verbatim in `Sum/Binary/Base.agda:87,90,93,96` and `:120,:123` and
  `Subgrammar/Base.agda:87` `the-path`. Harmless but it is a tic across six sites.

### 6.2 Primed variants used as a convention

`ind'` (`Inductive/Base.agda:62`), `coind'` (`Coinductive/Base.agda:65`),
`ind-id'` (`:69`), `coind-id'` (`:72`), `unroll'` (`:95`), `μ-η'` (`:52`), `ν-η'` (`:55`),
`&-η'` (`Product/Binary/Base.agda:64`), `isUnambiguousRetract'` (`Unambiguity/Disjoint.agda:106`),
`unambiguousRetract'→≅` (`:123`), `subgrammar-ind'` (`Subgrammar/Base.agda:121`),
`eq-π-pf'` (`Subgrammar/Equalizer.agda:43`), `semact-⊕ᴰ'` (`SemanticAction/Base.agda:101`),
`witness∃'` (`PropositionalTruncation/Base.agda:81`).

The prime means five different things across these: "pointwise version" (`ind'`),
"unpackaged-arguments version" (`isUnambiguousRetract'`), "the intermediate step"
(`subgrammar-ind'`), "the non-dependent version" (`semact-⊕ᴰ'`), and "a duplicate"
(`&-η'`, `unroll'`). **Fix.** Use suffixes that say which: `-at`, `-fun`, `-alg`, `-const`;
delete the two duplicates.

### 6.3 Stale "Grammar" vocabulary — SEVERITY: MEDIUM

44 hits of `grammar` in the core, and they are *all* the subobject connective:

- `src/Theory/Type/Subgrammar/Base.agda` — module `Theory.Type.Subgrammar.Base`,
  `module Subgrammar:53`, `subgrammar:54`, `subgrammar-section:96`, `subgrammar-ind:129`,
  `subgrammar-ind-alg:116`, `subgrammar-ind':121`, `mono→subgrammar:151`,
  `unambiguous→subgrammar:162`
- `src/Theory/Type/Subgrammar/Equalizer.agda:40` `equalizer≡subgrammar`
- `src/Theory/Type/PropositionalTruncation/Base.agda:68` `module ∃Subgrammar`,
  `:72` `∃subgrammar`

Everything else in the tree says `Ty`/`TheoryTy`/`theory type`. The migration is complete
except for this one connective. Two other residues:
`src/Theory/Base.agda:62` `-- used for Grammars` and
`src/Theory/Type/Equivalence/Base.agda:105` "The old grammar development had to…" (that
one is a legitimate historical note; keep it).

**Fix.** Rename `Theory/Type/Subgrammar/` → `Theory/Type/Sub/`, `subgrammar` → `subTy`,
`Subgrammar` → `SubTy`, `∃Subgrammar` → `∃SubTy`. Note `sub-π`/`sub-intro`/`sub-β`/`sub-η`
are already migrated, so only the former's name is stale.

### 6.4 Instance vocabulary in the generic core

`src/Theory/Type/Later/Tag.agda:9`

```agda
data ParserTag : Type where
  ⟨▷⟩ ⟨□⟩ : ParserTag
```

with a header saying "A parser is indexed by one of these". Nothing about `▷`/`□` is
parser-specific; this is the "available now / available later" modality tag of a guarded
type. `▷?`, `▷?wk`, `▷?map`, `▷?lax`, `▷?next`, `▷?laxᴰ` in `Later/Indexed.agda:249-283`
are all indexed by it. **Fix.** `ParserTag` → `ModalityTag` (or `Availability`), and
reword the header.

---

## 7. Comments

The comment quality in this tree is **good** — there is essentially no LLM slop, no
top-of-file essay, no line-by-line narration. Concretely good examples worth preserving:
`Operation/Base.agda:126-134` (the measured cost of matching a splitting),
`Residual/Base.agda:1-7` (an honest "this is not definitionally nice, a manual definition
per theory may be better"), `Guarded/Base.agda:80-84` (why `löb` needs no pragma),
`Later/Tabulated.agda:88-90` (why the chain view makes the memo table shareable),
`Subgrammar/Base.agda:90-91` (why `sub-η` is on the nose).

### 7.1 Non-obvious mathematics with no comment — SEVERITY: MEDIUM

1. **Why `Eq.≡` and not `_≡_`** — see §2.3. This is the highest-value missing comment in
   the tree.
2. **`Operation/Base.agda:218-235` `eqn→Iso`.** The header line ("Equations of the theory
   lift to isos of the convolutional liftings") states *what*; the actual content is that
   the `sec`/`ret` go through only because the `Eq`-component is a proposition
   (`isPropValEq`), i.e. because the model is a set — which is exactly why `MOD`'s objects
   are `hSet`-valued (`Finitary.agda:78`). One sentence.
3. **`Finitary.agda:88-94` `ALGᴰ`'s `Hom` has an odd shape**:
   `… (y : ⟨ X (σ .resultSort o) ⟩) → y ≡ α o x → f _ y ≡ β o (…)`. It carries a
   redundant `y` with a proof `y ≡ α o x` rather than being stated at `α o x` directly.
   That shape is what makes `recHomo` (`Closing.agda:104`) and `Theory/Free/Closing.agda:28`
   `cong (f _) eq ∙ homf o x` work, but nothing says so.
4. **`Finitary.agda:56-58`** `-- equations are finitary too: an equation has finitely many
   variables, which is what lets a convolution along a term carry a level per slot` — this
   *is* the right kind of comment and is the only one explaining the finitarity constraint.
   It should be echoed at `Operation/Base.agda:40-48` where `sup`/`Args` cash it out.
5. **The six `TERMINATING` sites** — §5.1.
6. **`Distributivity.agda:50`** — why no inverse; §1.3 item 9.

### 7.2 Comments that restate the code

- `src/Theory/Free/Base.agda:36` `-- equations but with Eq` — delete, replace with the
  reason (§2.3).
- `src/Theory/Type/Operation/Base.agda:92` `-- uniform levels`, `:176` `-- projecting a
  slot out of the tuples`, `:201` `-- Map an operation convolution with independently
  varying input levels.` — the last is fine; the first two restate the signature.
- `src/Theory/Type/Sum/Binary/Base.agda:48-49` "`&` distributes over `⊕` because both are
  computed pointwise" — true but it is the *definition* directly below; the useful comment
  would say why this is not in `Distributivity.agda`.

### 7.3 Stylistic tic: narrative continuation across definitions

`-- ...and its dual, the recursor` (`Guarded/Base.agda:80`),
`-- ...so truncating an unambiguous type does nothing` (`PropositionalTruncation/Base.agda:59`),
`-- ...and closed, which is what a top-level decision wants` (`Decidable/Route.agda:101`),
`-- ...and conversely, pointwise injectivity is monicity` (`Equivalence/Base.agda:125`),
`-- ...and so the equalizer is a subterminal-indexed choice` (`Subgrammar/Equalizer.agda:57`),
`-- ...with a value carried alongside` (`Operation/Base.agda:145`),
`-- ... and the order from a measure` (`Guarded/Justification.agda:93`).
Also `-- THE THEOREM, in context` (`Decidable/Route.agda:58`) and the scare-quoted
`-- "This system admits hylomorphisms, uniquely."` (`Guarded/Base.agda:53`).
Each is individually readable; nine of them across the core reads as one voice narrating
rather than as reference documentation. Low priority, but worth normalising if the core is
going to be the thing people read first.

---

## Appendix: ranked summary

| # | severity | finding | site |
|---|---|---|---|
| 1 | high | six `{-# TERMINATING #-}`, three on proofs, none commented at site | `Inductive/Base.agda:41,51`; `Coinductive/Base.agda:44,54`; `Inductive/HLevels.agda:154,169` |
| 2 | high | `Δ` names two connectives; four `hiding (Δ)` in clients | `Product/Base.agda:48` vs `SemanticAction/Base.agda:52` |
| 3 | high | `▷` has no `⊢`-level intro/elim; `Löb.app` is the one pointwise field | `Later/Indexed.agda:169,175`; `Guarded/Base.agda:42` |
| 4 | high | `FreePresentation` has no `elim`; the new eliminator is unreachable from `Theory.Base` | `Theory/Free/Base.agda:43-64` |
| 5 | high | `rec`/`recUniq` still independent of `elim` | `Closing.agda:88-100,157-201` |
| 6 | high | `⊗` — the primary connective — has no β, no η, no `≅` | `Operation/Base.agda:111-124` |
| 7 | med-high | `Decidable`'s consumption API is entirely pointwise, incl. a record field | `Decidable/Base.agda:46-88,176-190` |
| 8 | med-high | `Residual`'s 14 model-level helpers are public and leak into `√At`/`isSetResid` | `Residual/Base.agda:43-187` |
| 9 | med | `Lift` has no β/η/`≅`/map; `Code/Base` inlines them as `refl` | `Lift/Base.agda:25-29`; `Code/Base.agda:56,65,79` |
| 10 | med | the residual is stated twice (`Resid` and `√`) with two proofs | `Residual/Base.agda` vs `Later/Derivative.agda` |
| 11 | med | eight duplicate definitions under different names | table in §1.6 |
| 12 | med | `eq-β` and `eq-η` in different modules | `Equalizer/Base.agda:39` vs `Subgrammar/Equalizer.agda:53` |
| 13 | med | a test harness is `open … public`ed from the core, causing `hiding (at)` | `SemanticAction/Base.agda:34-50` |
| 14 | med | `HLevels.agda` grab-bag: 13-way fan-in, second API, one upstream lemma | `HLevels.agda:26-39,46-97,163-167` |
| 15 | med | stale `subgrammar` vocabulary — the only unmigrated connective | `Subgrammar/Base.agda` (44 hits) |
| 16 | med | ~400 lines dead: `Reify` (whole module), `ν`, 5/7 of `Code/Container`, `Covering`/`Cases`, … | §5.2 |
| 17 | med | why `Eq.≡` is used everywhere is nowhere written down | `Theory/Base.agda:83` |
| 18 | low-med | `Equalizer/Base` and `Subgrammar/Base` depend on `μ` for one lemma each | `Equalizer/Base.agda:20`; `Subgrammar/Base.agda:28` |
| 19 | low-med | `≅` composition private to `Theory.Base`, re-derived downstream | `Theory/Base.agda:72-73`; `Equivalence/Base.agda:131-155` |
| 20 | low-med | no aggregator modules; the instance layer is doing the core's job | `Theory/Instances/Monoid/Types.agda:33-44` |
| 21 | low | `⊗&ᴰ-dist` one-sided with no explanation | `Distributivity.agda:50` |
| 22 | low | `&ᴰ`/`⊕ᴰ` β missing; `⊕ᴰ≅` and `mapFst&ᴰ` missing; `&-assoc≅`, `id⊕_` missing | §1.3 |
| 23 | low | `⊤Ty↑` has no rules while `⊥Ty↑` does | `Top/Base.agda:25` |
| 24 | low | `go`/`hy`/`st`/`unf`/`uniqAux`/`q`/`p₂`/`cons`/`key`/`bridge` | §6.1 |
| 25 | low | primes mean five different things | §6.2 |
| 26 | low | five files share a copy-pasted TODO/WARNING header | `Later/{Poset,Lex,Derivative,Indexed,Tabulated}.agda:1-5` |
| 27 | low | `ParserTag` is instance vocabulary in the generic core | `Later/Tag.agda:9` |
