# Port status: `Grammar/` → `Theory/`

Companion to `theory-port-audit.md`.  **32 modules, 5,150 lines, all
typechecking with exit 0 — no holes, no postulates, no `TERMINATING`
pragmas.**  Verified against local `cubical` `92166033` and
`cubical-categorical-logic` `82334ff` (the flake pins), with

    agda --library-file=<cubical, ccl, src/grammar.agda-lib> <module>

## Landed — generic (`Theory/Type/`)

| module | lines | replaces |
|---|---|---|
| `Type/Equivalence/Base` | 155 | `Grammar/Equivalence/Base` residue: `_≈_`, `_isRetractOf_`, `isMono`, `isMono→injective`, `isMono→hasPropFibers`, `_≅∙_`, `sym≅`, `id≅` |
| `Type/Subgrammar/Base` | 163 | `Grammar/Subgrammar/Base`: `Ω`, `true`/`false`, `Subgrammar`, `subgrammar-ind`, `preimage`, `mono→subgrammar`, `unambiguous→subgrammar` |
| `Type/Subgrammar/Equalizer` | 61 | `Grammar/Subgrammar/Equalizer`: `eq-prop`, `eq-η`, `isMono-eq-π` |
| `Type/PropositionalTruncation/Base` | 86 | `Grammar/PropositionalTruncation/Base` in full |
| `Type/Unambiguity/Disjoint` | 140 | `Grammar/Properties/Base` residue: `disjoint` + lemmas, `π≡→unambiguous`, `Δ≅`, `≈→≅`, `&⊤≅` |
| `Type/Reify/Base` | 26 | `Grammar/Reify/Base` |
| `Type/Bottom/Base` | +7 | added `⊥Ty↑-elim` / `⊥Ty↑-η` |

## Landed — connective tier (`Theory/Instances/Monoid/`)

The last three files that bind a model element.  Everything downstream --
every automaton, every Thompson clause, the whole determinisation -- is DSL
composition; `grep`ing the 27 modules for `funExt λ m`, `λ m →` or a
destructured splitting finds hits only here and in the `Theory/Type/`
connective introductions (`Ω`, `eq-η`, Yoneda naturality).

| module | lines | content |
|---|---|---|
| `Monoid/Unitor` | 170 | the associator and both unitors are isomorphisms; naturality at general levels; `⊗≅` |
| `Monoid/Convolution` | 95 | `⟦⊗e⟧`'s β/η and naturality, and the nullary `⊗e ε·` |
| `Monoid/Residual/Laws` | 61 | how `⟜-intro⁻` crosses `⟜-post` and `⟜-precomp` |
| `Monoid/KleeneStar/Map` | 95 | `_*` is a functor; `*-map-section`, `*≅` |

## Landed — automata (`Theory/Instances/Monoid/`)

| module | lines | content |
|---|---|---|
| `Automata/NFA/Base` | 219 | the `NFA` record, `matchesTransition`/`hasTransition`, the `Accepting` and `PotentiallyRejecting` trace codes with `STOP`/`STEP`/`STEPε`, and `step-in`/`step-out`/`map-step` for both |
| `Automata/NFA/Properties` | 81 | `Acc.Trace q ≅ PR.Trace true q` |
| `Automata/Deterministic` | 159 | the `DeterministicAutomaton` record, its trace code, `parse` (every word has a run from every state) and `print` |
| `Automata/DFA/Base` | 21 | `DFAOver`, `DFA` |
| `Automata/Turing/OneSided/Base` | 133 | one-sided Turing machines; `Turing = Reify Accepting` |

## Landed — Thompson (`Theory/Instances/Monoid/Thompson/`)

Stated over `Regex.Base`'s nullability-indexed `RE`, not over a private copy
of the old `RegularExpression` (which the `Regex` rewrite deleted).  Two
consequences: the index rules out `(εr) *r`, so the guardedness side
condition is a typing rule rather than a lemma; and `satr` needs one
transition per satisfying character, so `Thompson/Base` and
`Thompson/Equivalence` take `isFinSet Alphabet`.  That is the classical
hypothesis for Thompson's construction and the first place in this port
that wants it.

| module | lines | content |
|---|---|---|
| `Construction/Epsilon` | 63 | `Parse εNFA ≅ ε↑` |
| `Construction/Bottom` | 62 | `Parse ⊥NFA ≅ ⊥↑` |
| `Construction/Literal` | 137 | `Parse (literalNFA c) ≅ literal c ↑` |
| `Construction/Sat` | 142 | `Parse (satNFA P) ≅ satG P ↑` — new; `RE` has a `satr` the old regex did not |
| `Construction/Sum` | 335 | `Parse (⊕NFA N N') ≅ Parse N ⊕ Parse N'` |
| `Construction/LinearProduct` | 544 | `Parse (⊗NFA N N') ≅ Parse N ⊗ Parse N'` |
| `Construction/KleeneStar` | 512 | `Parse (*NFA N) ≅ (Parse N) *` |
| `Thompson/Base` | 138 | `regex→NFA` over `Regex.Base`'s `RE`; `reLevel`; `isFinOrd` of states, transitions and ε-transitions |
| `Thompson/Equivalence` | 82 | **`regex≅NFA : ∀ {n} (r : RE n) → Parse (regex→NFA r) ≅ ⟦ r ⟧nfa`** |

## Landed — determinization

`Determinization/WeakEquivalence` (497 lines): the ε-closure, the subset
construction `ℙN`, and

    NFA≈DFA : NTrace.Trace true N.init
            ≈ ℙN.Trace true (ε-closure (SingletonDecℙ N.Q N.init))

The module requires the states to sit at `ℓ-max ℓN ℓAlph`.  That is a real
side condition, not a level hack: the powerset the construction ranges over
has to hold the transition relation, whose decidable proposition compares
*labels*, so it cannot be smaller than the alphabet.  The old file assumed
`Alphabet : hSet ℓ-zero` and so never met it.

## Landed — sequential unambiguity

`A ⊛ B` ("for every character, either `A` cannot be *continued* by it or `B`
cannot *begin* with it") is the side condition every LL/greedy argument
wants.  The old tree stated it over `Grammar/External/LinearProduct/
SplittingTrichotomy`; here the one element-level fact is `Precise.⊗&-align`
and everything above it is DSL composition.

| module | lines | content |
|---|---|---|
| `SequentialUnambiguity/Nullable` | 87 | `stringSplit` (the internal `&string-split≅`), `¬Nullable` transfer through every connective |
| `SequentialUnambiguity/First` | 196 | `startsWith`, `_∉First_` and its closure; `first⊗-split`; `_#_` and `#→disjoint`; `∉First*` |
| `SequentialUnambiguity/FollowLast` | 73 | `_∉FollowLast_`, the primed (Brüggemann-Klein/Wood) variant, and their agreement under `¬Nullable` |
| `SequentialUnambiguity/Base` | 408 | `_⊛_` and its closure; `⊛→must-split`; `⊗&-distL`; `∉FollowLast-⊗¬null` / `-⊗null` / `-⊕` / `-*` |
| `Precise` | +80 | `levi`, `splitAgree`, `⊗&-align` |

`splitAgree` -- "under those hypotheses the two cuts coincide" -- is the
shared root.  `⊗&-align` repackages it as a term; `Soundness.unambiguous⊗`
needs it as a *path* between the two splittings, which `⊗&-align` does not
expose, so neither derives from the other.  Landing it collapsed three
copies of the same Levi-clash case analysis:
`Automaton/Implicit/Soundness`'s `clash⊗` + `go` and
`KleeneStar/Unambiguous`'s `levi` + `headStarts` + `clash` + `piecesFrom`
both went away (-125 lines, +38).  `Soundness.disjointFirsts→` is now
`First.#→disjoint`, and `KleeneStar/Unambiguous` imports `startsWith`,
`_∉First_` and `_∉FollowLast_` instead of restating them.

`⊗&-align` is the whole content:

    (∀ g → (A ⊗ ⟨g⟩⊤ & C ⊢ ⊥) ⊎ (⟨g⟩⊤ & B ⊢ ⊥))
    → (∀ g → (C ⊗ ⟨g⟩⊤ & A ⊢ ⊥) ⊎ (⟨g⟩⊤ & D ⊢ ⊥))
    → (A ⊗ B) & (C ⊗ D) ⊢ (A & C) ⊗ (B & D)

Levi says two factorisations of a word differ by a `d`; if `d` starts with
a letter `g` then `g` both continues one left factor into the other and
opens the other's right factor, so a separation hypothesis at `g` refutes
it.  With every proper case refuted the two cuts coincide.  Instantiated at
`C := A` the hypotheses are literally `A ⊛ B` and `A ⊛ C`, which is the old
`⊗&-distL≅`.  Only the forward map is built: the clients use only `.fun`,
and the round trips would need splitting bookkeeping that nothing wants.

`∉FollowLast-*` is Brüggemann-Klein and Wood's star theorem.  One
unrolling does not suffice, so it is a `fold*r` whose carrier is
`¬Ty (FollowLastTy (A *) c) & (A *)`; `⊗&-distL` is applied twice per cons
step to pin the two cuts against each other.  The old proof needed
`¬Nullable A` as a hypothesis for the inverse of `(A *) & char⁺ ≅ A ⊗ A *`;
only the forward map is used, so the port drops it.

## Still not ported

* `Grammar/External/*` (1,439) — deliberately not ported; it states things in
  `Set` rather than internally.  `Monoid/Precise` is the internal
  replacement for the splitting trichotomy.
* `Grammar/Coherence` (73) — **cut deliberately**.  Its three lemmas are
  consequences of "grammars at `ℓ-zero` form a `MonoidalCategory`", stated
  through `Cubical.Categories.Monoidal.Combinators`; that is external
  framing.  The internal content it rested on — the associator and unitors
  being isos — is `Monoid/Unitor`, and clients should use that.
* `Automata/Deterministic`'s completeness,
  `π q ∘⊢ parse* ∘⊢ print b q ≡ σ⊕ b`.  The `readChars` half is now done
  (`KleeneStar/Read`, below); what remains is `unambiguous (Trace b q)`.
  See "Two deterministic automata" below -- that theorem already exists.

## Landed -- `KleeneStar/Read`

`readChars ∘⊢ ⊤Ty-intro ≡ id⊢` at `char *`.  `Strings` proves this for
`String*`, but `String*` is `μ X. εTy ⊕ (char ⊗ X)` under `kleeneBranch`
while `char *` is *the same code* under `starBranch char` -- identical
right-hand sides, but as functions `Bool → Functor` they never compare, so
the two are different types.  `Strings` cannot define `char *` either:
`KleeneStar` imports `Strings`, not the reverse.

Rather than mirror `Strings.readSq'` at the other code, it comes out of the
sequential-unambiguity layer.  `char` is non-nullable, unambiguous, and
`c ∉FollowLast char` for every `c` -- no letter can continue a one-letter
word, which is `Precise.char⊗-precise` -- so `unambiguous-*` gives
`unambiguous (char *)`, and *any* two terms into a proposition agree.  The
section is then three lines.  Corollary in `Automata/Deterministic`:
`parse ∘⊢ ⊤Ty-intro ≡ parse*`.

## Merged: the two deterministic automata

`Automata/Deterministic` (this port) and `Automaton/Deterministic` (ported
concurrently) both defined a `DeterministicAutomaton` with a `Bool`-indexed
`Trace`.  They are now one record, in `Automaton/Deterministic`;
`Automata/Deterministic` is deleted.

The blocker was that theirs pinned `Q : Type ℓAlph`, with a comment saying
the level was forced by the code language.  It is not: `Functor` is

    data Functor (ℓA : Level) {ℓX} (X : Type ℓX) (xs : X → S) : S → Type _

so the variable set carries its *own* level.  The only real constraint is
`⊕e : (Y : Type ℓX) → …` -- the summand index `Tag` mentions `Alphabet`, so
it has to sit at `X`'s level.  Hence `QL = Lift ℓAlph Q`, and the *carrier*
stays at `ℓM`, so no grammar inside the code is lifted.  (The deleted copy
lifted the carrier too, which was unnecessary.)

Fallout, all of it mechanical, because `Lift` has η:

| file | change |
|---|---|
| `Automaton/Unambiguous` | `Fam` at `ℓT`; `Var (δ q c)` → `Var (lift (δ q c))` |
| `Implicit/Disjointness` | `ParseAlg↑` / `recParse` adapters; `disjAlg` and `fromCode` index by `QL` |
| `Implicit/Soundness` (1309 lines) | nine `rec (D_.TraceTy true) alg initial` → `recParse M alg initial`; no proof touched |
| `Automaton/GreedyMax` | one `alg` indexed by `QL` |

Carried across from the deleted copy into the merged record: `TraceAlg`,
`STOP'` (stop at a given bit), the named `stepBranch`, and the DSL-level
`step-in`/`step-out`/`step-η`/`map-step` -- the combinators that keep a
labelled-transition branch from binding a model element.
`Determinization/WeakEquivalence` and `Automata/DFA/Base` now sit on the
merged record.  `print` moved to `Automaton/Print`.

## Landed -- completeness of `parse`/`print`

`Automaton/Print.parse-print`:

    π q ∘⊢ parse isSetQ ∘⊢ print b q ≡ σ⊕ b

Totality is `parse` (every word has a run from every state); this is
uniqueness.  Both sides are maps into `Runs q = ⊕[ b ] Trace b q`, and that
is a proposition, so there is nothing left to check -- each `Trace b q` is
unambiguous (`Automaton/Unambiguous`) and traces at different bits are
disjoint (`TraceDisj`).

Getting there meant moving two things up to where they belong:

* `TraceDisj` was stated only inside `Implicit/Disjointness`'s
  `module _ (M : ImplicitDeterministicAutomaton Q)`, though nothing in its
  `disjAlg` mentions that wrapper.  It is now
  `Automaton/Disjoint.TraceDisj`, over any `DeterministicAutomaton`, with
  `unambiguous-Runs` beside it.  `Implicit/Disjointness` keeps a one-line
  re-export (-109 lines, +44).
* `ε∉lit⊗` and `sameHead` -- a `literal`-headed word is not empty, and two
  such words agree on their head letter -- were top-level in
  `Implicit/Disjointness`.  They are precision facts about `literal`, so
  they moved to `Precise`, which is what both the automaton and the
  sequential-unambiguity layers already depend on.  `CodeLayer`/`fromCode`
  moved into the `DeterministicAutomaton` record next to `unrollTrace`.

The other direction is free: `char *` is a proposition, so `print` is the
*only* map a run has into it (`print-unique`) -- there is nothing to prove
about which word it produces.
