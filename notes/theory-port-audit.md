# Port audit: old `Grammar/` tree → `Theory/`

Verified by reading `src/` on `theory-core` @ `b97897d`, not predicted.

Sizes: old tree 18,858 lines (`Grammar` 10,449 · `Automata` 2,417 · `Examples`
2,634 · `Thompson` 1,666 · `String` 648 · `Determinization` 490 · `Lex` 217 ·
`Term` 205 · `Parser` 132). `Theory/` is 17,062 lines.

`Theory/` imports **nothing** from the old tree — the two are disjoint, so
nothing here is blocked on anything else.

Two useful facts that shape every recommendation below:

* `Theory/Type/*` is generic in `(σeq, V, vs, 𝒫)` — a finitary multisorted
  theory and a presentation. `Theory/Instances/Monoid/*` instantiates it at
  `MonEqns` + `listPresentation`, and that is where strings live.
* `Theory/` contains **zero** uses of `FinSet`/`isFinSet`. The entire
  finite-state layer of the old tree has no counterpart, and this is
  deliberate — see §5.

---

## 1. Ported and generic (`Theory/Type/`)

| old | new |
|---|---|
| `Grammar/Base`, `Term/{Base,Category,Nullary}` | `Theory/Base` (`TheoryTy`, `_⊢_`, `THEORYTY` wildcat), `Type/Category` |
| `Grammar/Equivalence/Base` (StrongEquivalence) | `Theory/Base._≅_` via `WildCatIso` |
| `Grammar/{Top,Bottom}` | `Type/Top/{Base,Properties}`, `Type/Bottom/Base` |
| `Grammar/Sum/*`, `Grammar/Product/*` | `Type/Sum/{Base,Binary/Base}`, `Type/Product/{Base,Binary/Base}` |
| `Grammar/Function/*` (`⇒`) | `Type/Function/Base` |
| `Grammar/Lift`, `Grammar/HLevels`, `Grammar/Distributivity` | `Type/Lift/Base`, `Type/HLevels`, `Type/Distributivity` |
| `Grammar/Equalizer` | `Type/Equalizer/Base` |
| `Grammar/Inductive/{Indexed,Functor,HLevels}` | `Type/Code/{Base,Container}`, `Type/Inductive/{Base,HLevels}` |
| `Grammar/Unfold` | `Type/Coinductive/Base` |
| `Grammar/Later/*` | `Type/Later/{Poset,Indexed,Tabulated,Tag,Derivative,Lex}`, `Type/Guarded/{Base,Justification}` |
| `Grammar/Maybe` | `Type/Monad/Maybe` (+ `Cont`, `Except`) |
| `Grammar/Negation` | `Type/Decidable/Base.¬Ty` |
| `Grammar/Properties/Base` (unambiguity) | `Type/Unambiguity/Base` — partial, see §3 |
| `Grammar/SemanticAction/Base` | `Type/SemanticAction/{Base,Pipeline}` |
| `Grammar/LinearProduct/*` (`⊗`) | `Type/Operation/Base` — `⊗` is *any* signature operation lifted |
| `Grammar/LinearFunction` (`⊸`/`⟜`) | `Type/Residual/Base` |
| `Grammar/Reify` | `Type/Representable/Base` (`⌈ m ⌉`, Yoneda) |

New with no old counterpart: `Type/Cover/Base` (indexed
total-and-disjoint covers — the LL condition), `Type/Decidable/{Base,Route}`.

## 2. Ported and monoid-specific (`Theory/Instances/Monoid/`)

| old | new |
|---|---|
| `String/Base`, `Grammar/String/*` | `Monoid/{Base,ListPresentation,Strings,Types}` |
| `Grammar/{Epsilon,Literal}/*` | `Monoid/Strings` (`εTy`, `literal`, `char`) |
| `Grammar/KleeneStar/Inductive/*` | `Monoid/KleeneStar`, `Monoid/KleeneStar/Guarded` |
| `Grammar/Derivative/{Base,String}` | `Monoid/Derivative`, `Monoid/Derivative/General` |
| `Grammar/Greedy/{Base,Automata}` | `Monoid/Greedy/{Base,Examples}` |
| `Grammar/RegularExpression/*` | `Monoid/Regex/*` (9 modules — surface syntax, Unicode classes, derivative, parse) |
| `Lex/Det/{Base,Eval}` | `Monoid/Lex/{Base,Regex,Demo}` |
| `Automata/Deterministic` | `Monoid/Automaton/{Base,Scan,Examples}` — reformulated, see §5 |
| `String/Unicode` | `Monoid/Unicode/Base`, `Regex/Unicode` |
| `Parser/{Base,RecursiveDescent}` | `Monoid/Combinator/{Decidable,Incomplete}/*` (24 modules) |
| `Examples/Dyck`, `Examples/Benchmark/Dyck` | `Monoid/Grammars/Dyck`, `Combinator/*/Dyck` |
| splitting-trichotomy facts | `Monoid/Precise` (Levi derived from cons-injectivity) |

Also new: `Monoid/Backreference/*`, `Monoid/Lookahead/*`, `Monoid/Suffix/Base`,
`Monoid/Residual`, `Monoid/GuardedSplit`.

---

## 3. Not ported, and genuinely generic → `Theory/Type/`

These need no monoid structure. Ordered by value-per-line.

* **`Grammar/Subgrammar/{Base,Equalizer}`** (353 lines) — the subobject
  classifier `Ω m = hProp ℓ`, `true`/`false`, subgrammar as the pullback of
  `true`, and the derivation of subgrammars from equalizers. Every dependency
  (`Top`, `Equalizer`, `HLevels`) is already generic. Straight lift to
  `Type/Subgrammar/{Base,Equalizer}`. This is the largest clean win.

* **`Grammar/PropositionalTruncation/Base`** (61 lines) — `∥ A ∥ m = ∥ A m ∥₁`
  and its recursor. Pointwise, so fully generic. Blocks the weak-equivalence
  work below.

* **`Grammar/Coherence`** (73 lines) — MacLane coherence for `⊗`/`ε`. At
  `Type/Operation/Base` this becomes coherence for *any* associative-unital
  signature operation, driven by the theory's equations rather than restated.
  (Memory note `project_monoid_structure` says a version of this exists on
  another branch — check before rewriting.)

* **`Grammar/Properties/Base` residue** — `Type/Unambiguity/Base` has
  `unambiguous`, `subterminal`, `unambiguous{⊤,⊥,⇒}`, `unambiguousRetract`. It
  is missing binary `disjoint A B = A & B ⊢ ⊥Ty` and its lemmas
  (`disjoint⊕l/r`, `disjoint→⊕-unambiguous`), and the weak equivalence `_≈_`.
  Note `Type/Cover/Base` already carries a `disjoint` *field* in indexed form,
  so the binary version should be derived from a two-element cover, not
  restated.

* **`Grammar/Equivalence/Base` residue** (~60 of 186 lines) — `isMono`,
  `_isRetractOf_`, `hasRetraction→isMono`, `isStrongEquivalence→isMono`.
  Pure category theory over `THEORYTY`; belongs in `Type/Category`.

## 4. Not ported, and monoid-specific → `Theory/Instances/Monoid/`

* **`Grammar/SequentialUnambiguity/*`** (944 lines: `Nullable`, `First`,
  `FollowLast`, `Base`, `Properties`) — `¬Nullable`, `c ∉First A`,
  `c ∉FollowLast A`, `A # B`, `A ⊛ B`, and the congruence lemmas over
  `⊗`/`⊕`/`*`. This is the *semantic* FIRST/FOLLOW theory, and it is the
  biggest unported chunk with no replacement anywhere. `Theory/` currently has
  `¬Nullable` (in `Regex/Base`, `KleeneStar/Guarded`, `Lex/Base` — reinvented
  three times, informally) and Bool-level FIRST/FOLLOW inside
  `Combinator/Decidable/{Polynomial,Productions}`, but no `∉FollowLast` and no
  `⊛`. Porting this would let the LL combinators state their side conditions
  as theorems instead of as decidable tests.

  Dependencies: `PropositionalTruncation` (§3), `Precise` (present),
  `Monoid/Suffix` (present). `Grammar/External/{LinearProduct/SplittingTrichotomy,
  String/Tiny}` are imported by the old version but should be replaced by
  `Monoid/Precise` rather than ported — see §5.

* **`String/{ASCII/Base,ASCII/NoWhitespace,SubAlphabet}`** (321 lines) —
  concrete alphabets and the sub-alphabet embedding. `Theory/` has Unicode
  only. Mechanical; low priority unless something needs ASCII.

* **`Examples/Section2/*`, `Examples/BinOp`, `Examples/RegexParser`** (~2,634
  lines incl. `Examples/RecursiveDescent`) — paper figures. Only worth porting
  the ones the paper still cites; `Monoid/Examples` +
  `Combinator/Decidable/Arith` already cover much of `BinOp`.

## 5. Deliberately not portable as-is

**`Grammar/External/*`** (1,439 lines) — `External/HLevels`,
`External/Equivalence/PointwiseIso`, `External/LinearProduct/SplittingTrichotomy`,
`External/String/Tiny`. These state things about grammars in `Set` rather than
internally, which is exactly what the `Theory/` design rejects. `Precise.agda`
is the internal replacement for the splitting trichotomy; the rest should be
re-derived internally on demand, never lifted.

**The `AsPath`/`AsEquality` and `AsPrimitive`/`AsIndexed` duplication** —
`Grammar/{Epsilon,Literal,LinearProduct}/As{Path,Equality}` and
`Grammar/{Sum,Product}/Binary/As{Primitive,Indexed}` are two presentations of
the same connective. `Theory/` picked one of each (`Eq`-flavoured, primitive
binary) and there is no reason to carry the other back.

**Empty leftovers** — `src/Grammar/Investigations/` and `src/Strict/` contain
no `.agda` files.

---

## 6. Thompson / NFA / determinization

`Automata/{NFA,DFA,Implicit,Turing}` (2,417) + `Thompson/*` (1,666) +
`Determinization/WeakEquivalence` (490) = **4,573 lines, none of it ported**.
The honest reading is that most of it was *replaced*, not left behind.

The old chain was `regex → NFA (Thompson) → DFA (subset construction) → Trace
grammar → parse`, with `Trace` a μ-grammar over a `FinSet` of states and
weak equivalence `≈` mediating the ambiguity that determinization introduces.

`Theory/` takes the derivative route instead, and the header of
`Monoid/Regex/Derivative.agda` says so outright: *"ours is the same with the
automaton deleted, indexing by the residual regex instead of by a DFA state."*
`Monoid/Automaton/Base` confirms the reformulation — a `DerivAutomaton` does
not *define* a language from a transition table, it takes the language `L : Q →
TheoryTy` as given and *requires* `δ` to be the derivative:

```agda
δ-∂  : (q : Q) (c : Alphabet) → ∂[ literal c ] (L q) ⊢ L (δ q c)
δ-∂⁻ : (q : Q) (c : Alphabet) → L (δ q c) ⊢ ∂[ literal c ] (L q)
```

That kills the need for `FinSet`, for decidable state equality, and for the
`Trace ≅ L` theorem that Thompson's 1,666 lines mostly consist of. Which is why
`Theory/` has no `FinSet` at all.

So the recommendation splits three ways:

**(a) Generalize `DerivAutomaton` to an arbitrary theory — worth doing.**
The interface is nearly theory-generic already: `∂[_]_` comes from
`Type/Residual`, `⌈gen v⌉` from `Type/Representable`. Replacing `δ : Q →
Alphabet → Q` with `δ : Q → V → Q` over the presentation's generator set `V`
gives derivative automata for *any* finitary theory — a commutative automaton
at `Bags`, a tree automaton at the two-sorted lambda theory. The catch, and it
should be stated rather than papered over: `δ*`/`Scan` additionally need an
eliminator for `↓M s` by generator-steps with a well-founded step order. At
`Monoid` that is list recursion via `ListPresentation` and `Monoid/Suffix`. So
the generic module wants a `GeneratedPresentation` record (generator step +
well-foundedness) as a *second* parameter, and `Monoid` supplies it. Suggested
home: `Theory/Type/Automaton/Base` (interface, generic) with
`Monoid/Automaton/Base` becoming the instantiation.

**(b) Port the NFA as a code, not as a record — worth doing, cheap.**
`Automata/NFA/Base`'s `Trace` is literally a strictly-positive functor: `⊕e`
over outgoing transitions, `⊗e` with `literal (label t)`, `Var (dst t)`. That
is exactly what `Type/Code/Base` classifies. A nondeterministic automaton over
any theory is then "a `Q`-indexed `Code`", with `μ` giving the trace type and
`Type/Inductive/HLevels` giving its set-ness for free. This is ~50 lines
generic and subsumes the record, the `Turing` module's shape, and the ε-closure
bookkeeping (an ε-transition is a `Var` summand with no `⊗e`).

**(c) Thompson and the subset construction — port only if you want
finiteness.** These two exist to prove *every regex is weakly equivalent to a
DFA*. `Theory/`'s derivative route gets parsing without them, but it gets it
via unbounded syntactic residuals: there is no Brzozowski finiteness theorem
(finitely many derivatives up to ACI) anywhere in `Theory/`, and no
`isFinSet` to state one with. Concretely:

* If the goal is *parsing*, Thompson + `Determinization/WeakEquivalence` are
  dead code. `Regex/Derivative` + `Automaton/Scan` already do the job with 0
  holes, and `Regex/Derivative`'s own comment explains why the smart
  constructors — not determinization — are what keeps the residual from
  blowing up.
* If the goal is the *finite-state theory* (pumping, minimization, closure
  under complement, a decision procedure for regex equivalence), then
  `Determinization/WeakEquivalence` is the only place in the repo with the
  powerset construction and reachability, it is the only consumer of `≈`, and
  it is worth a real port — but it should be re-stated against
  `DerivAutomaton` (subset-of-residuals) rather than against the old `NFA`
  record, and it will drag `PropositionalTruncation` (§3) and `≈` in with it.

Thompson's per-connective constructions (`Construction/{KleeneStar,
LinearProduct,Sum,Literal,Epsilon,Bottom}`, 1,521 of the 1,666 lines) are the
part I would *not* port under either goal: they are `⊗`/`*`-specific splitting
arguments that `Monoid/Precise` and `Monoid/Suffix` now do better, and the
theorem they build toward is reachable from derivatives instead.

---

## Suggested order

1. `Type/Subgrammar/*` + `Type/PropositionalTruncation/Base` — clean generic
   lifts, no design questions, unblock §4.
2. `Monoid/SequentialUnambiguity/*` — biggest unreplaced chunk; makes the
   existing LL combinators' side conditions provable rather than merely
   decidable.
3. `Type/Automaton/Base` — generalize `DerivAutomaton` over `V`, factor out
   the generated-presentation requirement, re-instantiate `Monoid/Automaton`.
4. `Type/Automaton/Code` — NFA-as-code; retires `Automata/{NFA,DFA,Turing}`.
5. `Type/Category` residue (`isMono`, retracts) + `Unambiguity` residue
   (binary `disjoint` from a two-element `Cover`, `_≈_`).
6. Decide on finiteness before touching `Determinization`; delete
   `Thompson/Construction/*` and `Grammar/External/*` rather than porting.
