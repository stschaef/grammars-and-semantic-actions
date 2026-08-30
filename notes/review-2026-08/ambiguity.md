# Audit: the ambiguity / sequential-unambiguity subsystem

Read-only review. Paths are absolute-from-repo-root (`/home/steven/grammars-and-semantic-actions/`).

---

## 0. What the definitions actually say

Stated in my own words, from the code, before the findings.

| name | site | meaning as implemented |
|---|---|---|
| `unambiguous A` | `src/Theory/Type/Unambiguity/Base.agda:26` | `∀ m → isProp (A m)` — for each model element (word) `m`, at most one derivation. **Element-level.** This is what the old tree called `isLang`, not what the old tree called `unambiguous`. |
| `subterminal A` | `src/Theory/Type/Unambiguity/Base.agda:28` | `∀ {B} (f g : B ⊢ A) → f ≡ g` — `A` is a subterminal object of the type category. **The internal statement.** Proved equivalent to `unambiguous` at `:31`–`:43`. |
| `disjoint A B` | `src/Theory/Type/Unambiguity/Disjoint.agda:45` | `A & B ⊢ ⊥Ty` — no word is both an `A` and a `B`. Fully internal. |
| `Disjoint A` (family) | `src/Theory/Type/Cover/Base.agda:34` | `∀ y y' → (y Eq.≡ y' → ⊥) → A y & A y' ⊢ ⊥Ty` — pairwise disjointness of an indexed family, with the index inequality in the metalanguage. |
| `Cover Y A` | `src/Theory/Type/Cover/Base.agda:39` | `Disjoint A` + `Total A` where `Total A = ⊤Ty ⊢ ⊕[y] A y` — a partition of the whole sort into `Y`-many parts. |
| `¬Nullable A` | `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:45` | `A & εTy ⊢ ⊥Ty` — i.e. `disjoint A εTy`. `A` does not accept the empty word. |
| `startsWith c` | `src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda:46` | `literal c ⊗ ⊤Ty`. |
| `c ∉First A` | `.../First.agda:58` | `startsWith c & A ⊢ ⊥Ty` — no `A`-word begins with `c`. Note the subsystem only ever has **refutations**: there is no positive `First A ⊆ Σ`. |
| `c ∉FollowLast A` | `.../FollowLast.agda:37` | `(A ⊗ startsWith c) & A ⊢ ⊥Ty` — no word is simultaneously an `A`-word and an `A`-word extended by a nonempty `c`-headed suffix. `∉FollowLast'` (`:40`) restricts the left factor to nonempty words (Brüggemann-Klein–Wood). |
| `A ⊛ B` | `.../SequentialUnambiguity/Base.agda:52` | `(c : Alphabet) → (c ∉FollowLast A) ⊎ (c ∉First B)`. |
| `A # B` | `.../First.agda:127` | `(c : Alphabet) → (c ∉First A) ⊎ (c ∉First B)` — "separated first sets". |
| `Precise` | `src/Theory/Instances/Monoid/Precise.agda` | **No definition of this name exists.** The word is used informally in the header for "a splitting whose left factor is one letter is determined by the whole word". |

The definitions are individually correct and match the standard formal-language notions. Two of them are subtly *not* what their name suggests; see F6 and F7.

---

## Findings, ranked

### F1 (critical, dead code + duplicated development) — the entire FollowLast-closure theory has zero consumers

`src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda` is 434 lines. Grepping the whole repo for uses outside the file itself:

```
⊛∘⊢-r ⊛∘⊢-l ⊛-⊗l ⊛-⊗ ⊛-⊕ ⊛-& ⊛-* ⊛-⊥ ⊛-εL ⊛-εR   : 0 uses
∉FollowLast→⊛  ⊛→must-split  ⊗&-distL  ⊗&-distL⁻  factor⊗3 : 0 uses
∉FollowLast-⊗¬null  ∉FollowLast-⊗null  ∉FollowLast-⊕  ∉FollowLast-* : 0 uses
```

The only importer is `src/Theory/Instances/Monoid/Automaton/Implicit/Soundness.agda:46`:

> `using (#→disjoint ; unambiguous⊗ ; unambiguous⊕ ; disjointFirsts→)`

and `#→disjoint`/`disjointFirsts→` are the same function (F5). So ~300 of 434 lines — including the two hardest proofs, `∉FollowLast-⊗null` (`:202`–`:248`) and the Brüggemann-Klein–Wood star theorem `∉FollowLast-*` (`:305`–`:399`) — are load-bearing for nothing.

The reason is visible at `Soundness.agda:1159`–`:1176`: the `DetReg` syntax carries its first/follow-last sets as *external* powerset annotations (`c ∈ℙ ¬FL`), and the corresponding grammar-level refutations are produced from the **automaton** side:

```agda
seqOfTy dr dr' su c with su c
... | Sum.inl h = Sum.inl (¬FollowLastAut (Aut dr) c (nullOf disc dr) (δq-fail disc dr c h) ∘⊢ …)
```

So the repo carries two independent proofs that `∉FollowLast` is closed under `⊗`, `⊕`, `*`: an automaton-theoretic one (live, in `Automaton/Implicit/*`) and a grammar-theoretic one (dead, here).

**Fix.** Decide. Either (a) delete `Base.agda:57`–`:399` and keep only the four used lemmas, moving them to `FollowLast.agda`; or (b) keep the grammar-side theory as the *primary* one and derive the `DetReg` side conditions from it, deleting `¬FollowLastAut`/`δq-fail`. Do not ship both. If the grammar-side theory is kept for its own sake, say so in the header, which currently claims "the reason it is the side condition every LL/greedy argument wants" (`:7`–`:8`) — no LL/greedy argument in the repo wants it.

---

### F2 (high, duplication) — `SeqUnambig`/`Unambig` re-declare `⊛`/`unambiguous`, with a false excuse

`src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda:46`–`:57`:

```agda
-- `∀ m → isProp (A m)`, as `Theory/Type/Unambiguity/Base` states it; named
-- locally because that module reaches here by two paths.
Unambig : TheoryTy ℓA tt → Type _
Unambig A = (m : String) → isProp (A m)

SeqUnambig : TheoryTy ℓA tt → Type _
SeqUnambig A = (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First A)
```

The excuse is wrong: this file already imports `Theory.Instances.Monoid.Strings` at line 33, and `Strings.agda:53` re-exports `Theory.Type.Unambiguity.Base` **publicly**, so `unambiguous` is already in scope and `Unambig` is a shadowing duplicate. Downstream this leaks: `Soundness.agda:41` imports `SeqUnambig` from here and `unambiguous⊗` from `SequentialUnambiguity/Base` — two names, one concept, in one import block.

**Fix.** Delete `Unambig`, use `unambiguous`. Move `sequentiallyUnambiguous`/`⊛` **down** from `SequentialUnambiguity/Base.agda:50` into `SequentialUnambiguity/FollowLast.agda` (both `_∉FollowLast_` and `_∉First_` are in scope there, and `KleeneStar/Unambiguous.agda:41` already imports exactly that module). Then `SeqUnambig A` is `A ⊛ A` and both files share one definition.

---

### F3 (high, duplication) — three verbatim copy-pastes across the subsystem

1. **`≈→≅`.** `src/Theory/Type/Unambiguity/Disjoint.agda:133` and `src/Theory/Instances/Monoid/Automaton/Implicit/Soundness.agda:74`–`:79` are character-for-character the same four clauses, with `Soundness` even carrying a comment calling it "the old `≈→≅`". Delete the copy in `Soundness`; import from `Unambiguity/Disjoint`.
2. **`isPropεTy`.** Defined at `src/Theory/Instances/Monoid/Unitor.agda:39` and again at `src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:46`. Two downstream files (`Soundness.agda:58`, `GreedyMax.agda:52`) import the *automaton* copy, so a fact about `εTy` is being sourced from an automaton module. Delete the second; re-export from `Strings`.
3. **`isUnambiguousRetract'`.** `src/Theory/Type/Unambiguity/Disjoint.agda:106`–`:108` is a pure eta-expansion of `unambiguousRetract` from `Base.agda:59`:
   > `isUnambiguousRetract' f g r uB = unambiguousRetract f g r uB`

   Delete it and rename call sites (`:112`, `:115`, `:126`).

Also `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:432`–`:434`:

```agda
disjointFirsts→ : … → disjoint A B
disjointFirsts→ = #→disjoint
```

Both names are exported and both are imported by `Soundness.agda:46`. Pick one.

---

### F4 (high, internality) — `⊗&-align`'s separation hypothesis is `⊛` spelled out by hand, matched only definitionally

`src/Theory/Instances/Monoid/Precise.agda:164`–`:169`:

```agda
  (sepL : (g : Alphabet)
    → ((A ⊗ (literal g ⊗ ⊤Ty)) & C ⊢ ⊥Ty)
      Sum.⊎ (((literal g ⊗ ⊤Ty) & B) ⊢ ⊥Ty))
```

That is `(g ∉FollowLast A) ⊎ (g ∉First B)` with `startsWith`, `FirstTy`, `FollowLastTy`, `_∉First_`, `_∉FollowLast_` and `sequentiallyUnambiguous` all manually unfolded, because `Precise` sits below `SequentialUnambiguity` in the import order. Then `SequentialUnambiguity/Base.agda:171`–`:172`:

```agda
⊗&-distL sepB sepC = ⊗&-align {A = A} {B = B} {C = A} {D = C} sepB sepC
```

passes an `A ⊛ B` where `sepL` is expected. This typechecks only because six definitions happen to unfold to the same expression. Any of them changing (e.g. `startsWith c = char & …`, or `FirstTy` swapping the `&` operands) silently breaks the single most important lemma in the subsystem with an unification error a hundred lines away.

**Fix.** Introduce `startsWith`, `FirstTy`, `FollowLastTy`, `_∉First_`, `_∉FollowLast_` and `_⊛_` in a module *below* `Precise` (see F10), and state `⊗&-align`'s hypotheses as `A ⊛ B` and `C ⊛ D`. `⊗&-distL` then becomes `⊗&-align` with no argument massaging at all, and the definitional coincidence becomes a type-level fact.

---

### F5 (high, duplication against the old tree) — two live copies of the whole subsystem, with `unambiguous` meaning different things in each

`src/Grammar/SequentialUnambiguity/{Base,First,FollowLast,Nullable}.agda` is a 1-for-1 predecessor of the Theory versions (same lemma names in the same order: `∉FollowLast→⊛`, `⊛-⊗l`, `⊛-⊗`, `⊛∘g-r/-l`, `⊛-&`, `⊛-*`, `⊗&-distL≅`, `⊛→must-split`, `factor⊗3≅`, `∉FollowLast-⊗¬null`, `∉FollowLast-⊗null`, …). It is still imported by `src/Automata/Implicit.agda:22`, `src/Automata/Implicit/RegExp*.agda`, `src/Lex/Det/Base.agda:22`, `src/Examples/RecursiveDescent/{BinOp,Dyck}.agda`. Likewise `src/Grammar/Properties/Base.agda` ↔ `src/Theory/Type/Unambiguity/{Base,Disjoint}.agda` (`disjoint`, `disjoint⊢`, `disjoint⊢2`, `disjoint≈`, `disjoint≅`, `disjoint≅2`, `disjoint⊕l`, `disjoint⊕r`, `isUnambiguousRetract'`, `unambiguousRetract→…`, `&⊤≅`, `≈→≅`, `π≡→unambiguous`, `Δ≅→unambiguous`, `unambiguous→Δ≅` — all present in both).

The dangerous part is the name collision:

- `src/Grammar/Properties/Base.agda:43` — `unambiguous A = ∀ {B} (e e' : B ⊢ A) → e ≡ e'` (i.e. **subterminal**)
- `src/Theory/Type/Unambiguity/Base.agda:26` — `unambiguous A = ∀ m → isProp (A m)` (i.e. the old **`isLang`**)

Both trees are compiled. A reader moving between them will misread every statement. The two are provably equivalent (`Unambiguity/Base.agda:31`–`:43`), which makes the collision *safe* but not *clear*.

**Fix / what survives.** The Theory versions. The `src/Grammar/**` tree should be marked deprecated in a top-level note and its remaining consumers (`Automata/Implicit`, `Lex/Det`, `Examples/RecursiveDescent`) ported. Until then, at minimum rename the old one to `subterminal` so the word `unambiguous` means one thing repo-wide.

---

### F6 (medium, conceptual) — `⊛` is a *decision table*, not a property, and nothing says so

`SequentialUnambiguity/Base.agda:50`–`:55`:

```agda
sequentiallyUnambiguous A B =
  (c : Alphabet) → (c ∉FollowLast A) Sum.⊎ (c ∉First B)
```

The `⊎` is a metalanguage sum, so `A ⊛ B` is **data**, and two inhabitants can differ. This is not incidental: `Soundness.agda:541` / `:647` / `:742` / `:842` / `:946` / `:1036` all do `with seqUnambig c` and *build a different automaton transition* depending on which injection the witness chose. So `⊛` is closer to "an LL(1) lookahead table for the cut between `A` and `B`" than to "the concatenation is unambiguous".

The header (`Base.agda:2`–`:10`) describes it purely as a property — "the side condition every LL/greedy argument wants" — and never mentions that the witness is consumed computationally. Same for `A # B` (`First.agda:126`–`:127`).

**Fix.** One sentence in each header saying the witness is a choice function and is scanned by consumers; and consider naming them `Separation` / `separates` rather than `sequentiallyUnambiguous`, reserving the latter for the (propositional) consequence `unambiguous (A ⊗ B)`.

---

### F7 (medium, conceptual) — `Precise.agda` holds two unrelated notions under a name it never defines

The module is called `Precise` and its header (`:2`–`:6`) explains "precision of the token grammars". But there is no `Precise` or `isPrecise` definition anywhere. What is in the file is:

- lines 33–131: genuine token precision (`flat`, `flatEq`, `Dl-ε`, `Dl-lit⊗`, `lit⊗-nil/-head/-tail`, `lit⊗-precise`, `char⊗-precise`, `ε∉lit⊗`, `sameHead`, `dec-lit⊗↑`, `dec-char⊗↑`);
- lines 133–202: **Levi's lemma** and the two-splitting alignment `splitAgree`/`⊗&-align`, which is a different theorem about arbitrary factors under a separation hypothesis, and which is the real engine of the subsystem.

`Precise.agda:133` marks the boundary with a bare comment `-- Levi's lemma, and the alignment of two splittings that it powers.`

**Fix.** Split into `Precise.agda` (token precision) and `Levi.agda` (`levi`, `agree`, `splitAgree`, `⊗&-align`). `KleeneStar/Unambiguous.agda:39` and `SequentialUnambiguity/Base.agda:37` both import `Precise` solely for `splitAgree`/`⊗&-align`; after the split they would import only `Levi`, and the dependency graph would say what it means.

---

### F8 (medium, internality — avoidable escapes)

Two properties are proved by binding a model element where an internal term is available and already imported.

**F8a.** `src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda:68`–`:70`:

```agda
∉First-⊕ᴰ : … → ((y : Y) → c ∉First (A y)) → c ∉First (⊕[ y ∈ Y ] A y)
∉First-⊕ᴰ h m (sw , (y , a)) = h y m (sw , a)
```

`&⊕ᴰ-distR : A & (⊕[ y ] B y) ⊢ ⊕[ y ] (A & B y)` is imported into this very file at line 34. The internal proof is one line:

```agda
∉First-⊕ᴰ h = ⊕ᴰ-elim h ∘⊢ &⊕ᴰ-distR
```

The sibling `⊕ᴰ-¬Nullable` (`Nullable.agda:50`–`:52`) already does exactly this, so the file is internally inconsistent about its own idiom.

**F8b.** `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:113`–`:124`, the `where`-block under `∉FollowLast→⊛`:

```agda
    lit-first-clash d e ne m (sw , sw') = Empty.rec (ne (headEq m sw sw'))
      where
      headEq : (m : String) → startsWith d m → startsWith e m → d ≡ e
      headEq m (ms , q , (ld , _)) (ns , q' , (le , _)) =
        L.cons-inj₁ (flat d (ms zero) (ms (suc zero)) m ld q
                    ∙ sym (flat e (ns zero) (ns (suc zero)) m le q'))
```

`Precise.sameHead` (`Precise.agda:110`–`:122`) is precisely this fact as a `⊢`-term, and is already used internally by `Automaton/Disjoint.agda:65`. The whole 12-line block is:

```agda
lit-first-clash d e ne = ⊕ᴰ-elim (λ p → ⊥Ty-elim ∘⊢ Empty.rec (ne p)) ∘⊢ sameHead d e ∘⊢ …
```

(modulo the `⊤Ty` on the right of each `startsWith`). The old tree did it this way — `src/Grammar/SequentialUnambiguity/Base.agda:53` uses `same-first` — so this is a regression introduced by the port.

**Justified escapes** (no internal route exists; flagging only so the list is complete):
`Precise.agda:137` `levi`, `:172` `agree`, `:191` `splitAgree`, `:197` `⊗&-align` — Levi's lemma is genuinely combinatorial and there is no `⊗`-extensionality principle in the theory to replace it with.
`First.agda:82`–`:108` `split-go`/`first⊗-split` — matching the left factor's word is the only way to expose the head letter.
`Automaton/Unambiguous.agda:56`–`:123` and `KleeneStar/Unambiguous.agda:97`–`:153` — `unambiguous` is itself an element-level predicate, so its proofs must be.
`Base.agda:110` `with disc c c'` — forced by F6: `⊛` is data.
`Cover/Base.agda:34` `y Eq.≡ y' → ⊥` — the index is a metalanguage type by construction.

**F8c** (small, but the header lies): `First.agda:8`–`:9` says of `first⊗-split`, "It is the last element-level step in this layer." `∉First-⊕ᴰ` at line 70 of the same file is also element-level, and avoidably so (F8a).

---

### F9 (medium, proof engineering) — the same 40-line `PathP` dance, three times, and the lemma that would collapse it

Three proofs assemble a path between two elements of a binary-slot type by hand, with identically-named helpers:

| | file:line | helpers |
|---|---|---|
| a | `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:406`–`:420` | `pieces`, `sp` |
| b | `src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:72`–`:123` | `headc`, `headd`, `heads`, `c≡d`, `tails`, `sp`, `eqP`, `Fam`, `main`, `tP`, `gP` |
| c | `src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda:110`–`:153` | `split`, `parts`, `heads`, `tails`, `sp`, `main`, `eqP`, `tP`, `gP` |

(b) and (c) are structurally the same proof — `sp = funExt λ where zero → …; (suc zero) → …`, `eqP = isProp→PathP (λ i → isPropEqString) e e'`, `tP = toPathP h`, `gP zero = isPropPathP _ (isOfHLevelLift 1 …)`, `gP (suc zero) = λ i → lift (tP i)`, all wrapped in `cong (roll m) (ΣPathP …)`.

(a) is shorter only because `Strings.agda:225` already provides `⊗PathP'` for the `_⊗_` case. (b) and (c) cannot use it because they live over `⟦ two X Y ⟧TheoryTy`, the raw operation interpretation, rather than `_⊗_`.

**Proposed lemma.** Generalise `⊗PathP'` from `_⊗_` to a binary operation slot family — in `Theory/Type/HLevels.agda` or next to `⊗PathP'`:

```agda
opPathP2 : {F G : … } {x y : String} (r : x ≡ y)
  {ms ns : arities MonSig _⊙_ → String} (s : ms ≡ ns) …
  → PathP (λ j → F (s j zero)) a a'
  → PathP (λ j → G (s j (suc zero))) b b'
  → PathP (λ j → ⟦ two F G ⟧TheoryTy P (r j)) (ms , ex , a , b , tt*) (ns , ey , a' , b' , tt*)
```

with `⊗PathP'` becoming its `F = k A`, `G = k B` instance. (b) and (c) then lose `eqP`, `tP`, `gP` and `main` entirely — about 60 lines between them — and keep only the interesting part (`c≡d` / `parts`).

Also worth noting: both (b) `:73`–`:77` and (c) `:107`–`:113` carry a near-identical comment explaining why the recursive call cannot go in a `where`. That comment should live once, next to the lemma.

---

### F10 (medium, layering) — the primitive notions of this subsystem are defined in modules about something else

- `¬Nullable` — the most basic notion here — is defined in `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:45`, a module about guarded recursion for the Kleene star, and re-exported through `SequentialUnambiguity/Nullable.agda:26`. It has nothing to do with `*`.
- `char⁺` is defined in `src/Theory/Instances/Monoid/Greedy/Base.agda:31` and re-exported through `Nullable.agda:32`–`:33`. It has nothing to do with greedy matching.
- `startsWith` is defined in `First.agda:46`, *above* `Precise`, so `Precise.agda:148` has to re-spell it:
  > `-- \`startsWith g\`, spelled out so that this module need not name it`
  > `headed g d v r = two (g ∷ []) d , … `
- `disjoint` is pulled all the way from `Theory/Type/Unambiguity/Disjoint` into `First.agda:39`–`:40` and re-exported `public`, purely so `#→disjoint` can name its own conclusion.
- `Nullable.agda:9`–`:12` documents, rather than fixes, a duplication:
  > `NOTE: \`Automaton.Greedy\` independently states \`¬Nullable-map\`, \`⊕ᴰ-¬Nullable\`, \`char⁺-¬Nullable\` and \`¬Nullable→char⁺\`. … that file could import them from here instead.`

  In fact `Greedy.agda:38`–`:39` *does* import them from here now, so the NOTE is stale.

**Fix.** A single low module (extend `Strings.agda`, or a new `Theory/Instances/Monoid/Letters.agda`) holding `char⁺`, `startsWith`, `¬Nullable`, `stringSplit`, `FirstTy`, `FollowLastTy`, `_∉First_`, `_∉FollowLast_`, `_#_`, `_⊛_`. It sits below `Precise`, `KleeneStar`, `Greedy` and `Automaton`, which removes F4's fragility, F10's re-spelling, and most of the `public` re-export chains. Delete the stale NOTE at `Nullable.agda:9`–`:12`.

---

### F11 (medium, dead code)

All confirmed by repo-wide grep, zero uses outside the defining file:

| symbol | site |
|---|---|
| `trivialCover` | `src/Theory/Type/Cover/Base.agda:51` |
| `Covering`, `ofCover` | `src/Theory/Type/Cover/Base.agda:55`, `:64` |
| `Cases` | `src/Theory/Type/Cover/Base.agda:70` |
| `▷-tok` | `src/Theory/Instances/Monoid/Suffix/Base.agda:157` |
| `▷-tok⊗` (`= ▷-⊗r c`, a bare alias) | `src/Theory/Instances/Monoid/Suffix/Base.agda:172` |
| `module SufLex` (and with it the only use of `suffixWFOrder`) | `src/Theory/Instances/Monoid/Suffix/Base.agda:245`–`:265` |
| `⊗&-distL⁻` | `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:174` |
| `FollowLastTy-split` | `.../SequentialUnambiguity/FollowLast.agda:70` |
| `stringSplit⁻` | `.../SequentialUnambiguity/Nullable.agda:62` |
| `∉First*-notnull` | `.../SequentialUnambiguity/First.agda:168` |
| `#∘⊢2` | `.../SequentialUnambiguity/First.agda:136` |
| `&-¬NullableL`, `char⁺→¬Nullable` | `.../SequentialUnambiguity/Nullable.agda:42`, `:70` |
| `Δ≅→unambiguous`, `unambiguous→Δ≅` | `src/Theory/Type/Unambiguity/Disjoint.agda:94`, `:98` |
| `∉FollowLast→∉First` | `.../SequentialUnambiguity/FollowLast.agda:63` |

Two of these are worse than merely unused:

- `⊗&-distL⁻` (`Base.agda:174`) exists only as the would-be inverse of `⊗&-distL`, but they are never composed and no iso is stated. The old tree had `⊗&-distL≅` (`src/Grammar/SequentialUnambiguity/Base.agda:193`) — a strong equivalence. The port **lost the iso** and kept two disconnected maps with `⁻`-suffixed names implying one. Either restore the iso or rename to `⊗&-pair`.
- `SufLex` (`Suffix/Base.agda:245`) is described as "A drop-in alternative to `Lex`" — an unused alternative implementation is a maintenance liability, not a feature.

No `postulate`, `TERMINATING`, `trustMe`, `NON_COVERING`, holes, or commented-out blocks anywhere in the reviewed scope. Credit where due.

---

### F12 (low–medium, naming)

- `split-go` — `src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda:82`. A `go`. It is "the head-letter case analysis of `first⊗-split`"; call it `first⊗-split-onWord` or `splitHead`.
- `agree` — `src/Theory/Instances/Monoid/Precise.agda:172`. It refutes every non-trivial Levi case; `refuteOverlap` or `leviCases`.
- `main` — `src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:109`, `src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda:135`. Both are "assemble the roll-path from the tail path"; `rollPath`.
- `sp`, `eqP`, `tP`, `gP`, `Fam` — `Automaton/Unambiguous.agda:94`–`:117`, `KleeneStar/Unambiguous.agda:130`–`:148`. `splitsAgree`, `indexEqPath`, `tailPath`, `slotPath`, `TailTypes`.
- `N`, `D₀`, `W`, `S₁`, `S₂`, `Carrier` — `SequentialUnambiguity/Base.agda:319`–`:340`. `D₀`, `W`, `S₁`, `S₂` in particular are opaque; they are respectively "the cons-layer input", "the witness `(A ⊗ A*) ⊗ c…`", "empty prefix", "nonempty prefix". Name them.
- `flat` — `Precise.agda:36`. Says nothing; it flattens a splitting-with-literal-head to a cons-path. `splitToCons` or `headCons`.
- `pieces`/`parts` — `Base.agda:412` and `KleeneStar/Unambiguous.agda:118` are the same thing under two names.
- `Point` — `Cover/Base.agda:30` collides with `Theory/Type/Later/Indexed.agda:156`'s `Point` (a different thing: a family of global elements).
- **`_⊛_` means three different things** in `src/Theory/Instances/Monoid/`: sequential unambiguity (`SequentialUnambiguity/Base.agda:55`), the binary tensor of the signature (`GuardedSplit.agda:43`), and monoid multiplication (`ListPresentation.agda:56`). They do not currently collide in any single scope, but `SequentialUnambiguity/Nullable.agda:26` opens `KleeneStar/Guarded` publicly and `Guarded` itself has `GuardedSplit`'s `⊛` in scope — this is one `public` away from breaking. Rename `GuardedSplit._⊛_` to `_⊗ᴼ_` or `_⊙Ty_`.
- Stale "Grammar" vocabulary in files that otherwise say `Ty`/`TheoryTy`: `Nullable.agda:2` ("the split of any grammar by whether its word is empty"), `:65`–`:66` ("a non-nullable grammar is entirely its nonempty part"), `:76` ("a non-nullable grammar is refuted at ε"), `First.agda:151` ("two separated grammars"), `Suffix/Base.agda:175`–`:177` ("`▷` at this order, on grammars… a grammar *is* a family… nothing downstream names a family"), `Precise.agda:2` ("Precision of the token grammars"), `:80` ("refuting the suffix refutes the whole tensor" is fine, but `:79` "`literal c` is precise"). Also `Theory/Type/Subgrammar/Base.agda` is a whole module named "Subgrammar".

---

### F13 (low, comments) — changelog narration in source

Several headers and inline comments are commit messages that ended up in the file. They will be false within a release.

- `src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda:6`–`:9`:
  > `The old proof went through \`firstChar≅\` and \`same-first\` over \`A ⊗ string\` (~30 lines); here it is one match on the left factor's word…`
- `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:167`–`:168`:
  > `the old proof went through the external splitting trichotomy and two four-fold \`⊕ᴰ-elim\`s.`
- `src/Theory/Instances/Monoid/Precise.agda:160`–`:161`:
  > `This is the internal replacement for the old \`SplittingTrichotomy\`-based \`⊗&-distL≅\`.`
- `src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda:62`–`:63`:
  > `the \`PathP\`s are built inline, so no tensor-extensionality lemma is needed after all.` — and F9 argues one *is* needed.
- `src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:6`–`:8`:
  > `Proved by direct induction on the trace, not through \`Trace≅string\`… The induction is the one of \`Implicit/Disjointness\`'s \`TraceDisj\`, one level stronger`
- `src/Theory/Instances/Monoid/SequentialUnambiguity/Nullable.agda:9`–`:12` — the stale NOTE (F10).

None of these is chatty AI slop of the "restate the code" kind; the comment quality in this subsystem is generally good and several comments (`Precise.agda:33`–`:35` on why K forbids the match, `Precise.agda:41`–`:43` on `flatEq` vs `flat`, `Suffix/Base.agda:54`–`:55` on why `_◂_` is data) explain genuinely non-obvious steps. The fix here is narrow: move the "the old proof was…" sentences into the commit log.

**Non-obvious steps with no comment** (the reverse problem):

- `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:171`–`:172`: `⊗&-distL` passes `sepB sepC` into `⊗&-align`'s hand-unfolded hypotheses (F4). This is the single most fragile line in the subsystem and carries no comment at all.
- `src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda:105`–`:108`: the `subst` along `two-η` in `first⊗-split` — why the motive has to be that four-argument function, and why `two-η` is needed at all (splittings are `Fin 2 → String` with no η) — is unexplained here, though the fact is explained in `Convolution.agda:34`.
- `src/Theory/Instances/Monoid/Automaton/Disjoint.agda:52`–`:54`: `reState` transports a trace across `δ q d ≡ δ q c` and is the only place determinism is used; unremarked.

---

### F14 (low) — `--lossy-unification` is blanket, not targeted

137 of 191 files under `src/Theory` carry `{-# OPTIONS --lossy-unification -WnoUnsupportedIndexedMatch #-}`, including every file in this scope except `Theory/Type/Unambiguity/Base.agda`, `Theory/Type/Cover/Base.agda` and `GuardedSplit.agda`. So it is a project-wide convention rather than a specific slow definition being papered over, and I found no single definition it is masking. Recording it only so the maintainer knows: nobody can currently tell which files actually need it. Worth one experiment removing it from the three leaf modules of this subsystem (`Nullable.agda`, `FollowLast.agda`, `First.agda`) to see whether the convention has grown past its cause.

---

### F15 (low, conceptual) — the `Cover`/`disjoint` relationship claimed in the header does not exist in code

`src/Theory/Type/Unambiguity/Disjoint.agda:1`–`:3`:

> `-- \`disjoint A B\` is the binary case of a \`Cover\`'s \`disjoint\` field; it is`
> `-- stated separately because most clients only need two summands.`

Nothing in either file connects them: `Cover.Disjoint` (`Cover/Base.agda:34`) quantifies over an index with `Eq.≡ → ⊥`, `disjoint` (`Disjoint.agda:45`) is a bare `A & B ⊢ ⊥Ty`, and there is no `binaryCover : disjoint A B → Total … → Cover Bool …` anywhere. Either add that three-line bridge (which would also give `Cover` its only `Bool` instance and justify the claim) or delete the sentence.

---

### F16 (low) — import hygiene in the two largest files

`src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:32`–`:38` imports `Residual` twice (lines 32 and 35) and `Precise` twice (lines 34 and 37), and `⊗ε-unit-l⁻` (line 33) is never used in the file. `First.agda:20`–`:22` imports `_++_`, `Bool`/`true`/`false`, and `Cubical.Data.Sigma` — none used in the body.

---

## Summary of the recommended shape

1. New low module `Theory/Instances/Monoid/Letters.agda` (or a section of `Strings.agda`): `char⁺`, `startsWith`, `¬Nullable`, `stringSplit`, `FirstTy`, `FollowLastTy`, `_∉First_`, `_∉FollowLast_`, `_#_`, `_⊛_`. Kills F4, F10, most of F2.
2. Split `Precise.agda` into token precision + `Levi.agda`. Restate `⊗&-align` over `_⊛_`. Kills F7.
3. `opPathP2` in `Theory/Type/HLevels.agda`; rewrite `Automaton/Unambiguous` and `KleeneStar/Unambiguous` through it. Kills F9.
4. Decide F1: the automaton-side or the grammar-side FollowLast closure. Delete the loser.
5. Sweep F3, F8, F11, F16.
