# Comment & Naming Audit — grammars-and-semantic-actions

Scope: 371 `.agda` files under `src/` (`src/_build/**` excluded).
Method: exhaustive `grep`/`awk` extraction of every comment line, then read in
context. Raw extracts kept beside this file:
`theory-comments.txt` (2551 comment lines under `src/Theory`),
`other-comments.txt` (637 outside it), `short-labels.txt` (626 label/definition
pairs), `go-list.txt` (112 `go`-style helpers with their owning definitions).

**Caveat on line numbers.** Another agent was editing the tree throughout this
audit: 16 files went `M` mid-run, a `satG` → `satTy` rename landed, and
`Combinator/Decidable/STLC.agda` was split (from ~2000 lines to 1121), as was
`Type/SemanticAction/Base.agda` (its `module Suite` became
`Type/SemanticAction/Suite.agda`). Two new files appeared:
`Instances/Monoid/Pipeline/STLC.agda` and `Type/Decidable/DiscreteEq.agda`.

To handle this I took a second full snapshot of every comment line at the end
and compared it per-file against the first. Exactly five files' line numbers
had moved:

| File | Action taken |
|---|---|
| `Combinator/Decidable/STLC.agda` | all ~45 citations re-derived against the current file |
| `Automaton/GreedyExamples.agda` | all 6 citations re-derived |
| `Regex/UnicodeTests.agda` | 3 citations re-derived; one comment had moved into `Sat.agda` and is noted as such |
| `Instances/Monoid/Sat.agda` | re-derived (`satTy` now at `:28`) |
| `Type/Decidable/Route.agda` | re-derived |

Every other citation below was byte-identical across both snapshots. Two
findings were **already fixed by the concurrent agent** and are marked as such:
`satG` → `satTy`, and the extraction of `module Suite`.

## Headline counts

| | |
|---|---|
| Comment lines in `src/Theory` | 2551 |
| Comment lines outside it | 637 |
| Entries marked DELETE below | **308**, over 135 files (some cover a named group of 2-9 comments, so ~400 individual comment blocks) |
| Entries marked REWRITE below | 100 |
| Comments explicitly protected | 101 marked KEEP in place + 44 in the dedicated keep list |
| `go`/`go2`/`go3`/`go4`/`helper`/`foo`/`bar` local bindings | **117** (112 `go*`, in 28 files) |
| Vocabulary renames (`Grammar`/`Gr` → `Ty`) | **31** |
| Actively misleading names | 14 |

The slop is almost entirely inside `src/Theory/**`. The older `src/Grammar`,
`src/Automata`, `src/Thompson`, `src/Examples` trees are sparsely commented and
mostly human-voiced; only four entries below come from them.

## The house style that has to go

Nearly every comment in `src/Theory` is written in one recognisable register:

1. **`-- ...` continuation openers.** 151 occurrences. A comment that begins
   `-- ...and`, `-- ...so`, `-- ...or`, `-- ...at scale` is narrating a
   sequence of definitions as if it were prose. It is the single largest and
   most mechanical class of deletion.
2. **Label comments that restate the signature underneath.** `-- The syntax`
   above `data REB`, `-- The alphabet` above `data Tok`, `-- Monomorphisms`
   above `isMono`.
3. **Editorialising about the code's own history.** "the old proof went
   through…", "used to exclude…", "no `rec`, no pragma", "Existing users pass
   this and behave exactly as before", "kept for the contrast", "BENCH
   473108713".
4. **Benchmark tables pasted into source.** Six of them, with wall-clock
   seconds measured "off-tree" on an unnamed machine. These rot the day the
   machine changes.
5. **Multi-paragraph `{- -}` essays.** 80 files carry a block header longer
   than six lines. Many are re-stating the module's types in English.

---

# SWEEP 1 — DELETION LIST

Grouped by file, ordered by path. `→` marks the definition the comment sits on.

## src/Theory/Base.agda
- `59-62` — `-- this is a locally small wildcat / -- Currently its main use is to give access to a WildCatIso / -- record that recovers on the nose the notion of StrongEquivalence / -- used for Grammars` — **REWRITE**: keep the wildcat fact, drop "Currently its main use is" and the stale word "Grammars".
- `82` — `-- representables` → `⌈_⌉ : ∀ {s} → ↓M s → TheoryTy ℓM s` — **DELETE**: restates the name.

## src/Theory/Free/Base.agda
- `1-6` — `-- A presentation of the free model / -- This means we can choose a nicer presentation … / -- This is often advantageous. For example, we'd rather …` — **REWRITE**: keep the one sentence about list-vs-HIT indices; "This means…", "This is often advantageous" is filler.

## src/Theory/Free/Term.agda
- `1` — `-- Free model on a signature (i.e. a theory without equations)` — **KEEP** (see keep list; the parenthetical is the content).

## src/Theory/Instances/Bags/Sequence.agda
- `65` — `-- fold and case-split` → `recSeq` — **DELETE**: two words restating two definition names.
- `76` — `-- the ordinary list constructors, for building concrete arrangements` → `[]ᵍ` — **DELETE**.
- `85` — `-- the underlying list of an arrangement: forget every index` → `seqElements : Seq ⊢ K (List El)` — **DELETE**: the type says it.

## src/Theory/Instances/Bags/Sorted/Base.agda
- `73` — `-- the underlying list of a sorted arrangement: forget every index` → `elements : Sorted ⊢ K (List El)` — **DELETE**: verbatim duplicate of `Sequence.agda:85`.

## src/Theory/Instances/Bags/Sorted/HLevels.agda
- `24` — `-- a representable is prop-valued: it is an equality in a set` → `isSet⌈⌉` — **REWRITE**: the *reason* is worth a clause; the name is not.

## src/Theory/Instances/Bags/Partition.agda
- `28` — `-- an arrangement split in two, each half bounded by the pivot` → `Halves` — **DELETE**.
- `32` — `-- which side of the pivot a generator falls on` → `side : El → Bool → El → hProp` — **DELETE**.

## src/Theory/Instances/Bags/Generation.agda
- `35` — `-- combining two views: whichever side offers a generator gives one` → `joinView` — **DELETE**.
- `73` — `-- the fold puts every bag back where it started` → `fold-fst : (m : Bag) → fold m .fst ≡ m` — **DELETE**: the statement is shorter than the gloss.

## src/Theory/Instances/Bags/Join.agda
- `33` — `-- the pivot together with the sorted half above it` → `Pivot` — **DELETE**.
- `113` — `-- the join itself: two sorted halves around a pivot make a sorted whole` → `join : (Sorted & Below x) ⊎B Pivot x ⊢ Sorted` — **DELETE**: transliterates the type.

## src/Theory/Instances/Bags/Order.agda
- `138` — `-- opaque: its result is a bound, never something an answer is read from` → `opaque` — **REWRITE**: cut the leading `opaque:`, keep the reason.
- `160` — `-- a fold that is ⊤ at every generator is ⊤ everywhere` → `bagAll-⊤` — **DELETE**.

## src/Theory/Instances/Bags/Rank.agda
- `123` — `-- ... and splitting what the generator left: both halves are below it` → `▷-split` — **DELETE**: `...` continuation.

## src/Theory/Instances/Lambda/Signature.agda
- `2` — `-- Signature of Lambda ASTs` — **DELETE**: the module is named `Lambda.Signature`.

## src/Theory/Instances/Monoid/Automata/NFA/Base.agda
- `133` — `-- the labelled summand, named so its two directions can be stated` → `stepBranch` — **DELETE**: duplicated verbatim at `Automaton/Deterministic.agda:73`; "named so …" is an apology for a `where`-binding.

## src/Theory/Instances/Monoid/Automaton/Demo.agda
- `78` — `-- rule index and matched text, as text` → `lex : AS.String → Mb.Maybe (ℕ × AS.String)` — **DELETE**.
- `97` — `-- ...and it stops exactly where the rule stops, not at the end of input` → `_ : lex "42abc" ≡ Mb.just (2 , "42")` — **DELETE**: the test *is* the statement.
- `131-135` — `-- 3. At scale. / -- / -- Five automata in lockstep … Timings measured off-tree against a baseline …` — **DELETE**: unreproducible timing anecdote.
- `146` — `-- a 3200-character identifier, matched in one pass` — **DELETE**: `_ : len (Lex.lexOneS (xs 3200 ++ …)) ≡ 3200` says it.

## src/Theory/Instances/Monoid/Automaton/Deterministic.agda
- `73` — `-- the labelled summand, named so its two directions can be stated` → `stepBranch` — **DELETE**.
- `85` — `-- an algebra over the trace code, indexed as `rec` wants it` → `TraceAlg` — **REWRITE**: keep only "indexed as `rec` wants it".
- `111` — `-- Constructors: pick the tag, roll.` — **DELETE**.
- `196` — `` -- `parse`: the whole table, in one pass. `` — **DELETE**: `parse` is on the next line.
- `251-257` — the eight-line "Dead states." essay — **REWRITE**: the operative sentence is "a consumer that can test deadness refutes a run without inspecting one"; the recitation of `dead-empty`'s two clauses is a proof transcript.
- `268-269` — `-- the always-available one: nothing is known dead, and nothing is gained. Existing users pass this and behave exactly as before.` — **DELETE**: "Existing users … as before" is changelog, not documentation.

## src/Theory/Instances/Monoid/Automaton/Disjoint.agda
- `105` — `-- ...so the run of a word from a state is unique, bit and all.` → `Runs` — **DELETE**: `...` continuation; "bit and all" is chatty.

## src/Theory/Instances/Monoid/Automaton/Greedy.agda
- Whole file — **REWRITE**: it carries one comment line (the OPTIONS pragma) while `Automaton/GreedyExamples.agda:4-9` says elsewhere that `GreedyMax` "supersedes this scan in every respect ... If `Automaton/Greedy` is retired, this goes with it". Either delete the module or say so at its own top; do not leave the fact in a downstream examples file.

## src/Theory/Instances/Monoid/Automaton/GreedyExamples.agda
- `4-9` — `` -- `Automaton/GreedyMax` supersedes this scan in every respect -- its type says the match is maximal, and it is faster -- and … `` — **REWRITE**: the fact belongs in `Greedy.agda`, not here.
- `33` — `-- The greedy scan over that automaton.` → `munch` — **DELETE**.
- `40` — `` -- `a b*` on "abbab": the longest accepted prefix is "abb" `` → `_ : munch (a ∷ b ∷ b ∷ a ∷ b ∷ []) ≡ a ∷ b ∷ b ∷ []` — **DELETE**: transcribes the equation.
- `44-45` — `-- ...and it really is *maximal*: it does not stop at the first accepting state, which would give "a"` — **DELETE**: `...` opener + emphasis asterisks; duplicated verbatim at `GreedyMaxExamples.agda:42-43`.
- `52` — `-- nothing accepts here, so the scan reports no match rather than ε` — **DELETE**.
- `56-63` — the `n: 0 50 200 …` / `sec: 2.9 3.0 …` benchmark table — **DELETE**: measured "off-tree" on an unnamed machine.

## src/Theory/Instances/Monoid/Automaton/GreedyMax.agda
- `117` — `-- forget the end state, remembering only that it accepts` → `TraceTo→Trace` — **DELETE**.
- `132` — `-- ...and recover it.` → `Trace→TraceTo` — **DELETE** the `...and recover it.` sentence; **KEEP** the `Trace b q` unfolding that follows it.
- `177` — `` -- ...so the `⊕[ q' ]` of `BridgeTy` is a *singleton* sum `` → `endState` — **DELETE**: `...` opener.
- `228` — `-- a match: a run ending at an *accepting* state` → `Match : Q → Q → TheoryTy _ tt` — **DELETE**.
- `232-233` — `-- ...together with a refutation of every nonempty continuation …` — **DELETE**: `...` opener.
- `251` — `-- an accepting state's empty run, as a `Match` at itself` → `accHere` — **DELETE**.
- `285` — `-- extending the match is one `STEP`: O(1), and no derivative` — **REWRITE**: keep "one `STEP`", drop the O(1) editorial.
- `311-312` — `-- dead: the refutation comes from the certificate … Alive: exactly the old path.` — **DELETE**: "exactly the old path" is history.
- `368` — `-- ...and the bridge is an iso.` — **DELETE**: `...` opener.
- `396` — `-- the recursive call stands in the clause body, as in `Unambiguous`` — **KEEP** (see keep list).
- `469-476` — `-- Maximality, cashed in.` + seven lines — **REWRITE**: "cashed in", "which is what "longest" means" are voice; the `cancel` sentence is content.
- `496-497` / `501-503` — `-- ...and therefore the greedy branch …` / `-- the same fact spelled out.` — **DELETE**: two restatements of the theorem below them.

## src/Theory/Instances/Monoid/Automaton/GreedyMaxExamples.agda
- `26` — `-- the matched prefix: the left factor of the greedy witness' splitting` → `munch` — **DELETE**.
- `32` — `-- ...and the state it ended in, which the type now pins down` — **DELETE**.
- `38` / `42-43` / `50` — the three test-transcribing comments, duplicated from `GreedyExamples` — **DELETE**.
- `68-77` — the `n: 0 200 800 …` benchmark table, plus "i.e. the same shape as the unproved `GreedyAt` scan (0/200/800/3200/12800 = 2.9/3.0/3.4/5.1/12.3), slightly faster" — **DELETE**: two machines' worth of numbers cross-referencing each other.

## src/Theory/Instances/Monoid/Automaton/Implicit.agda
- `40` — `-- Freely adjoined states.` → `data FreelyAddInitial` — **DELETE**.
- `89` — `-- ...and the state sets are sets, which is all `parse` needs of them.` — **DELETE**: `...` opener.
- `116` — `-- The record, and its determinisation-free reading as a DFA.` — **DELETE**: restates `IDA→DA`'s type.

## src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda
- `112` — `-- union is `_++_`, and this is its contravariant half` → `memb-++-l` — **REWRITE**: "union is `++`" is worth one clause; "contravariant half" is not.
- `178` — `-- A `DetReg` together with the support of its two indices.` → `record DetOfB` — **DELETE**.
- `193-194` — `-- ...and this is the whole point: a total side condition out of one evaluated `Bool` plus the global disjointness.` — **DELETE**: `...` opener + "the whole point".
- `327-331` — `-- The analysis.` + the two-unit-clause explanation — **KEEP** the unit-clause reason (see keep list), **DELETE** the bare `-- The analysis.` label.
- `371-373` — `-- Getting the answer out. As with `Regex.Parse`'s `⟨|_|⟩`, …` — **REWRITE**: the type-error-at-use-site fact is real; "Getting the answer out" is not.

## src/Theory/Instances/Monoid/Automaton/Implicit/AnalysisExamples.agda
- `77` — `-- one position per literal, and nothing merged` → `_ : States … ≡ (Unit* Sum.⊎ Unit*)` — **DELETE**.
- `138` — `` -- `\d+`, i.e. `satr isDigit ⊗r satr isDigit *r` `` → `module M4 = POSIX "\\d+"` — **DELETE**: the module application already shows the pattern.
- `150-151` / `160-162` — `-- ...and a letter against a class, which *is* decidable` / `-- ...and at length, to check that the side conditions did not put anything expensive on the transition path.` — **DELETE**: `...` openers.
- `191` — `` -- `a|a` -- the same clash, at its smallest `` → `_ : Rejects "a|a"` — **DELETE**.
- `201` — `-- both branches nullable, which `⊕DR`'s `notBothNull` forbids` → `_ : Rejects "a?|b?"` — **KEEP** (names the constructor field that fails; not derivable from `Rejects "a?|b?"`).

## src/Theory/Instances/Monoid/Automaton/Implicit/Compile.agda
- `78` — `-- a decidable character class, as the set it denotes` → `⟦_⟧sat : (Alphabet → Bool) → ℙ` — **DELETE**.
- `58-61` — `-- `Cubical.Foundations.Powerset.More`, which the old `DetReg` used for `ℙ`, is not in this cubical …` — **REWRITE**: "not in this cubical" is worth a line; "which the old `DetReg` used" is history.
- `202` — `-- ...and outside the follow-last set never leaves an accepting one` — **DELETE**: `...` opener.
- `319-325` — `-- What the semantic layer consumes.` + "Nothing here mentions a grammar, so that port can land on top without touching this file." — **REWRITE**: the second half is a note-to-self about a future port.
- `335-336` / `343` — `-- ...and the DFA, by relabelling.` / `-- ...and its dead state, which is the freely added `fail`` — **DELETE**: `...` openers.

## src/Theory/Instances/Monoid/Automaton/Implicit/Disjointness.agda
- `48` — `` -- `A & -` commutes with a dependent sum, pointwise `` → `&⊕ᴰ-distR` — **DELETE**: the name says it.
- `62` — `` -- `sameHead` with the tails dropped `` → `same-first` — **DELETE**.
- `93` — `-- re-exported so that clients keep writing `fromCode M b q`` — **DELETE**: re-export bookkeeping.
- `164` — `-- Trace disjointness at this machine's underlying automaton.` → `TraceDisj` — **DELETE**.

## src/Theory/Instances/Monoid/Automaton/Implicit/RegExp.agda
- `57` — `-- one position, reached exactly by its own letter` → `litAut` — **DELETE**.
- `66-69` — `-- ...and a character class is the same automaton with a decidable predicate …` — **DELETE**: `...` opener; the follow-last fact is already at `Analysis.agda:206-207`.
- `76` / `98-99` / `124` — `-- Alternation: disjoint firsts, and not both nullable.` / `-- Concatenation: the left factor consumes, …` / `-- Star: the same condition against itself, …` — **REWRITE** as a single three-line table, or delete: each restates the side condition immediately below it.

## src/Theory/Instances/Monoid/Automaton/Implicit/RegExpExamples.agda
- `48` — `` -- `a b*`, as an implicit automaton. `` — **DELETE**.
- `93` / `100-101` — `-- accepted: `a`, and `a` followed by any number of `b`s` / `-- rejected, each for its own reason: empty, wrong first letter, …` — **DELETE**: transcribes the four `_ : Trace …` lines below.
- `114-124` — `-- ...at scale.` + the `n: 0 50 200 …` table + "~0.45ms/char … Linear." — **DELETE**.

## src/Theory/Instances/Monoid/Automaton/Implicit/Soundness.agda
- `71-72` — `-- Two maps plus unambiguity of both ends is an iso: this is the old `≈→≅`, and it is why the whole development can stay logical.` — **REWRITE**: keep the first clause, delete "this is the old `≈→≅`" and "why the whole development can stay logical".
- `90` — `-- The base cases.` → `module Leaves` — **DELETE**.
- `245` / `373` / `502` / `589` / `658` / `807` / `889` / `956` — `-- Into the alternation.` / `-- ...and back out of it.` / `-- The right factor, as what to do once the left one has accepted.` / `-- The left factor, in continuation-passing form.` / `-- ...and back: a trace of the concatenation splits at the join.` / `-- Splicing a further run in at an accepting state.` / `-- One iteration of the body, as a continuation.` / `-- ...and back: a run of the star is a list of runs of the body.` — **DELETE** the four `-- ...and back` openers, **KEEP** the two continuation-style ones (`502`, `589`) which name a non-obvious encoding.
- `1063` — `-- functoriality of the star, as a fold` → `map*` — **DELETE**.
- `1205` — `-- The theorem.` → `compile-sound` — **DELETE**.

## src/Theory/Instances/Monoid/Automaton/Implicit/SoundnessExamples.agda
- `30`, `37`, `44`, `53` — `` -- `true` ``, `` -- `true*` ``, `` -- `true false*` ``, `` -- `true | false` `` → `lit`, `star`, `seq`, `alt` — **DELETE** all four: the `DetReg` type on the next line spells the same expression.

## src/Theory/Instances/Monoid/Automaton/Lexicon.agda
- `174` — `-- The product automaton.` → `open DeterministicAutomaton` — **DELETE**.
- `191` — `-- the acceptance profile of a product state: which rules accept here` → `accAt : ProdQ → Fin n → Bool` — **DELETE**.
- `238` — `-- Maximal munch over the product = longest match across the lexicon.` → `scanProd` — **DELETE**: an `=` in prose restating a one-line definition.
- `242` — `-- the greedy run of the whole input, from the initial product state` → `runInit : ⊤Ty ⊢ Run Prod (init Prod)` — **DELETE**.
- `301` — `-- rule index, lexeme, remainder` → `tokAction : SemanticAction Tok (Fin n × String × String)` — **DELETE**: the tuple type says it.
- `312-313` — `-- ...observed at a word. This is the *only* place a `Maybe` appears, and it is the external one.` — **REWRITE**: drop the `...` opener and the emphasis, keep "the `Maybe` here is the external one".

## src/Theory/Instances/Monoid/Automaton/LexiconExamples.agda
- `61` — `-- One token: the winning rule's index, and the text it matched.` → `lexS : AS.String → Mb.Maybe (ℕ × AS.String)` — **DELETE**.
- `72` / `76` / `83` / `90` / `100` / `107` — six comments transcribing the six `_ : lexS "…" ≡ …` tests below them, two of them `...` openers — **DELETE** all six; the file's `{- -}` header already states the longest-match/priority rules.
- `139-150` — `-- ...at length.` + the `n: 50 200 800 …` table + "Only the 200 row is checked here; `Automaton/Demo` carries the 3200 one" — **DELETE**.

## src/Theory/Instances/Monoid/Automaton/Print.agda
- `50-51` — `-- ...and re-parsing a printed run returns it: both sides are maps into `Runs q`, which is a proposition.` — **REWRITE**: drop `...and`, keep the proposition argument.

## src/Theory/Instances/Monoid/Automaton/ScratchPerf.agda
- `52` — `-- OLD path: Greedy's scan, projecting the splitting by hand` — **DELETE**.
- `55` — `-- BENCH 473108713` — **DELETE**: a bare magic number with no unit and no referent. (The whole file is a scratch benchmark; see naming §d.)

## src/Theory/Instances/Monoid/Automaton/SuffixChain.agda
- `39` — `-- the proper suffixes of a word, nearest first` → `suffixes : SPt → List SPt` — **REWRITE**: keep "nearest first" (an ordering convention the type does not fix), drop the rest.
- `44` — `-- a proper-suffix witness *is* a position in that list` → `findSuf` — **DELETE**.
- `50` — `-- ...and dropping a letter extends the list by exactly one cell` — **DELETE**: `...` opener.

## src/Theory/Instances/Monoid/Automaton/TokenStream.agda
- `86-89` — `-- Comparing two prefixes of one word. Pure list arithmetic: …` — **REWRITE**: "Pure list arithmetic" is the only useful half.
- `106` — `-- a nonempty word is a `char⁺`, built rather than derived` → `char⁺-cons` — **DELETE**.
- `131-136` — `-- 1. The grammar.` + "The summand tag carries the winning rule …" — **REWRITE**: delete the numbered banner, keep the tag explanation.
- `165` — `-- one layer, as a sum of connectives rather than a code` → `StreamLayer` — **DELETE**.
- `181-182` / `204-205` / `449-450` — `-- 2. The tokenisation, read off the parse tree.` / `-- 3. The decision.` / `-- 4. ...and therefore a `Phase`.` — **DELETE**: numbered narrative banners; the last is also a `...` opener.
- `208` — `` -- `Match` forgets its end state and remembers that it accepts `` → `matchToL` — **DELETE**.
- `233` — `-- ...hence no token is empty, which is the whole payment` — **DELETE**: `...` opener.
- `258` — `` -- `GreedyMax`'s own `isSetMatch`/`isSetTable` are private there `` — **DELETE**: an apology for a duplicate definition; make the upstream ones public instead.
- `297-300` / `307-308` — the memoisation paragraphs — **KEEP** (see keep list).
- `368` — `-- ...and the mirror, when this match is the longer one` — **DELETE**.
- `409` — `-- nothing matches: the word is a stream exactly when it is empty` → `noneBranch` — **DELETE**.
- `441-442` — `-- the table is built once and then read twice, so it is threaded through the pair rather than named on both sides` — **KEEP**.
- `457` — `-- the display boundary. The `Maybe` is external, as in `Lexicon`.` — **DELETE**: third occurrence of "display boundary" as a label.
- `461-474` — `-- COST. Tokenising is linear. It took two things, both upstream of this file: …` + the `tokens: 40 80 160 …` / `before:` / `after:` table — **REWRITE**: the *mechanism* (dead-successor exit, `Lexicon.Tup` as a pair) is real and belongs; the before/after seconds are a commit message.

## src/Theory/Instances/Monoid/Automaton/TokenStreamExamples.agda
- `78` — `-- rule indices and lexemes, as text` → `toks` — **DELETE**.
- `83` — `-- one token, the way `Demo` reads it` → `lex1` — **DELETE**.
- `88-90` / `104` / `114-115` / `128-130` / `143` — the five numbered narrative banners ("1. The `wherever`/`where` pair comes out the same …", "2. Several tokens, which `lexOne` cannot say anything about.", "3. …", "4. …", "5. At scale: 19 tokens in one pass.") — **DELETE**: numbered essay over a list of `_ : … ≡ …`.
- `123-124` — `-- ...including when the failure is in the middle: …` — **DELETE**.
- `130` — `` --    interface that `dec : Decidable Gr` used to exclude. `` — **DELETE**: history, and it propagates the stale `Gr` name.

## src/Theory/Instances/Monoid/Automaton/Unambiguous.agda
- `45` — `-- the empty splitting is nullary, and its index equation is a proposition` → `isPropεTy` — **DELETE**: duplicated at `KleeneStar/Unambiguous.agda:87`.
- `55` / `61` / `66` / `71` — `-- stop / stop`, `-- stop / step`, `-- step / stop`, `-- step / step` → the four clauses that match exactly those patterns — **DELETE** all four: pure pattern transcription.
- `105` — `-- the line of types the two tails live over` → `Fam : I → Type ℓT` — **DELETE**.
- `125` — `-- ...i.e. `Trace b q` is unambiguous in the sense of `Unambiguity/Base`` — **DELETE**: `...` opener restating `unambiguousTrace`'s type.
- `129` — `-- and therefore subterminal: any two maps into it agree` → `subterminalTrace` — **DELETE**.

## src/Theory/Instances/Monoid/Backreference/Base.agda
- `32` — `-- A right factor that may read the left factor's parse.` → `Dep` — **KEEP** (see keep list).
- `84` — `` -- `⊗ᴰ` is functorial in its left factor, at a fixed indexed continuation. `` → `⊗ᴰ-mapL` — **DELETE**.
- `107` — `` -- `ε` determines its yield too: the empty string. `` — **DELETE**: "too" is narrative glue.

## src/Theory/Instances/Monoid/Backreference/Parser.agda
- `60` — `-- The publishing parser` → `Cont` — **DELETE**: labels a `Cont` definition with the name of a different concept.
- `93` — `-- Sequencing a capture group with what follows it` → `module _ {D : TheoryTy ℓD tt}` — **DELETE**.
- `172` — `-- Repetition at the publishing type` — **DELETE**.
- `174` — `` -- `ParserD` as a `TheorySet`, so it can sit under `▷` and be Löb'd. `` — **KEEP**.
- `193` — `-- A closed publishing parser is available at every suffix.` → `boxD` — **DELETE**: verbatim duplicate of `Combinator/Core.agda:370`.
- `230-232` — `-- ...and a parser for it: the fold over the captured string …` — **DELETE**: `...` opener.

## src/Theory/Instances/Monoid/Backreference/Regex.agda
- `37` — `-- Nullability (copied from `Regex.Base`)` → `data Nullability` — **REWRITE**: "copied from" is an admission of duplication; either import it or say why it cannot be imported.
- `57` — `-- The syntax` → `data REB : ℕ → Nullability → Type` — **DELETE**.
- `66` — `-- a capture group, scoping over everything that follows it` → `grpr` — **KEEP** (the scoping is not visible in `REB n ν → REB (suc n) ν' → REB n (ν ·ν ν')`).
- `68` — `-- ...and a reference back to one` → `brefr : Fin n → REB n nullable` — **DELETE**.
- `81` — `-- what the enclosing groups matched` → `Env : ℕ → Type ℓM` — **DELETE**.

## src/Theory/Instances/Monoid/Backreference/RegexTests.agda
- `32`, `46`, `63`, `74`, `85` — the five `` -- `(ab)\1` ``-style headers — **KEEP**: the `REB` term below them is unreadable without the regex source (see keep list).

## src/Theory/Instances/Monoid/Backreference/Stress/Common.agda
- `48` — `` -- `(a)(b)(a)(b)\1\2\3\4` `` → `fourRE` — **KEEP** (same reason).
- `73` — `-- ...referenced from outside: stresses `seqDᴰ` at depth` — **DELETE**: `...` opener.
- `119` — `-- ...and the same with the reference, still no trailing star.` — **DELETE**.

## src/Theory/Instances/Monoid/Backreference/StressTests.agda
- `35`, `39`, `43`, `47`, `51`, `55`, `59`, `63`, `67` — `-- CopyPos128`, `-- CopyNeg128`, `-- StarPos128`, `-- LitBack32`, `-- Deep15`, `-- TwicePos`, `-- TwiceNeg`, `-- AmbigPos20`, `-- AmbigNeg12` — **REWRITE**: these are *names* for nine anonymous `_ : matches … ≡ …` assertions. Bind each test to that name instead of commenting it. Nine deletions and nine bindings.

## src/Theory/Instances/Monoid/Combinator/Core.agda
- `46` — `` -- the grammar `Maybe` of `Types` shadows this one, so it stays qualified `` — **REWRITE**: `Types` is not the current vocabulary for that module's contents; keep the shadowing fact.
- `121` — `-- ...and the one-token cover is the instance the LL(1) parsers use.` — **DELETE**.
- `188` — `` -- `Lift` has η, so both round trips are `refl`. `` — **KEEP**.
- `195` — `-- the unit on the right, at the lifted `ε` a continuation carries` → `⊗ε↑-unit-r≅` — **DELETE**.
- `295` — `-- A parser for A turns answers about a grammar K into answers about A ⊗ K` → `Parser` — **REWRITE**: this is the module's central definition and deserves a comment, but not one that transliterates the type and says "grammar".
- `324` — `-- weakening the domain tag, uniformly in the tag it starts at` → `pw` — **DELETE**.
- `342` — `-- Combinators under an arbitray hypothesis D` — **DELETE** (also: typo "arbitray").
- `370` — `-- a closed parser is available at every suffix` → `box` — **DELETE**.
- `378` — `-- A parser under the hypothesis ⊤ is sufficent for answering about A` → `runP` — **DELETE** (also: typo "sufficent").
- `384` / `390` / `394` / `399` — `-- Build parsers as fixpoints` / `-- Call the hypothetical parser on a strictly smaller suffix` / `-- Guarded fixpoints build closed parsers` / `-- ...which are then used to answer` — **DELETE** the first, third and fourth; **KEEP** `390` (`call`'s "strictly smaller suffix" is the guard condition and is not in its type).
- `267-271` — `-- `AnswerFunctor` constrains types, not behaviour: an instance is free to define `Ans-≅ φ = <discard the answer>` and still typecheck. …` — **KEEP**.
- `522-524` — `-- What the laws buy: … which is the sentence this module's header asserts, now derived.` — **REWRITE**: drop the self-reference to the header.

## src/Theory/Instances/Monoid/Combinator/Decidable/Arrow.agda
- `263` / `301` — `-- Accepted` / `-- Refuted` — **KEEP** (two section markers over 12 tests; cheap and load-bearing).
- `268`, `272`, `276`, `281`, `285`, `290`, `295`, `306`, `310`, `314`, `318`, `325` — the twelve `-- (x) => x`-style source lines — **KEEP**: the `lp ∷ vid ∷ rp ∷ ar ∷ vid ∷ []` token lists are not readable otherwise.

## src/Theory/Instances/Monoid/Combinator/Decidable/Base.agda
- `72` — `-- the empty word carries no letter, hence no `char`` → `ε-char : Λ₁ ε₁ & (char ⊗ ty K) ⊢ ⊥Ty` — **DELETE**.
- `134` — `-- ...and so does `mapP`. This is where the three instances genuinely differ, which is why `Core` has no `mapP`.` — **REWRITE**: keep the second sentence, drop `-- ...and so does `mapP`.`
- `141` — `-- ...and a parser may only give up where there is nothing to decide.` → `fail` — **DELETE**.
- `149` — `-- ...which are then used to build deciders` → `decide` — **DELETE**. (Same sentence appears at `Incomplete/Base.agda:137` as "build tests" and `NonDet/Base.agda:173` as "enumerate": three copies of one joke.)
- `154` — `-- ...and the same for a family of nonterminals.` → `module FixAll` — **DELETE**.

## src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda
- `192` — `-- a bracket opened, then closed by the body itself` → `transp-open` — **DELETE**.
- `207` / `213` / `319` / `338` — `-- ...and what the classifier then says.` / `-- ...and for a word that swallows its own closing bracket` / `-- ...and a bracket closed by a following `)`` / `-- ...and the three class memberships a router needs.` — **DELETE**: four `...` openers in one file.
- `244` — `-- and the index is discrete, which is the other thing `PushOf` asks for` → `decClsEq` — **DELETE**.
- `260` — `-- the two carriers, as grammars` → `TranspG ClosG : TheoryTy ℓ-zero tt` — **DELETE**, and rename (see §b: `TranspG`/`ClosG`).
- `280` — `-- a letter that is not a bracket` → `tr-lit : (c : Tok) → NotBr c → literal c ⊢ TranspG` — **DELETE**.
- `117-119` / `148-150` / `226-234` — the `chase`/transparency/cover paragraphs — **KEEP** (see keep list).

## src/Theory/Instances/Monoid/Combinator/Decidable/Dyck.agda
- `28` — `-- Some tests running it` → `no-lp` — **DELETE**.

## src/Theory/Instances/Monoid/Combinator/Decidable/Lambda.agda
- `69` — `-- Every `Eq.refl` below is the parser running.` — **KEEP** (see keep list).

## src/Theory/Instances/Monoid/Combinator/Decidable/Lookahead.agda
- `42` — `-- Choice indexed by a cover` → `module Predictive` — **DELETE**.
- `57` — `-- the grammar the branches present: one summand per class` → `Alt` — **DELETE**.
- `73` / `118` / `123` — three `-- ...` openers — **DELETE**.
- `96` — `-- the whole use of the cover: `total` names the class, the class decides` → `commit` — **REWRITE**: drop "the whole use of the cover:".

## src/Theory/Instances/Monoid/Combinator/Decidable/Productions.agda
- `73` — `-- The table, as an indexed functor` → `itemCode` — **DELETE**.
- `123` — `-- ...and as a family of grammars` → `S : X → TheoryTy ℓG tt` — **DELETE**.
- `146` — `-- one summand per class, which is what `choose` decides` → `C` — **DELETE**.
- `164` — `-- the class sum and the ε-production are the two halves of the unrolling` → `rollAlt` — **DELETE**: the type shows both summands.
- `198` — `-- the leading terminal is where the step is paid for` → `prodP` — **KEEP** (names the guard payment, not in the type).
- `206` — `-- the ε-production, if there is one, and a refutation if there is not` → `nulP` — **DELETE**.
- `226` — `-- Reading the parse tree out` → `private` — **DELETE**.
- `232` — `-- the nonterminal items of a body, in order` → `kids` — **DELETE** (and rename `kids`, §a).
- `61` — `-- ...and which nonterminals derive ε` (trailing comment on `nul : X → Bool`) — **DELETE** the `...and`; keep "which nonterminals derive ε".

## src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda
- `110` — `-- the three nonterminals` → `data NT` with three constructors — **DELETE**.
- `237` / `247` — `-- types` / `-- terms` — **DELETE**.
- `302` — `-- how big those really are, as token lists` → `fib-size : length fibSrc ≡ 65` — **DELETE**.
- `311` — `-- the two languages do not accept each other` → `no-type-as-term` — **DELETE**.
- `338` — `-- The parse tree, as data.` → `open import Cubical.Data.Nat using (_+_)` — **DELETE**: the comment does not even label the line under it.
- `360` — `-- Pass 1: the concrete tree becomes an abstract one.` → `import Cubical.Data.Maybe as M` — **DELETE**: same problem.
- `554` / `601` / `664` / `814` / `1084` / `1107` — six `-- ...` openers (`-- ...run on the two programs.`, `-- ...and a few more type errors`, `-- ...and the decision, one clause per former`, `-- ...and so, every binder being annotated, is the typing`, `-- ...but bound under a binder that binds it`, `-- ...and refutations of *every* derivation, which is what completeness buys`) — **DELETE**.
- `115` / `122` / `129` — the three BNF lines (`-- A ::= bool | nat | arr A A | …`) — **KEEP**: the `Table.at` clauses below them are not readable as a grammar.

## src/Theory/Instances/Monoid/Combinator/Decidable/Widths.agda
- `41` — `` -- The two lookahead windows, at width `k+2`. `` → `aFill` — **DELETE**.
- `51` — `-- The grammar, indexed by the width` → `data NT` — **DELETE**.
- `136` — `-- Bodies, and the one unrolling. Both are inductions on the width.` — **REWRITE**: keep "inductions on the width".
- `180` — `-- every body begins with `a`, which is one unrolling` → `firstS : Lang St ⊢ literal ta ⊗ ⊤Ty` — **DELETE**.
- `201` — `` -- The route, at width `k+2`, and the parser. `` — **DELETE**.

## src/Theory/Instances/Monoid/Combinator/Grammars/Arith.agda
- `36` — `-- a literal, relabelled to the lifted `literal` the grammar's body uses` → `tokL` — **REWRITE**: keep "relabelled to the lifted `literal`".

## src/Theory/Instances/Monoid/Combinator/Grammars/ArithGrammar.agda
- `28` — `-- The alphabet` → `data Tok` — **DELETE**.
- `51` — `-- The grammar` → `data NT` — **DELETE**: and it is wrong — `NT` is the nonterminal set, not the grammar.
- `151-153` — `-- The route. `rExp` is the LL(1) table for `Exp` … both answer-free, which is the point: a table is a table at every answer.` — **REWRITE**: "which is the point" appears four times across `Combinator/**`; say it once, in `Core`.

## src/Theory/Instances/Monoid/Combinator/Grammars/ArithTests.agda
- `40` — `-- One parser, three answers.` → `decArith` — **DELETE** (also at `DyckTests.agda:33`, `PolynomialTests.agda:47`, `RegexTests.agda:48`: four copies).
- `84-85` — `-- ...and the same list at `ND`, where a `just` becomes a one-element enumeration …` — **DELETE**.

## src/Theory/Instances/Monoid/Combinator/Grammars/Dyck.agda
- `33` / `37` — `-- what the inner `S` is followed by` / `-- what a `(` is followed by` → `afterS`, `afterLp` — **DELETE**: the names already say it.
- `44` / `48` / `52` — `` -- `) S` ``, `` -- `S ) S` ``, `` -- `( S ) S` `` — **KEEP**: the production each parser recognises is not visible in `Parser ℓG ⟨▷⟩ ⟨□⟩ afterS`.

## src/Theory/Instances/Monoid/Combinator/Grammars/DyckTests.agda
- `33` — `-- One parser, three answers.` — **DELETE**.
- `76` — `-- exactly one parse each: the enumeration witnesses unambiguity` → `nd-trees` — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda
- `169` — `-- the continuation level: the one `μ` lands at` → `ℓG : Level` — **DELETE**.
- `254` — `-- ...and `Q`'s, which are `K`'s but for the denominator` — **DELETE**.
- `511` — `-- The tables themselves.` → `rE` — **DELETE**.
- `537-539` — `-- ...and the routes they induce. `into` is always the same three steps: …` — **REWRITE**: the three steps are content; the `...and` is not.
- `403-406` — `-- ...and the three grammars carrying their h-level … From here on it is `seq`, `tok`, `_<|>_`, `nil`, `call` and `fix`, as in `Dyck`: …` — **DELETE**: a table of contents for the rest of the file.
- `180` / `189` / `198` — the three BNF lines — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/Grammars/Polynomial.agda
- `70` — `-- the three `K`-heads, shared with `Q`` → `addP` — **DELETE**.
- `80` — `-- the ε-production, the one branch no route names` → `stopP` — **KEEP** (the "no route names it" fact is the design point).
- `96` / `100` — `` -- `) K` ``, `` -- `E ) K` `` — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/Grammars/Regex.agda
- `69` — `-- The parse tree an expression admits: the expression's own shape.` → `Tree : Reg t → Type ℓAlph` — **REWRITE**: keep the second clause only.

## src/Theory/Instances/Monoid/Combinator/Grammars/RegexTests.agda
- `48` — `-- The expressions. Written once, at no answer at all.` — **DELETE**.
- `56` / `115` — `-- ...and the same compiler at three answers.` / `-- ...and the leftmost of that fan is what the other two commit to.` — **DELETE**.

## src/Theory/Instances/Monoid/Combinator/Incomplete/Base.agda
- `137` — `-- ...which are then used to build tests` — **DELETE**.
- `103-106` — `-- Both derived, and both by discarding: … So a `Maybe` parser *can* be routed -- it just does not learn anything from the route that `_<|>_` would not also have found by trying.` — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/Incomplete/Dyck.agda
- `25` — `-- Sound but not complete: `nothing` is a refusal, not a refutation` → `testDyck` — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/NonDet/Base.agda
- `39` — `` -- `Types` hides this `Δ` in favour of the one from `Strings` `` → `open import …` — **DELETE**: import bookkeeping.
- `82` / `130` / `146` / `152` / `173` — five `-- ...` openers — **DELETE**.
- `70-72` — `-- The strength. `A` is used once per element of the list, which is legal because the list's `&` shares the string …` — **KEEP**.

## src/Theory/Instances/Monoid/Combinator/Syntax.agda
- `35` — `-- NOT public: `Reg`'s constructors would collide with other regex syntaxes` — **KEEP**.
- `42` — `-- Repetition.` → `module _ (ℓK : Level)` — **DELETE**.
- `61` / `68` / `74` — `` -- `A ⁺` ``, `` -- `p?` ``, `` -- `l p r` `` → `some`, `option`, `between` — **DELETE**: the names already say it (unlike the Dyck/Polynomial cases, where the name does not).
- `112` — `-- ...and the answer, at whatever `𝒯` is.` — **DELETE**.
- `92-95` — `-- Regular expressions, compiled to parsers. This is the counterpart of `Thompson.Base`'s `regex→NFA` …` — **KEEP**.

## src/Theory/Instances/Monoid/Convolution.agda
- `74` — `-- The nullary convolution, which mentions no slot family at all.` — **REWRITE**: keep "mentions no slot family"; drop the label.
- `87` — `-- ...so `map` at a nullary summand carries no information.` — **DELETE**.

## src/Theory/Instances/Monoid/Derivative.agda
- `55` — `` -- The character-level names from `Grammar.Derivative.Base`. `` → `Dr` — **REWRITE**: it points at the *old* tree, i.e. it is a migration note (see §b).
- `68-71` — `-- ...spelled with a cons rather than through `Dl-string-map`, so the index stays syntactically a cons …` — **KEEP** the reason; **DELETE** the `...` opener and the last sentence about `Regex/Derivative` keeping its own copy (that is a duplication apology).

## src/Theory/Instances/Monoid/Derivative/General.agda
- `43` — `-- The two formers, and the adjunction between them.` → `opaque` — **DELETE**.
- `46` / `50` — `-- sss-00PP` / `-- sss-00PR` — **KEEP**: these are forest tree IDs; they are the only external anchors in the file. (But they should be a consistent `-- see sss-00PP` form; the bare id reads as noise.)
- `90` — `-- Everything below uses only the adjunction.` — **KEEP**.
- `120` — `-- reindexing the weight, from `√-reweight` above` → `∂-weight` — **DELETE**.
- `149` — `-- ...and the residual, which agrees only here` — **DELETE**.

## src/Theory/Instances/Monoid/Extension.agda
- `211` — `` -- `⊗ₑ` against the raw two-slot tensor, and against `⌈ εᵖ ⌉`. `` — **DELETE**.
- `227` — `-- The unitors.` → `⊗ₑ-unitL⁻` — **DELETE**.
- `267` — `-- The residual, right adjoint to `_⊗ₑ_` in its second argument.` — **KEEP**.
- `286` — `-- Constant grammars, and how `⊗ₑ` and `⊕ᴰ` pass through them.` → `K` — **REWRITE**: "Constant grammars" → constant types (§b).

## src/Theory/Instances/Monoid/Grammars/Dyck.agda
- `18` — `-- the alphabet: one bracket pair` → `data Br` with `lp`/`rp` — **DELETE**.
- `147-148` — `-- ...so `rollS`/`unrollS` is an isomorphism, and a parser for `S` transports along it …` — **DELETE**: `...` opener.
- `168` — `-- ...and the tree a parse denotes` → `semactS` — **DELETE**.
- `74-78` / `111-113` — the `nodeIn`/`nodeOut` and inverse paragraphs — **KEEP** the naming reason; **DELETE** "so everything downstream still computes at `refl`-time" (history of a refactor).

## src/Theory/Instances/Monoid/Greedy/Base.agda
- `29` — `-- one or more characters` → `char⁺` — **DELETE**.
- `51-54` — `-- `no-nonempty-extension-step` of `Grammar/Greedy/Regex.agda` (a hole there) with the automaton removed: …` — **REWRITE**: a diff against a file in the old tree. Say what the lemma is, not what it was ported from.
- `65` — `-- the `char⁺` witness splits the matched prefix` → `pl = t .snd .snd .fst .snd` — **KEEP**: this is a projection chain, and the comment is the only readable thing about it. (Better: name the projection, §a.)
- `115` — `-- one character, O(1)` → `extendAt` — **DELETE**.
- `120` — `-- ...and what it gives up: the prefix parse` → `GreedyAt→prefix` — **DELETE**.

## src/Theory/Instances/Monoid/Greedy/Examples.agda
- `47-51` — `-- 1. A greedy match: `a+` against "aaab". / -- / -- The match is "aaa" and the rest is "b". It is greedy because of …` — **REWRITE**: keep the "because of the second component" sentence; drop the numbered banner and the restatement of the test.
- `56` / `63` / `91` / `98` — `-- what is left of `a+` once it has matched: the residual` / `-- the match itself, decided rather than asserted` / `-- ...and what it matched, read back out` / `-- the parse tree agrees with the splitting` — **DELETE**.
- `102-108` — `-- 2. Extending a match, one character at a time.` + "…which is exactly the case that hid a stuck `transp` here once." — **REWRITE**: the stuck-`transp` warning is real; "hid … here once" is anecdote.
- `122` — `-- n applications of `extendAt`, each O(1)` → `go` — **DELETE** (and rename `go`, §a).
- `139-141` — `-- 200 characters into the match, and the transported witness still projects: …` — **DELETE**.

## src/Theory/Instances/Monoid/GuardedSplit.agda
- `58` — `-- ... and what it gets: the hypothesis alongside the right slot` → `▷⊛r` — **DELETE**.
- `52-53` — `-- what a caller owes to read the hypothesis at the right slot: …` — **KEEP**.

## src/Theory/Instances/Monoid/KleeneStar.agda
- `104-105` — `-- Every word is a list of characters: `Strings.read` at the star rather than at `String*`. This is how an input is presented to a fold.` — **REWRITE**: the last sentence is filler.
- `134` — `` -- `roll*`/`unroll*` against `εTy` rather than the code's lifted one `` → `roll↑` — **KEEP**.
- `167` — `-- ...so a parser relabels along an isomorphism, not a mere pair of maps.` — **DELETE**.

## src/Theory/Instances/Monoid/KleeneStar/Guarded.agda
- `72` — `-- ...and the mirror, for a nullable head with a non-nullable tail` → `⊗-¬NullableR` — **DELETE**.
- `94-95` — `-- ...and the bridge. A head that is an `A` cannot be `[]`, so what follows it is a *proper* suffix.` — **REWRITE**: keep the second sentence.
- `106` — `-- the family being fixed: the fold itself, as an internal function` → `Fam` — **DELETE**.
- `118` — `-- the delayed fold reaches the tail because the head was paid for` → `step` — **DELETE**.
- `125` — `-- ...and Löb closes it. One combinator, no pragma.` → `fold*g` — **DELETE**: "One combinator, no pragma" is a boast about the diff.
- `129-134` — `-- The two star actions, by löb. `SemanticAction.semact-*` and `semact-skip*` are `rec`, so the pragma sits under every action; these are the same folds with `fold*g` underneath. / -- / -- The price is `isSet X`: …` — **REWRITE**: keep "The price is `isSet X`"; the rest compares against the code it replaced.

## src/Theory/Instances/Monoid/KleeneStar/GuardedTests.agda
- `29` — `-- the client states non-nullability internally, and never sees the order` → `nn` — **KEEP**.
- `33` — `-- the fold, by guarded recursion` → `len` — **DELETE**.
- `41` — `-- ...and it computes` → `_ : countAs [] ≡ M.just 0` — **DELETE**.

## src/Theory/Instances/Monoid/KleeneStar/Map.agda
- `44` — `-- A retraction of the elements is a retraction of the lists.` → `module _ …` — **DELETE**: restates `*Retract`'s type.
- `90` — `-- ...so an isomorphism of elements is an isomorphism of lists.` → `*≅ : (A *) ≅ (B *)` — **DELETE**.

## src/Theory/Instances/Monoid/KleeneStar/Read.agda
- `57` — `-- ...so `readChars` is *the* list of characters of a word.` → `readChars-section` — **DELETE**.

## src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda
- `46-47` — `` -- `∀ m → isProp (A m)`, as `Theory/Type/Unambiguity/Base` states it; named locally because that module reaches here by two paths. `` — **REWRITE**: an import-cycle apology; fix the cycle or say so in one clause.
- `59-63` — `-- The proof. `A *` is a real `data`, so both arguments are matched as … -- no `rec`, no pragma. This is `Automaton/Unambiguous`'s `unambiguous-Trace` technique; the `PathP`s are built inline, so no tensor-extensionality lemma is needed after all.` — **REWRITE**: keep the structural-descent fact; "no `rec`, no pragma", "after all" are diff commentary.
- `87` — `-- the nil layer is nullary, and its index equation is a proposition` → `isPropNil` — **DELETE**.
- `96` / `99` / `103` — `-- nil / nil`, `-- nil / cons`, `-- cons / nil` — **DELETE**: pattern transcription.
- `107-109` — `-- cons / cons. The recursive call stands in the clause body: through a `where` binding the checker compares the tail against the parameter rather than against the constructor pattern, and loses the descent.` — **KEEP** the second half (see keep list), **DELETE** the `-- cons / cons.` label.

## src/Theory/Instances/Monoid/Lex/Base.agda
- `35` — `-- the token stream grammar: a repetition of whatever one token is` → `Tokens` — **DELETE**.

## src/Theory/Instances/Monoid/Lex/Regex.agda
- `36` — `-- one token` → `tokenRE` — **DELETE**.
- `40` — `-- ...and the stream, which is the lexer's grammar` → `tokensRE` — **DELETE**.
- `49` — `-- the tokenisation itself, when there is one` → `Tokenisation` — **DELETE**.
- `56-61` — `-- Reading the tokenisation back out. / -- / -- This is the bridge to the next phase, not part of lexing: the tree already *is* the answer, and these just display it. …` — **REWRITE**: keep the "not part of lexing" boundary claim; the rest paraphrases `yield` and `which`.
- `77` — `-- which rule matched, and what it took` → `which : … SemanticAction … (ℕ × List Alphabet)` — **DELETE**.

## src/Theory/Instances/Monoid/Lookahead/Base.agda
- `29` — `-- The fibres of the classifying map Σ* ↠ M₁.` → `Λ₁` — **KEEP**.
- `88` — `-- the empty string is decidable: the lookahead cover already decides it` → `dec-ε` — **DELETE**.

## src/Theory/Instances/Monoid/Lookahead/Window.agda
- `33` — `-- the lookahead width, as a unary numeral` → `data Width` — **DELETE**.
- `43` — `-- a word of length at most n: the input, truncated to a n-token window` → `data Window` — **DELETE**.

## src/Theory/Instances/Monoid/Phase.agda
- `2-47` — the 46-line `{- -}` header — **REWRITE**. Keep: the argument that lexing is not a theory morphism (paragraphs 2-3), and gaps 2 and 3. Delete: gap 1, which begins `1. CLOSED. `dec : Decidable Gr` used to exclude the greedy lexer -- the one thing this interface exists to feed -- because …` — a closed issue, i.e. a changelog entry, and the longest single item in the header.
- `73` — `-- A phase.` → `record Phase` — **DELETE**.
- `77` / `79` / `81` — `-- what this phase recognises, over *this* alphabet` / `-- ...decided, so a failure is a refutation and not a dropped error` / `-- ...and what it hands the next phase: a word over the next alphabet` → the record's three fields — **REWRITE**: three field comments, two of them `...` openers, on three fields whose names should carry this instead (see §b: `Gr` → `Ty`).
- `85-89` / `95-100` — `-- Running one.` / `-- A canonical semantic action, for readable tests.` + explanations — **REWRITE**: delete the labels, keep "the only place a parse becomes metalanguage data" and "a test can only print what the grammar actually says".

## src/Theory/Instances/Monoid/Phase/Display.agda
- `37-38` — `------…------ / -- The instances.` — **DELETE**: banner + label.
- `57` — `` -- `AS.String` is a monoid too; this is its fold. `` → `cat` — **DELETE**.
- `69` / `73` / `77` / `81` / `88` / `94` / `106` — the seven per-instance one-liners (`-- ε prints as nothing at all.`, `-- a literal prints as its own letter …`, `-- ...and `char` reads the letter the parse selected`, `-- concatenation, at the splitting the tensor already carries`, `-- whichever side of the sum the parse is on`, `-- the star is the fold of the pieces, in order`, `-- nothing to print, vacuously`) — **DELETE** all seven: each restates `Display-εTy`, `Display-lit`, `Display-char`, `Display-⊗`, `Display-⊕`, `Display-*`, `Display-⊥Ty`.
- `122-133` — `-- The dependent sum. / -- / -- NOT an instance. Two reasons, both real: …` — **KEEP** (see keep list).
- `139` / `157-159` — `-- ...and the tagged version …` / `-- ...and the same for a decision …` — **DELETE**.
- `149` — `-- the resolved record itself, for the places that need to hand it on` → `theDisplay` — **DELETE**.
- `189-190` — `------…------ / -- Demo.` — **DELETE**.
- `222` — `` -- `a (b|c) d*` `` → `Alt Ds Tail G : TheoryTy _ tt` — **KEEP**.
- `242` — `-- The point of the file: no projection out of `parse` appears here.` — **REWRITE**: "The point of the file" appears twice in this file; state it once at the top.
- `246` / `254` / `258` / `270` — `-- the other summand, same printer` / `` -- `⊤Ty` prints its index, through `read`. `` / `` -- `char *`, resolved from `Display-char` and `Display-*` `` / `` -- `String*`, whose instance is bespoke because it is a `μ` `` — **DELETE** the first three; **KEEP** the fourth (the `μ` reason is the one at 114-118).
- `296-301` — `-- ...and the same class on a real regex parse. / -- / -- `decide-r` produces the parse; nothing below projects out of it. The instance for `ty ⟦ ident ⟧` is assembled from `Display-satTy`, `Display-⊕`, `Display-⊗`, `Display-lit` and `Display-*`.` — **DELETE**: the assembly list is exactly what instance resolution does and will go stale.

## src/Theory/Instances/Monoid/Pipeline/Dyck.agda
- `29-42` / `44-49` / `71-72` / `77-82` / `100-101` — the five `---------` banners with `-- 1. The token alphabet.` … `-- 5. It runs.` — **REWRITE**: five numbered banners in a 150-line file. Keep the substantive halves (the `Br`-not-a-fresh-datatype reason at `35-40`; the "two failures stay apart" reason at `80-82`); delete the numbering and rules.
- `103` / `113` / `117` / `130` / `148` — `-- The lexer alone: brackets kept, whitespace dropped.` / `` -- `[` is in no rule, so the lexer refutes every tokenisation. `` / `-- End to end.` / `-- Whitespace changes nothing but the source text.` / `-- deeper, and with the whitespace rule firing repeatedly` — **DELETE**: five comments transcribing five `_ : pipeline "…" ≡ …` lines.
- `17` — `-- re-exports `isSetAlphabet`, so `Phase` below is at the same instance` → `open import …` — **KEEP** (an instance-resolution hazard).

## src/Theory/Instances/Monoid/Precise.agda
- `90` — `-- ...and so is `char`, which fixes the splitting without fixing the letter` → `char⊗-precise` — **REWRITE**: keep the parenthetical distinction, drop `...and so is`.
- `101-103` — `-- Two more consequences of the same precision, both used wherever two one-step unrollings are compared: …` — **REWRITE**: "Two more consequences" is a running count; name the two facts.
- `133` — `-- Levi's lemma, and the alignment of two splittings that it powers.` — **KEEP**.
- `159-161` — `-- … This is the internal replacement for the old `SplittingTrichotomy`-based `⊗&-distL≅`.` — **DELETE** the last sentence: history.
- `189-190` — `-- The two cuts coincide. This is the whole content; `⊗&-align` below repackages it as a term, and `unambiguous⊗` needs it as a path.` — **REWRITE**: drop "This is the whole content".

## src/Theory/Instances/Monoid/Regex/Base.agda
- `152-156` — `-- Nullability is decided, and the index is what decides it. / -- / -- `re-¬Nullable` above gives one direction. With the other, the syntactic index is not bookkeeping: it answers the semantic question "does this regex match the empty word", correctly, for every regex.` — **REWRITE**: the first sentence is enough; the rest is a victory lap.
- `172` — `-- ...so the two together are a decision, with no case left open.` → `decNullable` — **DELETE**.

## src/Theory/Instances/Monoid/Regex/Derivative.agda
- `66` — `-- The derivative itself` → `δ` — **DELETE**.
- `99-104` — `-- The smart constructors do not change the language. … / -- ...so these are all the identity, and the theorem below never has to ask what a constructor did.` — **REWRITE**: keep the first sentence; delete the `...so` continuation, which repeats it.
- `132` — `` -- `Dl` across the connectives. `` → `private variable ℓA ℓB : Level` — **DELETE**: labels the wrong line.
- `138` / `149` / `156` / `163` — `-- forget which side the split fell on` / `-- ...and put it back, on the left` / `-- ...or on the right, which costs a witness that `A` accepts ε` / `-- when `A` cannot be ε the split must be `c`-headed` → `Dl-⊗-out`, `Dl-⊗-in-l`, `Dl-⊗-in-r`, `Dl-⊗-out!` — **DELETE** the first two (names say it); **KEEP** the third and fourth (the ε-witness cost and the `!` convention are not in the names).
- `181` — `-- a map of grammars acts on derivatives by applying it one letter in` → `Dl-map` — **REWRITE** ("map of grammars" → map of types, §b).

## src/Theory/Instances/Monoid/Regex/Examples.agda
- `43` — `-- ...displayed as text, so a case reads as text in, text out` — **DELETE**.
- `49` / `96-97` / `128` / `153-156` — `-- 1. Each regex is named once; the table says what it consumes.` / `-- 2. A lexer is a lexicon of those. …` / `-- ...and the tokenisations, written out.` / `-- 3. The same answers taken directly instead of through `observe`. …` — **REWRITE**: numbered narrative; the `⊕ᴰ`/refutation content in item 3 is worth keeping, the numbering is not.
- `137-143` — `-- NOT maximal munch, and this file is kept for the contrast. `where` is tried before the identifier rule and wins on a prefix, so "wherever" splits; a greedy lexer gives `Ident "wherever"`, and `Automaton/Demo` does exactly that on the same five rules. The ordered-choice path has never been rewired onto the automaton scan, so the case stays here, and stays wrong, as the record of what first-match costs.` — **REWRITE**: this is a **known-wrong test kept deliberately**, which is important, but it is buried in seven lines of apology. Reduce to two lines and give the test a name that says it (`wherever-first-match-splits`).
- `164` — `` -- `?` is in no rule, so *nothing* tokenises this input `` → `noq : NoTokenisation lexicon (text "x?")` — **DELETE**: the name says it.

## src/Theory/Instances/Monoid/Regex/Notation.agda
- `39` / `43` / `50` / `71` / `83` — `` -- `[abc]` ``, `` -- `[^abc]` ``, `` -- `r?` ``, `` -- `"abc"` ``, `` -- `r{n}` `` → `oneOfr`, `noneOfr`, `_?r`, `strr`, `repr` — **KEEP**: these map surface regex syntax onto the combinator names and are the file's whole point.
- `59` — trailing `-- no trailing `⊕r ⊥r` to explore` on `anyOfr (r ∷ []) = r` — **KEEP**.
- `93` — `` -- `r{n,m}` -- n copies, then up to  more `` — **REWRITE**: has a literal typo (a missing word after "up to", double space).

## src/Theory/Instances/Monoid/Regex/Parse.agda
- `69` — `-- A parser of characters, in the metalanguage` → `private` — **DELETE**.
- `90` — `-- what may not stand for itself` → `special : List AC.Char` — **DELETE**.
- `123` / `161` / `256` — `-- Escapes and the named classes` / `-- Bracket expressions` / `-- The entry point` — **DELETE**: three section labels on `private` blocks.
- `280` — `-- ...and its two projections` — **DELETE**.
- `272-273` — `` -- `⟨| "[a-z]+" |⟩` -- a malformed pattern is a type error here, because `IsJust nothing` is uninhabited and `Unit` is solved by eta. `` — **KEEP**.

## src/Theory/Instances/Monoid/Regex/ParseTests.agda
- `38` / `58` / `84` / `107` — `-- concatenation, alternation, star` / `-- postfix operators` / `-- classes, ranges, escapes` / `-- the ones a real lexicon is made of` — **DELETE**: four section labels over `_ : Yes "…" "…"` lines that already show which feature is exercised.

## src/Theory/Instances/Monoid/Regex/Tests.agda
- `31`, `45`, `59`, `85`, `106`, `128`, `141`, `151`, `161`, `177` — the ten `` -- `a b` ``-style headers — **KEEP**: each names the regex the `RE` term below encodes.
- `122` — `` -- `anyr` still works, now as a definition `` — **DELETE**: "still works, now as" is changelog.
- `2` — `-- The regex parser runs: every case is `decide-r` on a written regex.` — **KEEP**.

## src/Theory/Instances/Monoid/Regex/Unicode.agda
- `63` / `67` / `87` / `93` / `114` / `118` — the six syntax headers — **KEEP** (same reason as `Notation.agda`).

## src/Theory/Instances/Monoid/Regex/UnicodeTests.agda
- (was `61`) `-- the letter a `satr` matched, read back out` → `satChar` — **ALREADY GONE**: a concurrent edit moved this to `Instances/Monoid/Sat.agda:35` as `-- The letter that was matched, read back out. …`; the surviving comment is still a restatement — **DELETE** it there.
- `61` — `-- head and tail of the identifier` → `identChars : SemanticAction … (UChar × List UChar)` — **DELETE**.
- `107` — `-- a literal word, and `[0-9]{2,4}`` → `kw : RE notNullable` — **REWRITE**: the comment describes two definitions, only one of which follows.

## src/Theory/Instances/Monoid/Residual.agda
- `59` — `-- ...and this is the only thing the two transposes' β laws are missing.` → `⊗-split-η` — **DELETE**.
- `108` — `-- contravariance in the thing still wanted: every dot movement is this` → `⟜-precomp` — **DELETE**: "every dot movement is this" is unexplained jargon.
- `129` — `-- a residual that wants nothing more is what it produces` → `⟜-unitr : C ⟜ εTy ⊢ C` — **DELETE**.
- `192` — `-- feeding the left slot at the unit: this is how a parser is started` → `⊸-unitl` — **REWRITE**: keep "how a parser is started".
- `196-197` — `-- moving a consumed factor from the input side to the awaited side: this is a `shift`, before any parser is mentioned` — **REWRITE**.
- `207` — `-- the left residual turns a dependent sum on its left into a product` → `⊸⊕ᴰ` — **DELETE**.
- `223-224` — `-- ...and the same passage at a code, which is the form every client of `μ` meets it in. Writing the slot family out is all `two`'s missing η needs.` — **DELETE** the `...and`, **KEEP** the η sentence.
- `251` — `-- naturality of the left unitor's inverse, in the slot it does not touch` → `⊗-unit-l⁻-nat` — **DELETE**.
- `342` — `-- the unit law, at a representable: Eq-clean, unlike `⊗-unit-l`` → `ε⌈⌉-unit-l` — **KEEP** ("Eq-clean" is the reason this exists).
- `355` — `-- ...and the mirror, in the right factor` → `⊗⊕ᴰ-distR` — **DELETE**.
- `373-375` — `-- The constant grammar, carrying a metalanguage type through the DSL, …` — **REWRITE** ("constant grammar" → constant type, §b).

## src/Theory/Instances/Monoid/Residual/Laws.agda
- `37-38` — `-- The two together, which is the shape a client actually meets: …` — **DELETE**.
- `46` — `-- Pre-composition in the argument slot is on the nose.` → `⟜-precomp-intro⁻` — **DELETE**.
- `52` — `-- ...and so is uncurrying a pre-composition in the *result* slot.` — **DELETE**.
- `58` — `` -- `⟜-app` is `⟜-intro⁻` at the identity, so this is the previous law. `` — **KEEP**.

## src/Theory/Instances/Monoid/SemanticAction.agda
- `27` — `-- Observing a tensor: each factor is observed at its own half of the split.` → `semact-⊗₁` — **DELETE**.
- `32` — `-- ...and the same at the right factor.` → `semact-⊗ᵣ` — **DELETE**.
- `56-58` — `-- ...and the same fold, dropping the steps that emit nothing. …` — **REWRITE**: keep the "never has to filter outside the theory" clause.

## src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda
- `57` — `-- transport along maps, in either argument` → `⊛∘⊢-r` — **DELETE**.
- `66` — `-- ...and through each connective on the right` → `⊛-⊗l` — **DELETE**.
- `132` — `-- ...and `⊤Ty` on the right of a `startsWith` is absorbed.` → `startsWith⊗⊤` — **DELETE**.
- `157` — `` -- `⊕` on the left of a `&`, the mirror of `⊕-elim&`. `` → `private` — **DELETE**.
- `164-168` — `-- The keystone. Two ways of reading one word as `A` followed by something must cut it in the same place, because … This is `Precise.⊗&-align`; the old proof went through the external splitting trichotomy and two four-fold `⊕ᴰ-elim`s.` — **REWRITE**: **KEEP** the mathematical sentence (see keep list); **DELETE** "The keystone." and the last clause about the old proof.
- `178` — `-- ...and at three factors, which is the shape the star argument wants.` → `factor⊗3` — **DELETE**.
- `185` — `-- Closure of `∉FollowLast` under the connectives.` — **KEEP**.
- `213` / `221-222` / `342` / `347` / `354-355` / `366-367` — the six proof-branch narrations (`-- `B` empty: …`, `-- ...and the other copy of `B` is empty …`, `-- the prefix before the `c` is empty …`, `-- ...the trailing `A *` is empty …`, `-- ...and the real case: …`, `-- the prefix is nonempty …`) — **REWRITE**: they narrate a case split whose names (`emptyB`, `emptyPrefix`, `tailEmpty`) already carry it. Delete the three `...` ones; the other three are borderline.
- `431` — `` -- `_#_` unfolds to exactly `#→disjoint`'s hypothesis `` → `disjointFirsts→` — **KEEP**.

## src/Theory/Instances/Monoid/SequentialUnambiguity/First.agda
- `44` — `-- a word beginning with `c`` → `startsWith : Alphabet → TheoryTy ℓM tt` — **DELETE**.
- `125` — `-- separation: no character can begin both` → `_#_` — **KEEP** (defines the notation's reading).
- `145` — `-- Every nonempty word begins with some character.` → `char⁺→⊕startsWith` — **DELETE**.
- `150-152` — `-- ...so two separated grammars, one of which cannot be empty, are disjoint: …` — **REWRITE**: drop `...so`, keep the statement.
- `167` — `-- The star. With `A` non-nullable, one unrolling is enough.` — **KEEP**.

## src/Theory/Instances/Monoid/SequentialUnambiguity/Nullable.agda
- `37` — `` -- `¬Nullable` transfers backwards along any map. `` → `¬Nullable-map` — **DELETE**.
- `57-58` — `-- The split. `stringLayer↑` is the case analysis; `&⊕-distR` moves it under the `&`. This is the internal form of the old `&string-split≅`.` — **REWRITE**: delete the last sentence.
- `65-66` — `-- ...so a non-nullable grammar is entirely its nonempty part, …` — **DELETE**.
- `76` — `-- a non-nullable grammar is refuted at ε` → `¬Nullable→¬ε : ¬Nullable A → εTy ⊢ ¬Ty A` — **DELETE**.
- `80` — `-- the two ways a tensor inherits non-nullability` → `¬Nullable⊗l` — **DELETE**.

## src/Theory/Instances/Monoid/SequentialUnambiguity/FollowLast.agda
- `50-51` — `-- The converse needs `A` non-nullable: only then is every `A` a nonempty `A`, so the primed restriction costs nothing.` — **KEEP**.

## src/Theory/Instances/Monoid/Strings.agda
- `61` — `-- the carrier: strings, as the free monoid -- here, the list type itself` → `String : Type ℓM` — **REWRITE**: keep "here, the list type itself" (the presentation choice), drop the rest.
- `65-66` — `-- a single character, as a grammar: the sum of the representables at the generators` → `char` — **REWRITE**: "as a grammar" (§b); the sum-of-representables half is content.
- `170` — `-- the left unit law: an empty first factor is no factor` → `⊗-unit-l : εTy ⊗ A ⊢ A` — **DELETE**.
- `208` — `-- the carrier is a set, so a splitting's index equation is a proposition` → `isSetString : isSet String` — **REWRITE**: the consequence is the content, the premise is the type below.
- `248` — `-- ...so `⊗-unit-l` is the second projection, over any path of indices.` — **DELETE**.
- `264` — `-- functoriality of `⊗-map`, slotwise` → `⊗-map-∘` — **DELETE**.
- `270` — `-- naturality of `Eq.transport`, which is all `⊗-unit-l` does` → `transportEq-nat` — **KEEP** (the second clause).
- `356-358` — `-- Constructors and one-step observation for the canonical presentation. These live here (rather than being recovered through `Star`) so clients can use `String*` without a definitional coincidence between two codes.` — **KEEP**.
- `380-386` — `-- Canonical input observation / -- / -- The only non-formal part of `⊤Ty ≅ String*` is `read`: …` — **KEEP** the `read` argument; **DELETE** the two-word banner.
- `512` — `-- the unit's inverse. `⊗-unit-l⁻` above lands in `⊤Ty`, which is weaker.` — **KEEP**.
- `520` — `` -- The `Grammar/String/Terminal.agda` equivalence, recaptured. `` → `String*≅⊤Ty` — **DELETE**: a migration note; "recaptured" is not documentation (§b).

## src/Theory/Instances/Monoid/Suffix/Base.agda
- `62` — `-- a proper suffix is shorter, which is what makes the relation a poset` → `◂-length` — **DELETE**.
- `80` — `-- deciding a proper suffix means deciding equality against each tail` → `dec◂` — **DELETE**.
- `89` — `-- accessibility is structural recursion on the string` → `private` — **KEEP** (the "structural" claim is the well-foundedness argument).
- `108` — `-- points of the one-nonterminal indexing: a memo row per suffix` → `SPt` — **DELETE**.
- `125` — `-- Guarded elimination` — **DELETE**.
- `135` — `-- appending a non-empty prefix lands strictly below` → `◂-cons` — **DELETE**.
- `165` — `-- ... and in a tensor context: …` — **DELETE**.
- `189` — `` -- `▷? ⟨▷⟩` is "at every proper suffix", `▷? ⟨□⟩` is that and here too `` → `▷?` — **KEEP**.
- `199` — `-- the modality is functorial, lax over `&`, and holds a closed term` → `▷map` — **DELETE**: describes three definitions, sits on one.
- `215` — `-- reading the term here, and forgetting it` → `□here` — **DELETE**.
- `222` — `-- what holds at every proper suffix holds one step down, in both flavours` → `▷δ` — **DELETE**.
- `229` / `238` — `-- ...so a term made from the delayed one …` / `-- ...and Löb at a grammar` — **DELETE**.
- `246` / `250` / `254` — `-- the call took a proper suffix, or stayed put and dropped the rank` / `-- the call consumed something...` / `-- ...or it stayed where it was and the rank dropped` — **REWRITE**: three comments for a two-constructor datatype (`shorter`, `dropped`) whose names already say it. Keep one.

## src/Theory/Instances/Monoid/Thompson/Base.agda
- `57` — `-- where each regex's automaton lands` → `reLevel` — **DELETE**.
- `76-77` — `-- The carriers are finitely *ordered*, not merely finite -- which is what a determinisation has to enumerate over.` — **KEEP**.

## src/Theory/Instances/Monoid/Thompson/Construction/Epsilon.agda
- `43` — `-- the level a one-state automaton's traces land at` → `ℓε : Level` — **DELETE**. (Three near-identical copies: also `Thompson/Equivalence.agda:52` and `Automaton/Deterministic.agda:65`.)

## src/Theory/Instances/Monoid/Thompson/Construction/KleeneStar.agda
- `156` — `` -- `N`'s trace as a `*NFA` trace still owing the rest of the list `` → `⟦_⟧N` — **KEEP**.
- `174` — `-- ...and the list of them, folded back into one trace` — **DELETE**.
- `191` / `357` — `-- the shapes `ret`'s branches pass through` / `-- the shapes each branch passes through` — **DELETE**: two copies of a `where`-block apology (also at `LinearProduct.agda:427`).
- `334` — `` -- `NAlg`'s three bodies at the equalizer carrier `` — **DELETE** (duplicated at `LinearProduct.agda:404`).

## src/Theory/Instances/Monoid/Thompson/Construction/LinearProduct.agda
- `195-198` — `-- One `rec-section` covers both `⊗NFA` states at once. The old proof needed two separate equalizer inductions padded with `⊤*`, because `equalizer-ind` forces a carrier at *every* state; a homomorphism law does not.` — **REWRITE**: keep the last clause as the *reason for the design*; delete "The old proof needed…".
- `224` — `-- ...and the tails they are composed with, named so `cong` has a domain.` — **DELETE**.
- `232` / `257` / `267` / `284` / `388` / `404` / `427` / `448` — the eight `where`-block shape labels (`-- the crossing branch, at its two intermediate shapes`, `-- the branch as `NAlg` leaves it, before `map-step` is applied`, `-- ...and after, with the two reassociations left adjacent`, `-- the `N'` side, exactly the `Sum` construction's shape`, `-- the map each `⊕ᴰ≡` branch is precomposed with`, `-- `NAlg`'s three bodies, at the equalizer carrier`, `-- the shapes each branch passes through`, `-- the five shapes the labelled branch passes through`) — **DELETE**: eight comments in one file all saying "this `where` binding exists so `cong` has a domain".
- `364-368` — the `⟜`-currying paragraph — **KEEP**.

## src/Theory/Instances/Monoid/Thompson/Construction/Literal.agda
- `114` — `-- rolling up a `step` summand, named so `cong` has a domain to solve` — **DELETE**: ninth copy of the same apology.
- `102-105` — the `STEP ∘ (id ⊗ STOP) ∘ …` composite — **KEEP**.

## src/Theory/Instances/Monoid/Thompson/Construction/Sum.agda
- `174` — `-- ...and back: each sub-automaton's trace embeds by renaming transitions.` — **REWRITE**: keep "embeds by renaming transitions".
- `209-211` — `-- The composite each `step` branch … Naming it is what gives `cong` a domain to solve for.` — **DELETE** the last sentence.
- `258-260` — `-- ...and so is `fromNFA`, read as a map out of each sub-automaton's trace. …` — **DELETE** the `...and so is`.

## src/Theory/Instances/Monoid/Thompson/Equivalence.agda
- `52` — `-- the level a regex's automaton's traces land at` → `reNFALevel` — **DELETE**.
- `63` — `` -- `Regex.Base`'s `⟦_⟧`, at the level the traces live at `` → `⟦_⟧nfa` — **KEEP**.

## src/Theory/Instances/Monoid/Types.agda
- `42` — `` -- `at` clashes with the `_at_` of `SemanticAction`, which every test uses `` → `open import …` — **KEEP**.
- `48-50` — `-- The connectives' h-levels and the distributivity `⊗⊕-distL` is missing an inverse for. `Strings` states the connectives but does not import `HLevels`, so the set-ness of a binary `⊗` has to be said here.` — **REWRITE**: ungrammatical ("distributivity … is missing an inverse for"), and the second half is an import apology.
- `73-74` — `-- ...and it is an inverse: neither direction touches the splitting, so both round trips are the `⊕`'s case split and nothing else.` — **REWRITE**: drop `...and it is an inverse`.
- `87-88` — `-- ...and the grammars that carry their set-ness, …` — **DELETE**.
- `111-112` — `-- Deciding a lookahead class. This is equality of classes, not a parser combinator, so it sits with the classes.` — **REWRITE**: the file-organisation justification is not documentation.

## src/Theory/Instances/Monoid/Unicode/Base.agda
- `46` — `-- structural, so it reduces to `Eq.refl` -- the whole point` → `_≟Bits_` — **REWRITE**: keep "structural, so it reduces to `Eq.refl`"; "the whole point" is voice.
- `58` — `-- 21 bits span 0 .. 0x10FFFF, which is every code point` → `UChar` — **KEEP**.
- `69-71` — `-- Accumulator form, so the recursive call appears once. Measured: the duplicating form (`toNat bs + toNat bs`) is no slower, so Agda shares the thunk -- this is defensive, not a fix.` — **REWRITE**: "this is defensive, not a fix" admits the comment documents nothing.
- `83` — `-- the code point back out, so a range can be decided by comparison` → `code : UChar → ℕ` — **DELETE**.
- `87` / `91` — `-- text enters the theory here and nowhere else` / `-- ...and leaves here, which is what lets a test state its result as text` — **KEEP** the first (a real boundary claim), **DELETE** the second.

## src/Theory/Instances/Monoid/Unitor.agda
- `31-32` — `-- Two `castEq`s along inverse equations cancel, on the nose once the equation is matched.` — **KEEP**.
- `47-49` — `-- Both reassociations keep the same three slots over the same word; they differ only in how the splitting is rebuilt, and `two≡` is the whole difference.` — **REWRITE**: "is the whole difference" repeats "differ only in".
- `94-102` — `-- The right unitor. `⊗ε-unit-r` matches its argument's equation instead of transporting, so one composite is `castEq` bookkeeping... / -- ...and the other has to *match* …` — **KEEP** the mechanism; **REWRITE** the `...` split across two comments.
- `134-136` — `-- Naturality, at the levels a client actually meets. `Strings` states these only at `ℓM`, which is enough for its own use and for nothing else; the proofs never mentioned the level.` — **REWRITE**: "enough for its own use and for nothing else" is snide; say "restated level-polymorphically".

## src/Theory/Type/Bottom/Base.agda
- `35` — `-- the same at the lifted empty type, so a client never has to unfold it` → `⊥Ty↑-elim` — **DELETE**.

## src/Theory/Type/Code/Base.agda
- `1` — `-- Codes for strictly positive functors` — **KEEP**.

## src/Theory/Type/Code/Container.agda
- `1` — `-- TODO is this actually used?` — **REWRITE**: answer it (`grep` says: yes, nothing imports it). This is an agent's question left in the source.

## src/Theory/Type/Decidable/Base.agda
- `1` — `-- TODO how much of this is actually used?` — same; four copies of this exact TODO exist (see below).

## src/Theory/Type/Decidable/Route.agda
- `44` — `-- Deciding an index in `Eq`, so that matching refines.` → `DiscreteEq` — **KEEP**.
- `58-64` (unchanged) — `-- THE THEOREM, in context: decisions for the alternatives become a decision of their sum. …` — **REWRITE**: `THE THEOREM` in shouting caps; the content after the colon is good.
- `101` — `-- ...and closed, which is what a top-level decision wants.` → `routeDec` — **DELETE**.

## src/Theory/Type/Equivalence/Base.agda
- `79` — `-- Monomorphisms` → `isMono` — **DELETE**.
- `105-107` — `-- Yoneda turns a mono into an injection. The old grammar development had to go through `pick-parse` and a `JDep` over `⌈ w ⌉`; here `yoIso` *is* that argument, already done once and for all.` — **REWRITE**: keep sentence 1, delete the comparison with the old tree (§b).
- `125` — `-- ...and conversely, pointwise injectivity is monicity.` → `injective→isMono` — **DELETE**.
- `131-132` — `-- Composition and inversion of `≅`. `THEORYTY`'s `⋆WildCatIso` does this too, but that module is private to `Theory.Base`.` — **REWRITE**: an access-modifier apology; export it instead.

## src/Theory/Type/Guarded/Base.agda
- `27` — `-- where a guarded recursion is at: an index and an input` → `Pt` — **REWRITE**: "where … is at" is colloquial; the index/input pair is the content.
- `48` — `-- the β-rule: what `next` promised is what `app` delivers` → `app-next` — **KEEP**.
- `91` — `-- the β-law comes with it, rather than being a separate `refl`` → `fold-unfold` — **KEEP**.

## src/Theory/Type/Guarded/Justification.agda
- `2` — `-- TODO how much of this is actually used?` — see below.
- `88` — `-- memoising changes the cost, not the value` → `löbMemo≡löbFrom` — **KEEP**.
- `93-94` — `-- ... and the order from a measure. This is the *only* place a consumer's size argument has to go.` — **REWRITE**: drop the `...`, keep the "only place" claim.
- `104-105` — `-- The step vocabulary of the lexicographic guard, re-exported so that a consumer names it without naming an order.` — **KEEP**.
- `175` — `-- when the recursive call does not look at its guard, `mapG` *is* `map`` → `private` — **KEEP**.
- `194` — `-- coalgebra + algebra + guardedness, by löb` → `hylosFromGuard` — **DELETE**.
- `237-245` — the `löbByMeasure`-vs-fuel paragraph — **KEEP** (see keep list).
- `258` / `265` — `-- the fuel is spent one unit per step, structurally` / `-- how much fuel was left over does not change the value` → `go`, `go-irr` — **KEEP** the second (`go-irr`'s name does not say it); **DELETE** the first once `go` is renamed (§a).

## src/Theory/Type/HLevels.agda
- `163` — `-- a proposition at one end of a line of types fills the whole line` → `isPropPathP` — **DELETE**.

## src/Theory/Type/Later/Derivative.agda, Later/Indexed.agda, Later/Lex.agda
- `Derivative.agda:1-5`, `Indexed.agda:1-5`, `Lex.agda:1-5` — the **same five-line WARNING/TODO block, copy-pasted verbatim into three files**: `-- TODO how much of this actually used? / -- WARNING for now I have been treating this as a place to sequester the semantic reasoning about guarded recursion so that importers of this module can work with a clean interface / -- The implementation are subject to change per experiments w Cass` — **REWRITE**: this is the maintainer's own note, not agent slop, but three copies is two too many, and "The implementation are" is ungrammatical. Put it once, in `Theory/Type/Later/` — or delete now that `Guarded/Base` exists as the interface.
- `Lex.agda:24` / `28` / `60` — `-- the first component drops, or it does not and the second drops` / `-- the two disjuncts exclude each other, so the sum is a prop` / `-- decidable when each comparison is, plus equality on the first component` → `_<lex_`, `isProp<lex`, `dec<lex` — **DELETE** the first and third; **KEEP** the second (the exclusion is the proof).

## src/Theory/Type/Later/Tabulated.agda
- `50` / `54` / `59` — `-- a family's value at a point` / `-- the position of a cell in a table` / `-- the memo table: one materialised cell per listed point` → `At`, `_∈ᴾ_`, `Tbl` — **DELETE** the first; **KEEP** the other two (`∈ᴾ` and `Tbl` are notation-heavy).
- `112` — `-- the tabulated later modality` → `▷ᵗ` — **DELETE**.
- `129` — `-- a table is a delayed hypothesis: read it at every point below` → `tabulate` — **KEEP**.
- `139` — `-- the shared cell: `t` is a variable, so both its uses are one thunk` → `cell` — **KEEP** (the sharing is the whole point of the module).
- `171` / `182` / `196` / `210` — `-- every cell of the built table holds the fixed point's value there` / `-- the guarded fixed-point equation, for the tabulated hypothesis` / `-- reading the built table anywhere gives the fixed point's value` / `-- the tabulated fixed point *is* the untabulated one` → `build-tab`, `löbᵗ-unfold`, `key`, `löbTab≡löb` — **DELETE** all four: each transliterates the equation on the line below.

## src/Theory/Type/Monad/Base.agda
- `1` — `-- TODO how much of this Monad/ dir is actually used?` — see below.
- `19-20` — `-- TODO use an upstream interface for defining Monads / -- perhaps on a locally small cat?` — **KEEP**: a real, actionable TODO.
- `44-45` — `-- ...and `fmap` is functorial, from the three laws above. Every covariant answer functor gets its `Ans-≅` laws from these.` — **REWRITE**: drop the `...and`.

## src/Theory/Type/Operation/Base.agda
- `92` — `-- uniform levels` → `⊗ᵘ[_]` — **DELETE**.
- `126-134` — the `⊗-elim`-vs-projection paragraph including `-- Measured on `Bags/Quicksort/Tests`: matching costs >7min where projecting costs 3.3s.` — **KEEP** (see keep list); this is the one benchmark in the tree that documents a *design decision* rather than a machine.
- `145` — `-- ... with a value carried alongside, which is how a delayed hypothesis reaches the slots` — **REWRITE**: drop the `...`.
- `176` — `-- projecting a slot out of the tuples` → `argAt` — **DELETE**.
- `217` — `-- Equations of the theory lift to isos of the convolutional liftings` → `eqn→Iso` — **DELETE**.
- `249` — `-- the convolution of representables is the representable at the composite` → `⊗⌈⌉Iso` — **DELETE**.
- `261` — `-- A term that is a variable convolves to nothing` → `unVar` — **REWRITE**: "convolves to nothing" is unclear; the type says `⊥`.

## src/Theory/Type/PropositionalTruncation/Base.agda
- `48-50` — `-- The universal property: `∥_∥` is left adjoint to the inclusion of the unambiguous types. In `Theory`, `unambiguous A = ∀ m → isProp (A m)`, so this is `PT.rec` with nothing in the way.` — **KEEP**.
- `59` — `-- ...so truncating an unambiguous type does nothing.` → `∥∥idem` — **DELETE**.
- `84` — `-- the image factorisation: a map into `A` factors through `∃subgrammar`` → `∃-intro` — **REWRITE** (`∃subgrammar`, §b).

## src/Theory/Type/Representable/Base.agda
- `24` — `-- Yoneda: a map out of a representable is a point` → `yoIso` — **KEEP**.
- `31` — `-- precomposition with a pointwise iso` → `precompIso` — **DELETE**.

## src/Theory/Type/Subgrammar/Base.agda
- `95` — `-- a section of `sub-π` says `p` holds everywhere` → `subgrammar-section` — **DELETE**.
- `133` — `-- The preimage of a subobject along a map.` → `module _ …` — **DELETE**: `preimage` is three lines below.
- `143` — `-- Every mono into a set is a subobject.` — **KEEP**.
- `154` — `-- The constantly-`A` proposition, available whenever `A` is unambiguous.` — **DELETE**.

## src/Theory/Type/Sum/Binary/Base.agda
- `48-49` — `-- Eliminating a sum in a `&`-context: `&` distributes over `⊕` because both are computed pointwise.` — **KEEP**.

## src/Theory/Type/Unambiguity/Disjoint.agda
- `85-86` — `-- `&-Δ` having a section already forces unambiguity: the section makes the two projections agree.` — **KEEP**.
- `104-105` — `-- Transport of unambiguity, and the upgrade from a weak to a strong equivalence that unambiguity licenses.` — **DELETE**: table of contents for the next 30 lines.
- `132` — `-- The point of `≈`: between unambiguous types it is already a `≅`.` → `≈→≅` — **REWRITE**: "The point of X" is used seven times across the tree.

## Outside src/Theory (few, and mostly human)
- `src/Term/Category.agda:43` — `-- Note that with ⊗ implemented with SplittingEq,` — **REWRITE**: drop "Note that".
- `src/Grammar/LinearFunction/Base.agda:69` — `-- Now refl if the witness to splitting is Eq.refl` — **REWRITE**: drop "Now".
- `src/Examples/BinOp.agda:237` — `-- Here we ensure that the chosen guard and state match` — **REWRITE**: drop "Here we".
- `src/Examples/Section2/Figure5.agda:211` / `:247` — `-- Here we use our equalizer types, and in particular` / `-- That is, we have shown H→UL s ∘g UL→H s ≡ id` — **KEEP**: this is paper-companion code where first person is deliberate.
- `src/Grammar/External/HLevels/Properties.agda:27` — `-- This is the definition of unambiguity you'd expect in the grammar model of the …` — **REWRITE**: second person ("you'd"), the one instance in the tree.

### Repeated TODO, four copies
`src/Theory/Type/Code/Container.agda:1`, `src/Theory/Type/Decidable/Base.agda:1`,
`src/Theory/Type/Monad/Base.agda:1`, `src/Theory/Type/Guarded/Justification.agda:2`,
plus `src/Theory/Type/Later/{Derivative,Indexed,Lex}.agda:1` — seven files open with
`-- TODO how much of this actually used?`. **REWRITE**: answer it once with a
dependency check and delete the other six.

---

# SWEEP 1 — KEEP LIST (do not let a sweep take these)

These carry mathematical or Agda-operational content that is *not* recoverable
from the code. Be generous here: when in doubt, this list wins.

## The `Fin n` / η facts — the single most reused non-obvious fact in the tree
1. `src/Theory/Instances/Monoid/Strings.agda:215-216` — "`Fin 2` has no definitional η, so a rebuilt splitting reaches an arbitrary one only through this path."
2. `src/Theory/Instances/Monoid/Residual.agda:52` — same fact, at `two-η`.
3. `src/Theory/Instances/Monoid/Residual.agda:212-213`, `223-224` — why the convolution/tensor passage is stated once and at a code.
4. `src/Theory/Instances/Monoid/Convolution.agda:33-34` — "`Fin 2` has no η, so this is `two-η` and nothing else."
5. `src/Theory/Instances/Monoid/Unitor.agda:37-38` — "`εTy`'s splitting is a function out of `Fin 0`, so it is a proposition -- but only up to `funExt`, since `Fin 0` has no η."
6. `src/Theory/Instances/Monoid/KleeneStar.agda:122-126` — the `two-η` + `funExt λ ()` decomposition of `roll*`/`unroll*`.
7. `src/Theory/Instances/Lambda/Base.agda:72` — "`Fin 1` has no η, so the motive sees the tuple".
8. `src/Theory/Instances/Monoid/Automata/NFA/Base.agda:75-77` — why `k (Lift εTy)` rather than `⊗e ε·`: `Lift` has η, so stop-branches close by `refl`.
9. `src/Theory/Instances/Monoid/Combinator/Core.agda:188` — "`Lift` has η, so both round trips are `refl`."
10. `src/Theory/Instances/Monoid/Automaton/Implicit/Disjointness.agda:116-117` — "`Lift` has η, so the adapter is invisible in every branch."

## Cubical / `Eq` reduction hazards — the second reused class
11. `src/Theory/Instances/Monoid/Strings.agda:126-129` — why `⊗-assoc` is stated in `Eq`: "a `pathToEq` is stuck, and a stuck cast at `μ` blocks every recursor underneath it."
12. `src/Theory/Instances/Monoid/Residual.agda:33-35` — "`Eq.transport` goes through `subst`, so it leaves an `hcomp` even at `Eq.refl`."
13. `src/Theory/Instances/Monoid/Precise.agda:33-35` — the K-restriction: `(c ∷ []) ++ v ≟ c ∷ as` would eliminate a reflexive equation, so the split is flattened.
14. `src/Theory/Instances/Monoid/Precise.agda:40-43` — why `flat`'s `∙` leaves a stuck `transp` and `Eq.transport A Eq.refl a = a` does not.
15. `src/Theory/Instances/Monoid/Greedy/Base.agda:104-106` — "`flatEq`, not `flat`: a cubical `subst` here leaves a `transp` over the witness's splitting that never reduces."
16. `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda:54-57` — decidable `ℕ` equality by structural recursion, not `discreteℕ`, because `Eq.pathToEq` yields a proof that is not `Eq.refl` and `dec-lit⊗-at` gets stuck on it.
17. `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda:69-70` — "`Sum.inl Eq.refl` is what makes a matched letter *compute*."
18. `src/Theory/Instances/Monoid/Combinator/Decidable/Window.agda:25-27` — "`◂` is inverted by projection rather than by matching: `K` is off, so an equation between constructor applications does not split."
19. `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:45-47` — "`with` cannot see through a definition, so the elimination is a `where` on the sum."
20. `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:76-78` — the `(v : Bool) → x ≡ v` idiom for inspecting a stuck `Bool` *with* its equation.
21. `src/Theory/Instances/Monoid/Automaton/Implicit/Compile.agda:156-157` — "`if-true` is the only way the `if (M .acc q)` gets out of the way, since `acc q ≡ true` is a path."
22. `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:354-355` — "the `⊕` clause splits on `b` only because `νOf b +ν νOf b'` is stuck for a variable `b`."
23. `src/Theory/Instances/Monoid/Regex/Base.agda:49-51`, `Notation.agda:47-48`, `54-56`, `64-65` — the left-driven `_·ν_`/`_+ν_` argument: which argument drives is what keeps the index reducing.
24. `src/Theory/Instances/Monoid/Regex/Base.agda:102-103` — "the equation is threaded rather than matched: Agda cannot invert `_·ν_` in an index."
25. `src/Theory/Instances/Monoid/Strings.agda:393-394` — naming the slot functor with an explicit type pins its level so `Lift` levels stop being metavariables.
26. `src/Theory/Instances/Monoid/Phase/Display.agda:216-217` — "leaving them implicit blocks pattern unification."

## Termination / structural-descent facts
27. `src/Theory/Instances/Monoid/Automaton/Unambiguous.agda:73-74` — "the recursive call stands in the clause body: a `where` binding would hide the structural descent on `f' (suc zero)` from the checker."
28. `src/Theory/Instances/Monoid/KleeneStar/Unambiguous.agda:107-109` — the same, for `A *`.
29. `src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:199-200` — the same, for `cancel`.
30. `src/Theory/Type/Guarded/Justification.agda:237-245` — why the fuel-based Löb reduces where `löbByMeasure` does not (a match on an `Acc` blocks; carried-and-never-matched bound proofs do not).
31. `src/Theory/Instances/Monoid/KleeneStar.agda:24-25` / `Strings.agda:344-345` — "two occurrences of the same extended lambda never compare", so the branch must be a named function.

## Performance facts that document a *design*, not a machine
32. `src/Theory/Type/Operation/Base.agda:126-134` — `⊗-elim` blocks at a quotient model where the projecting variant does not; measured 7min vs 3.3s. **The single most valuable comment in the tree.**
33. `src/Theory/Instances/Bags/Quicksort/Tests.agda:1-40` — the two quicksort pitfalls (never `transp` a payload whose type is a `μ`; never recurse through `μ`'s recursor at a function-typed motive), with the A/B test for telling them apart. Trim, do not delete.
34. `src/Theory/Instances/Monoid/Automaton/Lexicon.agda:144-151` — why the product state is a nested pair and not a function (`(i : Fin n) → Qs i` re-walks a transition chain per access).
35. `src/Theory/Instances/Monoid/Automaton/Lexicon.agda:266-271` — why `find` runs on the state and not on the match's acceptance equation: the other way is quadratic.
36. `src/Theory/Instances/Monoid/Automaton/TokenStream.agda:297-300`, `307-308` — why the scan's table is carried rather than re-derived at each token boundary.
37. `src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:266-271` — the early exit: forcing the tail's cell makes one token cost the whole remaining input.
38. `src/Theory/Instances/Monoid/Phase/Display.agda:122-133` — why `⊕ᴰ` is deliberately *not* an instance, with the measured ambiguity report.

## Mathematical content
39. `src/Theory/Instances/Monoid/Precise.agda:133-136`, `156-161` (first three sentences) — Levi's lemma and the splitting-alignment argument it powers.
40. `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:164-166` — the keystone: two readings of `A`-followed-by-something must cut in the same place, because the disagreeing letter would both follow `A` and open the right factor.
41. `src/Theory/Instances/Monoid/SequentialUnambiguity/Base.agda:302-304` — Brüggemann-Klein and Wood's star theorem, and the carrier the refutation folds with.
42. `src/Theory/Instances/Monoid/Derivative/General.agda:125-130` — why `⌈ w ⌉ u` being a singleton is the *only* reason Brzozowski's derivative and the residual agree.
43. `src/Theory/Instances/Monoid/Lookahead/Base.agda:65-66` — "(`Λ₁ ε₁` is *not* extension-closed: ε is only the empty word.)"
44. `src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda:226-234` — the cover-with-a-classifier-as-the-part trade, with what is bought and what is owed.

Also protect: the surface-syntax headers in `Regex/{Tests,Notation,Unicode,UnicodeTests}.agda`,
`Backreference/{RegexTests,Stress/Common}.agda`, `Combinator/Decidable/Arrow.agda`
and the BNF lines in `Combinator/Decidable/STLC.agda` / `Grammars/{PolyGrammar,Dyck,Polynomial}.agda`.
They are the only readable form of the token lists and `Table.at` clauses below them.

---

# SWEEP 1 — NON-OBVIOUS CODE WITH NO COMMENT

The inverse defect. Top 20, by how much a reader loses.

1. `src/Theory/Type/SemanticAction/Base.agda:36-40` — `Δ X = ⊕[ x ∈ X ] ⊤Ty` and `SemanticAction A X = A ⊢ Δ X`. The central definition of the whole library. The file still has **zero** comment lines. Nothing says why a semantic action is a map into `Δ X`, or that this is what makes actions composable.
2. `src/Theory/Type/SemanticAction/Base.agda:78` — `semact-dec : SemanticAction A X → SemanticAction (DecTy A) (M.Maybe X)`. This is the bridge out of `DecTy` that `Regex/Examples.agda:37-39` separately calls out as "a *refutation* of every parse, not a dropped error". The definition site says nothing; the warning lives in an examples file three directories away.
3. `src/Theory/Type/Inductive/HLevels.agda:30-38` — `isSetValued`, a six-clause recursion over `Functor` that decides which codes are set-valued. 182 lines, one comment (the OPTIONS pragma). The `Lift ℓX` in the `Var` clause is a level-juggling subtlety with no explanation.
4. `src/Theory/Type/Monad/NonDet.agda:127-128` — `q = eq-π bindAppL bindAppR`, an equalizer projection used to prove a monad law. 173 lines, one comment.
5. `src/Theory/Instances/Lambda/TermPresentation.agda` (153 lines) — **zero** comments. It supplies the free-model presentation the whole `Lambda` instance is built on.
6. `src/Theory/Type/Top/Properties.agda` (121 lines) — zero comments.
7. `src/Theory/Type/Product/Binary/Base.agda` (120 lines) — zero comments.
8. `src/Theory/Instances/Monoid/Thompson/Construction/Sat.agda:130` — `satNFA≅ : Parse ≅ LiftTheoryTy ℓsat (satTy P)`. A coherence/equivalence result in a 135-line file with one comment line. Why the lift level is `ℓsat` and not `ℓM` is invisible.
9. `src/Theory/Instances/Monoid/Automaton/Greedy.agda` (130 lines, one comment) — the whole module is superseded by `GreedyMax` and nothing in it says so.
10. `src/Theory/Instances/Monoid/ListPresentation.agda` — 121 lines, one comment (`:113`). The other `recGen`/`recOp` clauses have the same unit-law subtlety the one comment describes and are unremarked.
11. `src/Theory/Instances/STLC/Base.agda:69-...` — h-level proofs for the STLC sorts/operations; 167 lines, two comments. The reason the *sorts* need `isSet` (the term presentation) is stated; the reason the operations do is not.
12. `src/Theory/Instances/Monoid/Automata/NFA/Properties.agda` — one comment line (the pragma) in the whole file, and it is one of the files the concurrent edit touched.
13. `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:824-851` — seven `go` helpers, each an *injectivity* lemma for a different type former (`Pr A B ≡ Pr A' B' → A ≡ A'`, …), all unnamed and all uncommented. That these are the inversion principles the uniqueness proof needs is invisible.
14. `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:855` — `data ArV : ATy → Type` has the comment `-- views, so a former that needs a shaped type says so once`, but the three *other* view families defined alongside it have none, and the comment does not say a view is what avoids matching on `ATy` under `Eq`.
15. `src/Theory/Instances/Monoid/Regex/Sat.agda:48` — `y = t .snd .snd .fst .fst`. A four-deep projection chain with no comment and no name (see §a).
16. `src/Theory/Instances/Monoid/Automaton/TokenStream.agda:322` — `z = gm .fst (suc zero)`. Same.
17. `src/Theory/Instances/Monoid/Greedy/Base.agda:66` — `pl = t .snd .snd .fst .snd`. Commented, but only as "the `char⁺` witness splits the matched prefix"; the *shape* being projected is not stated and the chain is unreadable.
18. `src/Theory/Type/Residual/Base.agda:187` — `x' = subst⁻ (argAt n ℓs ss As i) at x`. A `subst⁻` along a slot projection, uncommented; this is exactly the kind of transport that `Type/Operation/Base.agda:126-134` warns can block.
19. `src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:441-442` — "the end state is determined, the acceptance equation is a proposition, and the trace is unambiguous". Three hypotheses named, but the *conclusion* (that this makes `BridgeTy b q` a proposition, hence the two maps an iso) is stated 70 lines earlier at `370-374` and nowhere near the proof.
20. `src/Theory/Instances/Monoid/Combinator/Core.agda:480-501` — `Choice`'s `Guide`/`route` record. The comment explains what routed choice *is*, but nothing says why `into` must be the only way the cover is reached (the soundness condition), which is what `Grammars/ArithGrammar.agda:537-539` separately half-explains.

---

# SWEEP 2 — NAMING

## (a) Meaningless local helpers

**117 bindings.** `go` is used 112 times across 28 files, `go2`/`go3`/`go4` for
nested cases, plus one `helper` and one `foo`/`bar` pair. Full list in
`go-list.txt`; the patterns and their fixes:

### Pattern 1 — "case-split on a decision" (~45 occurrences)
`go : (x Eq.≡ y) Sum.⊎ ((x Eq.≡ y) → Empty.⊥) → …`, the eliminator for a `≟`.
Proposed name: **`onDec`** (or `fromDec`), uniformly.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Window.agda:43` — eliminates `c ≟ d` inside `decWindow`. → `onHeadDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda:84` — `decMTok (just x) (just y)`. → `onTokDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda:92` — `decCls (after s) (after t)`. → `onAfterDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda:98` — `decCls (headed c) (headed d)`. → `onHeadedDec`.
- `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda:64` — inside `_≟_` on `Tok`. → `onTokDec`.
- `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda:81` — `var v ≟ var w`. → `onVarDec`.
- `src/Theory/Instances/Monoid/Combinator/Grammars/PolyGrammar.agda:87` — `nat n ≟ nat n'`. → `onNatDec`.
- `src/Theory/Instances/Monoid/Combinator/Core.agda:116` — `decM₁ (tk c) (tk d)`. → `onLetterDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Base.agda:63` — `dec-lit⊗-at c`. → `onLetterDec`.
- `src/Theory/Instances/Monoid/Combinator/Incomplete/Base.agda:63` — same, at `Maybe`. → `onLetterDec`.
- `src/Theory/Instances/Monoid/Combinator/NonDet/Base.agda:110` — same, at `ND`. → `onLetterDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Lookahead.agda:91` — refutes a non-observed class. → `onClassDec`.
- `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:65` — `eqb-refl x = go (x ≟ x)`. → `eqbAtRefl`.
- `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:72` — `eqb-true x y`. → `eqbToPath`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:722`, `730`, `738` — inside `≟ty` at `Ar`, `Pr`, `Li`. → `onArgDecs`, `onArgDecs`, `onArgDec`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:772` — `lookupC ((y , B) ∷ Γ) x`. → `onNameDec`.
- `src/Theory/Type/Decidable/Base.agda:219` — `dec-cover`. → `onCellDec`.
- `src/Theory/Instances/Bags/Partition.agda:41` — `sideOf x y = go (le y x) Eq.refl`. → `onCompare`.

### Pattern 2 — "case-split on a stuck `Bool`, keeping its equation" (~15)
`go : (b : Bool) → p ≡ b → …`. Proposed name: **`onBool`** / `atValue`.
- `src/Theory/Instances/Monoid/Automaton/Lexicon.agda:101` — head of `allFin-elim`. → `headTrue`.
- `src/Theory/Instances/Monoid/Automaton/Lexicon.agda:110` — tail of `allFin-elim`. → `tailAll`.
- `src/Theory/Instances/Monoid/Automaton/Lexicon.agda:128` — inside `find`. → **`findFromHead`** (it is the real recursion: "either the head is `true` and it is the answer, or recurse on the tail").
- `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:146`, `152` — `DisjCls` at `one d` / `cls P`. → `onMembOfD`, `onMembOfE`.
- `src/Theory/Instances/Monoid/Automaton/Implicit/Analysis.agda:202` — `sideCond`. → `onMembership`.
- `src/Theory/Instances/Monoid/Regex/Sat.agda:76` — `dec-sat⊗-at`. → `onSatisfies`.
- `src/Theory/Instances/Monoid/Automaton/Greedy.agda:110`, `GreedyMax.agda:304` — the accept/reject split inside `scan`. → **`onAcceptance`**.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Productions.agda:210` — inside `nulP`. → `onNullable`.

### Pattern 3 — "the eliminator for the empty-state / accepting-state run" (2)
- `src/Theory/Instances/Monoid/Automaton/Greedy.agda:81` and
  `src/Theory/Instances/Monoid/Automaton/GreedyMax.agda:261` —
  `go : (q : Q) (b : Bool) → isAcc q Eq.≡ b → εTy ⊢ Run q`. Two files, identical
  signature, both called `go`. → **`emptyRunAt`**.

### Pattern 4 — "unfold a `⊗` witness into its two slots and its equation" (~20)
`go : (x y w : ↓M tt) → … → …`, always immediately applied to
`(ms zero) (ms (suc zero)) m …`. Proposed name: **`atSplit`** or `onSplit`.
- `src/Theory/Instances/Monoid/Residual.agda:123` (`⟜-uncurry`) → `atSplit`.
- `src/Theory/Instances/Monoid/Residual.agda:188` (`⊸-uncurry`) → `atSplit`.
- `src/Theory/Instances/Monoid/Residual.agda:203` (`⊸⟜-swap`) → `atSplit`.
- `src/Theory/Instances/Monoid/Residual.agda:247` (`⊗ε-unit-r`) → `atEmptyRight`.
- `src/Theory/Instances/Monoid/Residual.agda:332` (`⌈⌉-cat`) → `atSplit`.
- `src/Theory/Instances/Monoid/Residual.agda:339` (`⌈⌉-split`) → `atConcatEq`.
- `src/Theory/Instances/Monoid/Residual.agda:347` (`ε⌈⌉-unit-l`) → `atEmptyLeft`.
- `src/Theory/Instances/Monoid/Strings.agda:193` (`lits→⌈⌉`) → `atConsSplit`.
- `src/Theory/Instances/Monoid/Strings.agda:200`, `204` (`⌈⌉→lits`) → `atNilEq`, `atConsEq`.
- `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:68`, `79` (`⊗-¬Nullable`, `⊗-¬NullableR`) → `atSplitOfEmpty`.
- `src/Theory/Instances/Monoid/KleeneStar/Guarded.agda:100` (`¬Nullable→NonNull`) → `atSplit`.
- `src/Theory/Instances/Monoid/Lookahead/Window.agda:77` → `atHeadSplit`.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Bracket.agda:288`, `301`, `310`, `324`, `345`, `365`, `387` — seven `go`s + five `go2`s + four `go3`s + one `go4` in **one file**, all `(u v : List Tok) → u Eq.≡ (c ∷ []) → (u ++ v) Eq.≡ m`. → `atLeadingTok` / `atBodySplit` / `atCloseSplit` / `atRefSplit` by depth. **This file alone accounts for 17 of the 117.**

### Pattern 5 — "pointwise extensionality goal for an inverse law" (~10)
`go : (m : String) (x : … m) → f m x ≡ x`, always `funExt λ m → funExt (go m)`.
Proposed name: **`atPoint`** or `pointwise`.
- `src/Theory/Instances/Monoid/Unitor.agda:53`, `64` (assoc round trips) → `atPoint`.
- `src/Theory/Instances/Monoid/Unitor.agda:84`, `122` (unitor round trips) → `atPoint`.
- `src/Theory/Instances/Monoid/Strings.agda:322`, `333` (pentagon) → `atPoint`.
- `src/Theory/Instances/Monoid/Residual.agda:288`, `300`, `310`, `320` (the four triangles) → `atPoint`.
- `src/Theory/Type/Decidable/Base.agda:121`, `132` (`dec-retract-id`, `dec-retract-∘`) → `atDecision`.

### Pattern 6 — genuinely recursive workers named `go` (~12)
These are the ones where `go` is most defensible and still worst, because they
*are* the algorithm:
- `src/Theory/Instances/Monoid/Regex/Parse.agda:105` — decimal digits → ℕ. → **`digits`**.
- `src/Theory/Instances/Monoid/Regex/Parse.agda:114` — a bounded numeral with an "any digits seen" flag. → **`numeral`**.
- `src/Theory/Instances/Monoid/Regex/Parse.agda:153` — accumulate a character-class predicate. → **`classItems`**.
- `src/Theory/Instances/Monoid/Regex/Parse.agda:168` — scan a bracket expression to its `]`. → **`bracketBody`**.
- `src/Theory/Instances/Monoid/Regex/Parse.agda:213` — apply postfix operators at a fuel bound. → **`postfixes`**.
- `src/Theory/Instances/Monoid/Regex/Parse.agda:261` — the top-level `parseRE` driver. → **`parseAlt`**.
- `src/Theory/Instances/Monoid/Unicode/Base.agda:75` — bits → ℕ with an accumulator. → **`bitsFrom`**.
- `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:345` — sum node sizes over a `List Tree`. → **`sumNodes`**.
- `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:532` — `BFoldr`'s three-type unifier. → **`foldrTy`**.
- `src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:544` — `DecTy Term w → Maybe ATm`. → **`astFromDec`**.
- `src/Theory/Instances/Monoid/Greedy/Examples.agda:123` — n applications of `extendAt`. → **`extendN`**.
- `src/Theory/Type/Guarded/Justification.agda:259` — the fuelled Löb recursion. → **`byFuel`** (its sibling is already `go-irr`, which should become `byFuel-irr`).

### Pattern 7 — "dispatch on a `Dec (Ty? Γ t)`" — 15 identical `go`s in one block
`src/Theory/Instances/Monoid/Combinator/Decidable/STLC.agda:907`, `912`,
`921`, `931`, `941`, `947`, `964`, `976`, `990`, `1006`, `1011`, `1035`
(+`go2` at `1043`) — every clause of `typed?` has a `where go` that combines the
subterm decisions. → name each after its former: **`fromName`**, `fromSuc`,
`fromFst`, `fromSnd`, `fromPair`, `fromApp`, `fromCons`, `fromIte`, `fromRec`,
`fromLam`, `fromFoldr`, `fromLet` / `fromLetBody`. Twelve `go`s in 130 lines is
the worst single stretch in the tree.

### Other short/meaningless bindings
- `src/Theory/Instances/Monoid/Regex/Sat.agda:48` — `y = t .snd .snd .fst .fst` → **`matchedLetter`**.
- `src/Theory/Instances/Monoid/Automaton/TokenStream.agda:322` — `z = gm .fst (suc zero)` → **`remainder`**.
- `src/Theory/Instances/Monoid/Greedy/Base.agda:66` — `pl = t .snd .snd .fst .snd` → **`prefixSplit`**.
- `src/Theory/Instances/Monoid/Greedy/Base.agda:76` — `whole : c ∷ ms (suc zero) ≡ d ∷ (ks1 ++ ns1)` → `headsAgree`.
- `src/Theory/Type/Equivalence/Base.agda:117-118` — `q : f ∘⊢ yoIso m .inv x ≡ …` → **`yoNat`**.
- `src/Theory/Type/Monad/NonDet.agda:127-128` — `q : equalizer bindAppL bindAppR ⊢ ND B` → **`eqProj`**.
- `src/Theory/Type/Residual/Base.agda:187` — `x'` → **`slotAt`**.
- `src/Theory/Type/Later/Tabulated.agda:175` — `helper : (v : ChainView (below) p) → …` → **`onChainView`**.
- `src/Theory/Instances/Monoid/Combinator/Decidable/Productions.agda:233` — `kids` → **`subtrees`** (`kids` is jocular, and the sibling is `Tree`).
- `src/Grammar/Derivative/Base.agda:65-69` — `foo : √l c A (c ∷ w)` / `bar : (literal c ⊗ A) (c ∷ w)` → **`deriv`** / `litPair`. The only `foo`/`bar` in the tree; outside `src/Theory`, so likely predates the agents, but it is the most embarrassing pair in the repo.
- `src/Grammar/Bottom/Properties.agda:62,69,72,97` — `f`, `p`, `q` for an initial-map and two β-laws → `init⊥`, `f≡inl`, `e≡inr`.

## (b) Vocabulary drift — old "Grammar" vocabulary inside `src/Theory/**`

`satG → satTy` is **already done** (`src/Theory/Instances/Monoid/Sat.agda:28-33`;
a concurrent edit landed it during this audit, along with `Display-satG →
Display-satTy` at `Phase/Display.agda:185` and `unambiguous-satG →
unambiguous-satTy` at `Automaton/Implicit/Soundness.agda:1055`). Here is
every analogous case that remains.

### Identifiers
| # | Current | Location | Proposed |
|---|---|---|---|
| 1 | `Gr` (record field) | `Theory/Instances/Monoid/Phase.agda:78` | `Ty` — it is a `TheoryTy ℓA tt` |
| 2 | `Gr` (uses) | `Phase.agda:80`, `82`; `Pipeline/Dyck.agda:63`; `Automaton/TokenStream.agda:453` | `Ty` |
| 3 | `subgrammar` | `Type/Subgrammar/Base.agda:54,55,57,78,85,96,98,117,118,121,122,138,152,163` | `subTy` |
| 4 | `module Subgrammar` | `Type/Subgrammar/Base.agda:53`, `105` | `module SubTy` |
| 5 | `subgrammar-section` | `Type/Subgrammar/Base.agda:96`, `98` | `subTy-section` |
| 6 | `subgrammar-ind-alg` | `Type/Subgrammar/Base.agda:116` | `subTy-ind-alg` |
| 7 | `subgrammar-ind'` | `Type/Subgrammar/Base.agda:121`, `122`, `127` | `subTy-ind'` |
| 8 | `subgrammar-ind` | `Type/Subgrammar/Base.agda:129`, `130` | `subTy-ind` |
| 9 | `mono→subgrammar` | `Type/Subgrammar/Base.agda:151`, `152` | `mono→subTy` |
| 10 | `unambiguous→subgrammar` | `Type/Subgrammar/Base.agda:162`, `163` | `unambiguous→subTy` |
| 11 | `∃subgrammar` | `Type/PropositionalTruncation/Base.agda:66`, `84`, `85` | `∃subTy` |
| 12 | `TranspG` | `Combinator/Decidable/Bracket.agda:261` (+uses) | `TransparentTy` |
| 13 | `ClosG` | `Combinator/Decidable/Bracket.agda:261` (+uses) | `ClosingTy` |
| 14 | `ℓG` (continuation level) | `Grammars/PolyGrammar.agda:170`, and ~40 uses across `Combinator/**` | `ℓK` — `Core.agda:99` already calls the same thing `ℓK`; the two names coexist |
| 15 | `Lang` | `Combinator/Decidable/Widths.agda:181`; `Grammars/ArithTests.agda:42` | `Ty` or `Recognises` — "language" is the semantic notion, `Ty` the syntactic one |

### Module / directory names
| # | Current | Proposed |
|---|---|---|
| 16 | `src/Theory/Type/Subgrammar/Base.agda` | `src/Theory/Type/Subtype/Base.agda` |
| 17 | `src/Theory/Type/Subgrammar/Equalizer.agda` | `src/Theory/Type/Subtype/Equalizer.agda` |
| 18 | `src/Theory/Instances/Monoid/Grammars/Dyck.agda` | `src/Theory/Instances/Monoid/Types/Dyck.agda` (or fold into `Combinator/Grammars/Dyck`) |
| 19 | `src/Theory/Instances/Monoid/Combinator/Grammars/` (10 files) | `.../Combinator/Languages/` or `.../Combinator/Examples/` — the directory holds *parsers*, not grammars (see §d) |
| 20 | `Combinator/Grammars/ArithGrammar.agda` | `Combinator/Grammars/ArithSyntax.agda` |
| 21 | `Combinator/Grammars/PolyGrammar.agda` | `Combinator/Grammars/PolynomialSyntax.agda` (also fixes `Poly` vs `Polynomial`) |

### Comments that carry the old vocabulary (rename or delete)
| # | Text | Location |
|---|---|---|
| 22 | `-- used for Grammars` | `Theory/Base.agda:62` |
| 23 | `` -- `Grammar/String/Unambiguous.agda` argument `` | `Instances/Monoid/Strings.agda:490` |
| 24 | `` -- The `Grammar/String/Terminal.agda` equivalence, recaptured `` | `Instances/Monoid/Strings.agda:520` |
| 25 | `` -- The character-level names from `Grammar.Derivative.Base` `` | `Instances/Monoid/Derivative.agda:55` |
| 26 | `` -- `Grammar/Greedy/Base.agda` states this over a `Trace` `` | `Instances/Monoid/Greedy/Base.agda:2-3` |
| 27 | `` -- `no-nonempty-extension-step` of `Grammar/Greedy/Regex.agda` (a hole there) `` | `Instances/Monoid/Greedy/Base.agda:51` |
| 28 | `` -- `Grammar/RegularExpression/Deterministic.agda`, is the fragment that `` | `Automaton/Implicit/Compile.agda:7` |
| 29 | `-- The old grammar development had to go through `pick-parse` …` | `Type/Equivalence/Base.agda:105-106` |
| 30 | `-- Constant grammars, and how `⊗ₑ` and `⊕ᴰ` pass through them` | `Instances/Monoid/Extension.agda:286` |
| 31 | `-- the grammar the branches present` / `-- ...and as a family of grammars` / `-- a map of grammars` / `-- Isomorphisms of grammars` — 80 uses of the bare word `grammar` in `src/Theory/**` comments | `Combinator/Decidable/Lookahead.agda:57`, `Decidable/Productions.agda:123`, `Regex/Derivative.agda:181`, `Combinator/Core.agda:144`, and 76 others |

**31 renames.** Items 22-30 are also migration notes pointing into `src/Grammar/**`,
i.e. they document the port rather than the code; most should simply be deleted.

## (c) Inconsistent conventions across siblings

| Axis | Side A | Side B | Recommend |
|---|---|---|---|
| **`Automaton` vs `Automata`** | `src/Theory/Instances/Monoid/Automaton/` — 24 files | `src/Theory/Instances/Monoid/Automata/` — `DFA/Base`, `NFA/Base`, `NFA/Properties` | **`Automaton/`**, and move `Automata/{DFA,NFA}` under it. Two sibling directories differing only in Latin number is the single worst layout defect in the tree. |
| **Regex spelling** | `Regex/` (10 files), `Regex.Base`, `RE`, `decide-r` | `Automaton/Implicit/RegExp.agda`, `RegExpExamples.agda`; and `src/Grammar/RegularExpression/` in the old tree | **`Regex`** throughout; rename `Implicit/RegExp*.agda` → `Implicit/Regex*.agda`. |
| **Test-file suffix** | `*Tests.agda` (12: `RegexTests`, `StressTests`, `WidthsTests`, `ArithTests`, `DyckTests`, `PolynomialTests`, `GuardedTests`, `ParseTests`, `UnicodeTests`, `Tests`, `Quicksort/Tests`, `Backreference/RegexTests`) | `*Examples.agda` (10: `GreedyExamples`, `GreedyMaxExamples`, `AnalysisExamples`, `RegExpExamples`, `SoundnessExamples`, `LexiconExamples`, `TokenStreamExamples`, `Greedy/Examples`, `Regex/Examples`, `Monoid/Examples`) plus `Demo.agda`, `ScratchPerf.agda` | Both hold `_ : … ≡ …` assertions. Pick **`*Tests.agda`**; keep `*Examples.agda` only for files with prose narrative. `Demo.agda` and `ScratchPerf.agda` should become `Tests` or be deleted. |
| **`Foo.agda` vs `Foo/Base.agda`** | `Greedy/Base`, `Suffix/Base`, `Lookahead/Base`, `Lex/Base`, `Regex/Base`, `Backreference/Base`, `Combinator/Decidable/Base` | `Strings.agda`, `Precise.agda`, `Unitor.agda`, `Convolution.agda`, `Types.agda`, `Extension.agda`, `GuardedSplit.agda`, `ListPresentation.agda`, `SemanticAction.agda` — all flat, some with sibling directories (`Derivative.agda`+`Derivative/`, `Residual.agda`+`Residual/`, `KleeneStar.agda`+`KleeneStar/`, `Phase.agda`+`Phase/`) | Use **`X.agda` + `X/…` for a re-exporting parent** (the current `Derivative`/`Residual`/`KleeneStar`/`Phase` shape) and **`X/Base.agda` only where there is no parent**. Right now both idioms appear, and `Automaton/Implicit.agda` + `Automaton/Implicit/` vs `Combinator/Decidable/Base.agda` + `Combinator/Decidable/` disagree. |
| **`-elim` vs `Elim`** | `⊕-elim`, `⊗-elim`, `cover-elim`, `Ty-elim`, `var-elim`, `app-elim`, `lam-elim`, `and-elim`, `allFin-elim`, `K-elim`, `⊥Ty↑-elim` | `ClosingElim` (`src/Cubical/Algebra/Theory/Finitary/Free/ClosingElim.agda`), `prop-eliminator` | **`-elim`**. Rename `ClosingElim` → `Closing/Elim` and `prop-eliminator` → `prop-elim`. |
| **`mk*`** | `mkDisplay`, `mkApp`, `mkLam`, `mkVar`, `mkP`, `mkPD`, `mkThryTy`, `mkWeakEq`, `mkImplicitAut`, `mkDirectStr` | `makePshHomStrictPath` (upstream cubical) | **`mk*`** inside this repo; leave the upstream name alone. |
| **`is*` vs `has*`** | `isAcc`, `isDead`, `isMono`, `isNullable`, `isSet*` (~60) | `hasTransition` (`Automata/NFA/Base.agda:64`), `hasPropFibers`, `hasRetraction` (`Type/Equivalence/Base.agda:91,120`) | Keep `is*` for propositions-about-a-thing and `has*` for structure-it-carries. Only three `has*` names exist and all three are fine; the axis is consistent. Record the rule so it stays that way. |
| **`⊢`-suffix** | `⊤Ty-intro`, `id⊢`, `∘⊢` — the `⊢` marks a term | `sub-π`, `sub-intro`, `eq-π`, `⟜-intro`, `⟜-app` — same kind of thing, no marker | The `⊢` suffix marks *combinator on terms* (`id⊢`, `∘⊢`) rather than *term*, which is right; but `⊤Ty-intro` is a term and carries no marker while `id⊢` does. State the rule and apply it. |
| **Trailing `!`** | `winner!` (`Automaton/Lexicon.agda:231`), `Dl-⊗-out!` (`Regex/Derivative.agda:164`) | everything else | Two uses, two different meanings (`winner!` = "total version given a proof"; `Dl-⊗-out!` = "the strengthened version"). Pick one meaning or drop the convention; `winner!` → `winnerOf`, `Dl-⊗-out!` → `Dl-⊗-out-nonNull`. |
| **`Ty` suffix** | `TheoryTy`, `⊤Ty`, `⊥Ty`, `¬Ty`, `DecTy`, `εTy`, `satTy`, `LiftTheoryTy` | `char`, `literal`, `String*`, `Trace`, `Parse`, `Match`, `Run`, `L`, `Lang`, `S`, `Dep` | The `Ty` suffix is used for *connectives* and dropped for *named types*. That is defensible, but `Lang`/`L`/`S` are one-to-three letters for the same kind of thing; see §d. |

## (d) Actively misleading names — highest value

1. **`src/Theory/Instances/Monoid/Combinator/Grammars/` (whole directory)** —
   named "Grammars", but 6 of its 10 files are **parsers**: `Arith.agda:16`
   is `module …Grammars.Arith (𝒯 : C.AnswerFunctor) …` and its own header says
   "`Grammars/Arith` is the parser over it". The grammars live in
   `ArithGrammar.agda` and `PolyGrammar.agda` — inside the same directory. A
   reader looking for the Dyck *grammar* finds `Combinator/Grammars/Dyck.agda`,
   which is the parser; the grammar is at `Instances/Monoid/Grammars/Dyck.agda`.
   → split into `Syntax/` (grammars) and `Parsers/` (parsers).

2. **`src/Theory/Instances/Monoid/Examples.agda`** — not examples. It defines
   `LiteralStar` (`:19`), `literalStar-NIL`/`-CONS`, `dyckBranch`, `DyckCode`,
   `Dyck` — a **library of test fixtures** that other modules import. Every
   other `*Examples.agda` in the tree is a file of `_ : … ≡ …` assertions.
   → `Instances/Monoid/Fixtures.agda` or `Instances/Monoid/Types/Sample.agda`.

3. **`src/Theory/Type/Later/Lex.agda`** — `Lex` here means **lexicographic**
   (`_<lex_`, `isProp<lex`, `dec<lex`). Elsewhere in the same tree
   `src/Theory/Instances/Monoid/Lex/{Base,Regex}.agda` means **lexer**.
   Two unrelated concepts, same three letters, same repo.
   → `Theory/Type/Later/Lexicographic.agda`.

4. **`src/Theory/Type/Subgrammar/Base.agda`** — the module's own first line
   (`:1-2`) says "Subobjects, via the subobject classifier. A subtype of `A`
   is a map `A ⊢ Ω`". It is about **subobjects/subtypes**, and the header says
   so, while every identifier in it says `subgrammar`. → `Subtype`.

5. **`Phase.Gr`** (`src/Theory/Instances/Monoid/Phase.agda:78`) — a field of type
   `TheoryTy ℓA tt` abbreviated to two letters of the *previous* vocabulary. It
   propagates: `dec : Decidable Gr`, `emit : SemanticAction Gr (List Out)`, and
   into comments at `TokenStreamExamples.agda:130`. → `Ty`.

6. **`src/Theory/Instances/Monoid/Automaton/ScratchPerf.agda`** — a *scratch*
   benchmark file, committed, with a definition called `E6` (`:57`), a comment
   `-- BENCH 473108713` (`:55`), and an `oldScan` (`:53`) that exists only to be
   compared against. Nothing imports it. → delete, or `Automaton/Benchmarks.agda`
   with named cases.

7. **`src/Theory/Instances/Monoid/Types.agda`** — reads as "the type
   definitions". It is actually the **instantiation module**: its own header
   (`:5-6`) says "the connectives, `μ`, covers, decidability, lookahead classes
   -- is that instantiation. Nothing here is about parsing." → `Instantiation.agda`
   or `Connectives.agda`.

8. **`src/Theory/Instances/Monoid/Automaton/Greedy.agda`** vs
   **`Automaton/GreedyMax.agda`** — `Greedy` does *not* produce a greedy
   (longest) match with a typed guarantee; `GreedyMax` does, and
   `GreedyExamples.agda:4-9` says `GreedyMax` "supersedes this scan in every
   respect ... If `Automaton/Greedy` is retired, this goes with it". The unqualified name belongs to the superseded module.
   → delete `Greedy.agda`, or rename to `GreedyUnproved.agda` and `GreedyMax` → `Greedy`.

9. **`Case`** (`src/Theory/Type/SemanticAction/Suite.agda:19`) — `Case X = X × X`
   is not a case; it is an **expected/actual pair**, and the neighbouring
   `passes`, `accepts`, `rejects` all read it that way. → `Expected` or `Row`.
   (The larger problem here was fixed mid-audit: this test-assertion DSL used to
   live inside `Theory/Type/SemanticAction/Base.agda` as `module Suite`, `open`ed
   `public`, which is why `Instances/Monoid/Types.agda:42` carries a comment
   about `_at_` clashing with the `at` of `Decidable/Base`. A concurrent edit has
   since split it into its own module; the `_at_` clash and `Case` remain.)

10. **`Lang`** — used at `Combinator/Decidable/Widths.agda:181`
    (`firstS : Lang St ⊢ literal ta ⊗ ⊤Ty`) and `Grammars/ArithTests.agda:42`
    (`decArith : Dec.Decidable (Lang Exp)`) for a `TheoryTy`. "Language" is the
    *semantic* notion (a set of words) and the whole point of the theory-type
    presentation is that these are not that. Also collides with `L` used for the
    same thing in `Automaton/GreedyMax.agda:229` (`L q`) and
    `Combinator/Decidable/Arrow.agda:265` (`L`). Three names, one concept.

11. **`Combinator/Grammars/ArithGrammar.agda:53`** — the comment `-- The grammar`
    sits on `data NT : Type ℓ-zero`, which is the **nonterminal set**, not the
    grammar. The grammar is the `Table` 90 lines further down.

12. **`Combinator/Decidable/Widths.agda`** — "Widths" suggests a utility about
    widths. It is a **parameterised family of grammars requiring k+2 tokens of
    lookahead**, built to show the width hierarchy is strict. → `LookaheadHierarchy.agda`.

13. **`src/Theory/Instances/Monoid/Regex/Sat.agda`** vs
    **`src/Theory/Instances/Monoid/Sat.agda`** vs
    **`src/Theory/Instances/Monoid/Thompson/Construction/Sat.agda`** — three
    modules named `Sat`, in three directories, at three layers (the type, the
    decision combinator, the NFA construction). Only the middle one is guessable
    from the name. → `Sat.agda` (type) stays; `Regex/Sat.agda` → `Regex/SatDec.agda`;
    `Thompson/Construction/Sat.agda` → `.../SatNFA.agda`.

14. **`Combinator/Decidable/Productions.agda:233` `kids`** — a rose-tree child
    list called `kids` in a file whose other names are `Item`, `Prod`, `Table`,
    `Tree`, `node`. → `subtrees`.

---

## Suggested order of work

1. Delete the 151 `-- ...` openers. Mechanical, zero judgement, ~6% of all
   comments in `src/Theory` and the loudest part of the voice.
2. Delete the six benchmark tables (`GreedyExamples`, `GreedyMaxExamples`,
   `Implicit/RegExpExamples`, `LexiconExamples`, `Demo`, `TokenStream`) and the
   `ScratchPerf` file. Keep `Type/Operation/Base.agda:126-134`.
3. Delete the label comments that restate the signature below them (~90 of the
   entries above).
4. Rename the 117 `go`s. Start with `Combinator/Decidable/Bracket.agda` (17) and
   `Combinator/Decidable/STLC.agda` (~30).
5. `Automata/` → `Automaton/`; `Subgrammar` → `Subtype`; `Phase.Gr` → `Phase.Ty`.
6. Then the harder judgement calls: the `{- -}` headers, and splitting
   `Combinator/Grammars/`.
