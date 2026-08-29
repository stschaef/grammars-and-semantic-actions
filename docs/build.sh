#!/usr/bin/env bash
# Regenerates docs/combinators.html from the sources, so the code in the
# document is always exactly the code that typechecks.
set -euo pipefail
cd "$(dirname "$0")/../src"
OUT=../docs/combinators.html

esc() { sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' "$1"; }

code() {
  local path="$1"
  local n; n=$(wc -l < "$path" | tr -d ' ')
  printf '<figure class="src"><figcaption><span class="path">%s</span><span class="lines">%s lines</span></figcaption><pre><code>' "$path" "$n"
  esc "$path"
  printf '</code></pre></figure>\n'
}

exec > "$OUT"

cat <<'HTML'
<!doctype html>
<html lang="en"><head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Combinators for an arbitrary theory</title>
<style>
:root{
  --bg:#fbfaf8; --fg:#1c1a17; --muted:#6b6459; --rule:#e2ddd4;
  --code-bg:#f4f1ec; --code-fg:#23201c; --accent:#8a5a2b; --accent-bg:#f5ece1;
  --warn-bg:#fdf4ec; --warn-br:#d99a5b;
  --mono:"SFMono-Regular",Menlo,Consolas,"DejaVu Sans Mono",monospace;
}
@media(prefers-color-scheme:dark){:root{
  --bg:#16150f; --fg:#eae6dd; --muted:#a49b8c; --rule:#332f27;
  --code-bg:#1e1c16; --code-fg:#e6e1d6; --accent:#d3a06a; --accent-bg:#241f17;
  --warn-bg:#221b12; --warn-br:#a8752f;
}}
*{box-sizing:border-box}
html{scroll-behavior:smooth;scroll-padding-top:1rem}
body{margin:0;background:var(--bg);color:var(--fg);
  font:16px/1.65 Charter,"Iowan Old Style",Georgia,serif;
  -webkit-font-smoothing:antialiased}
#wrap{display:grid;grid-template-columns:250px minmax(0,1fr);max-width:1400px;margin:0 auto}
nav{position:sticky;top:0;align-self:start;max-height:100vh;overflow-y:auto;
  padding:2rem 1rem 3rem;border-right:1px solid var(--rule);font-size:13px;line-height:1.5}
nav b{display:block;font-size:11px;letter-spacing:.09em;text-transform:uppercase;
  color:var(--muted);margin:1.4rem 0 .45rem;font-weight:600}
nav b:first-child{margin-top:0}
nav a{display:block;color:var(--fg);text-decoration:none;padding:.16rem 0;opacity:.8}
nav a:hover{opacity:1;color:var(--accent)}
main{padding:2.5rem 3rem 8rem;min-width:0}
h1{font-size:2rem;line-height:1.2;margin:0 0 .3rem;letter-spacing:-.015em}
h2{font-size:1.4rem;margin:3.5rem 0 .6rem;padding-top:1.2rem;border-top:1px solid var(--rule);
  letter-spacing:-.01em}
h3{font-size:1.08rem;margin:2rem 0 .4rem;letter-spacing:-.005em}
h4{font-size:.95rem;margin:1.3rem 0 .3rem;color:var(--accent)}
p,li{max-width:66ch}
.sub{color:var(--muted);font-size:1.02rem;margin:.2rem 0 1.6rem}
code{font-family:var(--mono);font-size:.86em;background:var(--code-bg);
  padding:.1em .32em;border-radius:3px}
figure.src{margin:1.1rem 0 1.6rem;border:1px solid var(--rule);border-radius:6px;overflow:hidden}
figcaption{display:flex;justify-content:space-between;align-items:center;gap:1rem;
  background:var(--accent-bg);border-bottom:1px solid var(--rule);
  padding:.4rem .8rem;font-family:var(--mono);font-size:11.5px;color:var(--muted)}
figcaption .path{color:var(--accent);font-weight:600}
figure.src pre{margin:0;padding:.9rem 1rem;overflow-x:auto;background:var(--code-bg)}
figure.src code{background:none;padding:0;font-size:12.4px;line-height:1.5;
  color:var(--code-fg);white-space:pre;display:block}
.note{border-left:3px solid var(--accent);background:var(--accent-bg);
  padding:.7rem 1rem;margin:1.2rem 0;border-radius:0 4px 4px 0}
.note p{margin:.35rem 0}
.note>p:first-child{margin-top:0}.note>p:last-child{margin-bottom:0}
.warn{border-left-color:var(--warn-br);background:var(--warn-bg)}
.k{font-size:.82rem;letter-spacing:.07em;text-transform:uppercase;color:var(--accent);
  font-weight:700;display:block;margin-bottom:.25rem}
.warn .k{color:var(--warn-br)}
table{border-collapse:collapse;margin:1.1rem 0;font-size:.92rem;width:100%;max-width:68ch}
th,td{border-bottom:1px solid var(--rule);padding:.42rem .7rem;text-align:left;vertical-align:top}
th{font-size:.78rem;text-transform:uppercase;letter-spacing:.06em;color:var(--muted);font-weight:600}
td code{font-size:.84em}
.lede{font-size:1.06rem}
hr{border:0;border-top:1px solid var(--rule);margin:2.5rem 0}
@media(max-width:900px){#wrap{grid-template-columns:1fr}nav{position:static;max-height:none;
  border-right:0;border-bottom:1px solid var(--rule)}main{padding:1.5rem 1.2rem 5rem}}
</style></head><body><div id="wrap">
<nav>
<b>Orientation</b>
<a href="#what">What this is</a>
<a href="#idea">The one idea</a>
<a href="#glossary">Glossary</a>
<b>The generic core</b>
<a href="#core">Core.agda</a>
<a href="#core-look">&nbsp;&nbsp;look &amp; covers</a>
<a href="#core-node">&nbsp;&nbsp;nodes &amp; precision</a>
<a href="#core-answer">&nbsp;&nbsp;AnswerFunctor</a>
<a href="#core-comb">&nbsp;&nbsp;Combinators</a>
<b>The three answers</b>
<a href="#dec">Dec</a>
<a href="#maybe">Maybe</a>
<a href="#nd">ND</a>
<b>Free term algebras</b>
<a href="#term">Free/Term additions</a>
<b>Client 1 &mdash; scope</b>
<a href="#lguard">Lambda/Guard</a>
<a href="#lscope">Lambda/Scope</a>
<a href="#lname">Lambda/Nameless</a>
<a href="#ltests">ScopeTests</a>
<b>Client 2 &mdash; typing</b>
<a href="#abase">Annotated/Base</a>
<a href="#aguard">Annotated/Guard</a>
<a href="#atyping">Annotated/Typing</a>
<a href="#aelab">Annotated/Elaborate</a>
<a href="#atests">TypingTests</a>
<b>Client 3 &mdash; linear</b>
<a href="#alin">Annotated/Linear</a>
<a href="#alintests">LinearTests</a>
<b>Client 4 &mdash; matching</b>
<a href="#mbase">Match/Base</a>
<a href="#mguard">Match/Guard</a>
<a href="#mjudg">Match/Judgment</a>
<a href="#mbind">Match/Bindings</a>
<a href="#mexh">Match/Exhaustive</a>
<a href="#mtests">Match/Tests</a>
<b>Client 5 &mdash; layout</b>
<a href="#ybase">Layout/Base</a>
<a href="#yguard">Layout/Guard</a>
<a href="#yoffside">Layout/Offside</a>
<a href="#yrender">Layout/Render</a>
<a href="#ytests">OffsideTests</a>
<b>Client 6 &mdash; instances</b>
<a href="#cbase">Class/Base</a>
<a href="#cresolve">Class/Resolve</a>
<a href="#ctests">ResolveTests</a>
<b>Reflection</b>
<a href="#conventions">House conventions</a>
<a href="#internal">Is it internal?</a>
<a href="#trade">⊗ᴰ vs. summed indices</a>
<a href="#boundary">Where it stops</a>
<a href="#build">Building it</a>
</nav>
<main>

<h1>Combinators for an arbitrary theory</h1>
<p class="sub">A port of the parser-combinator framework off the free monoid, with six clients &mdash; scope checking, type checking, linear typing, pattern matching, the offside rule and typeclass instance resolution &mdash; each written once and run at three different notions of &ldquo;answer&rdquo;.</p>

<h2 id="what">What this is</h2>

<p class="lede">The existing framework in this repository parses <em>strings</em>. This is that framework with the strings taken out, plus six clients, not one of which is a parser.</p>

<p>The setting is a <strong>finitary algebraic theory</strong> &mdash; a signature of operations, possibly with equations. Every such theory has a free model, and a <strong>grammar</strong> is a predicate on the elements of that model:</p>

<pre><code>TheoryTy ℓ s  =  ↓M s → Type ℓ</code></pre>

<p>Which model you pick decides what you are doing:</p>

<table>
<tr><th>Theory</th><th>Elements of the free model</th><th>So a &ldquo;grammar&rdquo; is&hellip;</th></tr>
<tr><td>monoid</td><td>strings</td><td>a language, with parse trees</td></tr>
<tr><td>commutative monoid</td><td>bags / multisets</td><td>a predicate on multisets</td></tr>
<tr><td>a term signature</td><td>abstract syntax trees</td><td>a predicate on syntax</td></tr>
</table>

<p>The last row is what this work uses. A grammar over a lambda signature is a predicate on lambda terms &mdash; and &ldquo;is this term well-scoped?&rdquo; and &ldquo;does this term have type <code>A</code>?&rdquo; are exactly such predicates. So a scope checker and a type checker are <em>parsers</em>, in a precise sense, and they can be built from the same combinators.</p>

<p>Then the question becomes how far the sense stretches, and the answer is the interesting part. Change the model to <em>values</em> and the same combinators do pattern matching; to <em>token streams</em> and they do the offside rule, which is the standard counterexample to &ldquo;syntax is context-free&rdquo;; to <em>types</em> and they do typeclass instance resolution. Change nothing but a client&rsquo;s <code>Slots</code> and intuitionistic typing becomes linear typing. Six clients, one <code>fix step</code>.</p>

<div class="note"><span class="k">The payoff</span>
<p>Each client is written <strong>once</strong>, mentioning no particular notion of answer, and then instantiated three ways: as a <em>decision procedure</em> that returns a proof or a refutation, as a <em>partial function</em> that returns at most one result, and as an <em>enumerator</em> that returns every derivation. Same source text, three behaviours.</p></div>

<h2 id="idea">The one idea</h2>

<p>Here is the whole reason the port is smaller than the original, in two pictures.</p>

<p><strong>Parsing a string.</strong> A parser eats a <em>prefix</em> and leaves a <em>suffix</em> behind. Something has to consume the leftover, so every parser is written in continuation-passing style: &ldquo;give me a way to handle the rest, and I&rsquo;ll handle the whole thing.&rdquo; That is where the original framework&rsquo;s <code>Parser ℓK a c A</code>, its quantification over all continuations, and its <code>ParserTag</code> bookkeeping come from.</p>

<p><strong>Checking a term.</strong> A constructor consumes the <em>entire</em> term. <code>app f a</code> is fully accounted for by <code>f</code> and <code>a</code>; there is no leftover. So the continuation disappears, and with it the rank-2 quantification, the tags, and the three separate rules for &ldquo;consume this letter&rdquo;, &ldquo;consume any letter&rdquo; and &ldquo;consume nothing&rdquo;. They collapse into a single rule about nodes.</p>

<div class="note"><span class="k">Rule of thumb</span>
<p>Every feature of the original that mentions <em>lookahead width</em>, <em>the alphabet</em>, or <em>the leftover input</em> is monoid-specific and vanishes. Everything that mentions <em>recursion</em>, <em>alternatives</em>, or <em>what an answer is</em> survives unchanged.</p></div>

<h2 id="glossary">Glossary</h2>

<p>Six pieces of jargon carry most of the weight. Everything below is written in terms of them.</p>

<h4>grammar (<code>TheoryTy</code>) &mdash; a predicate on model elements</h4>
<p>Not a set of strings: a <em>proof-relevant</em> predicate. <code>A m</code> is the type of derivations showing <code>m</code> satisfies <code>A</code>. If that type has two distinct inhabitants, the grammar is ambiguous at <code>m</code>. If it is a proposition, the grammar is unambiguous &mdash; and that is a fact about the type, not a theorem you prove afterwards.</p>

<h4><code>_⊢_</code> &mdash; a map of grammars</h4>
<p><code>A ⊢ B</code> is <code>∀ m → A m → B m</code>: convert a derivation of <code>A</code> into one of <code>B</code>, at every element, uniformly. This is the language&rsquo;s notion of morphism. Writing something as a <code>⊢</code>-term rather than as an ordinary Agda function is what &ldquo;internal to the DSL&rdquo; means here.</p>

<h4><code>&amp;</code>, <code>⊕</code>, <code>⊕ᴰ</code> &mdash; and, or, big-or</h4>
<p>All computed pointwise: <code>(A &amp; B) m</code> is a pair, <code>(A ⊕ B) m</code> is a tagged union, <code>⊕ᴰ Y A</code> at <code>m</code> is a <code>y</code> together with a derivation of <code>A y</code>.</p>

<h4><code>▷</code> (&ldquo;later&rdquo;) &mdash; available only at strictly smaller elements</h4>
<p>A modality from guarded recursion. <code>▷ A</code> at <code>m</code> is &ldquo;an <code>A</code> at every element strictly below <code>m</code>&rdquo;, for some well-founded order. This is how recursion is made safe <em>by typing</em>: a recursive call is only well-typed if it descends. Left recursion is a type error, not a hang.</p>

<h4><code>Cover</code> &mdash; a total, non-overlapping classification</h4>
<p>A family <code>Λ : Y → grammar</code> with two laws: <code>total</code> (every element is in some class) and <code>disjoint</code> (no element is in two). Case analysis goes through a cover. In the string world the classes are &ldquo;starts with letter <code>c</code>&rdquo; &mdash; that is LL(1) lookahead. Here they are &ldquo;is a node of operation <code>o</code>&rdquo;.</p>

<h4><code>Ans</code> &mdash; what an answer is</h4>
<p>The parameter that makes one grammar give three checkers. Concretely one of:</p>
<table>
<tr><th>Answer</th><th>Meaning</th><th>At a fork it&hellip;</th></tr>
<tr><td><code>DecTy A = A ⊕ ¬A</code></td><td>a proof or a refutation</td><td>decides both, combines</td></tr>
<tr><td><code>Maybe A</code></td><td>at most one derivation</td><td>takes the left one</td></tr>
<tr><td><code>ND A</code></td><td>a list of derivations</td><td>keeps both</td></tr>
</table>
<p><code>Dec</code> is the only one that is <em>intrinsically</em> correct: its type <em>is</em> the correctness statement. <code>ND</code> returns a list and nothing types &ldquo;that list is complete&rdquo; &mdash; a real gap, flagged in the source.</p>

HTML

cat <<'HTML'
<h2 id="core">The generic core</h2>

<p>One module, parameterised by a theory and nothing else. It defines what an answer is, what a node is, and how recursion and case analysis work. Read it in four passes; the whole file is at the end of the section.</p>

<h3 id="core-look">Case analysis: <code>look</code> and covers</h3>

<p>The first question any checker faces is <em>which rule applies?</em> The undisciplined way is to pattern-match on the term. The disciplined way is to go through a cover, because a cover carries the two facts that make the case split sound: the classes are exhaustive, and they do not overlap.</p>

<pre><code>look : Cover Y Λ → ((y : Y) → D &amp; Λ y ⊢ C) → D ⊢ C
look cov br = ⊕ᴰ-elim br ∘⊢ &amp;⊕ᴰ-dist ∘⊢ (id⊢ ,&amp; (cov .total ∘⊢ ⊤Ty-intro))</code></pre>

<p>Read right to left: observe the element through the cover (<code>total</code>), which names a class; distribute; then run the branch for that class. Inside branch <code>y</code> you additionally <em>have</em> <code>Λ y</code> as a hypothesis &mdash; you know which class you are in, and that turns out to matter a lot later.</p>

<div class="note"><span class="k">Where this comes from</span>
<p>This is the exact sibling of <code>look⊗</code> in the string framework, which splits on the first character via the lookahead cover. Replacing that cover with any other cover is what makes the case analysis theory-generic. For a term algebra the cover is by root constructor &mdash; and since the root always determines the production, <strong>prediction over a term algebra is always LL(1)</strong>. All the machinery the string world needs for wider lookahead simply has nothing to do here.</p></div>

<h3 id="core-node">Nodes and precision</h3>

<p>Two definitions do the structural work.</p>

<pre><code>NodeAt o m = Σ[ ms ] (op o ms ≡ m)          -- "m is built by operation o"
Precise o  = ∀ m → isProp (NodeAt o m)      -- "...in exactly one way"</code></pre>

<p><code>NodeAt o</code> is the cover&rsquo;s class. <code>Precise o</code> says the decomposition is unique, and it is what lets a checker <em>refute</em>: if one argument fails, the whole node fails &mdash; but only because there is no other way to split the term that might have worked.</p>

<div class="note"><span class="k">Why this replaces &ldquo;the alphabet is discrete&rdquo;</span>
<p>A free term algebra is precise at <em>every</em> operation: that is constructor injectivity, and it is proved once, generically, in <code>Free/Term</code>. The free monoid is precise almost nowhere &mdash; a word splits many ways &mdash; which is exactly why the string framework has three bespoke token rules instead of one node rule.</p></div>

<p>Then the node itself:</p>

<pre><code>NodeArgs ℓ o = (ms : interpIn o ↓M) (a : arities σ o) → TheorySet ℓ (sortOf o a)

⊗ᴰ o As m = Σ[ ms ] ((op o ms ≡ m) × (∀ a → ty (As ms a) (ms a)))</code></pre>

<p>&ldquo;<code>m</code> is <code>o</code> applied to arguments <code>ms</code>, and each argument satisfies its slot grammar.&rdquo; The important letter is the <code>ms</code> in <code>NodeArgs</code>: <strong>a slot&rsquo;s grammar may depend on the other slots&rsquo; values.</strong></p>

<div class="note warn"><span class="k">Why the dependency is not optional</span>
<p>The library already had an operation tensor, <code>⊗ᵘ</code>, with <em>independent</em> slots. It cannot state a binder. In <code>lam x t</code> the body <code>t</code> is checked in the context <code>Γ, x</code> &mdash; and <code>x</code> is the value in slot zero. With independent slots there is nowhere to say that. <code>⊗ᵘ</code> is the constant case of <code>⊗ᴰ</code>, so nothing is lost by generalising.</p></div>

<h3 id="core-answer">The <code>AnswerFunctor</code></h3>

<p>Six fields. This is the entire interface a new backend must implement.</p>

<table>
<tr><th>Field</th><th>In words</th></tr>
<tr><td><code>Ans</code></td><td>What an answer about a grammar <em>is</em>.</td></tr>
<tr><td><code>Ans-map&amp;</code></td><td>Relabel an answer along a renaming of grammars &mdash; given a hypothesis both directions may use.</td></tr>
<tr><td><code>Ans-⊕&amp;</code></td><td>An answer about <code>A</code> and one about <code>B</code> combine into one about <code>A</code>&nbsp;or&nbsp;<code>B</code>. <em>This single field is the entire difference between the three backends.</em></td></tr>
<tr><td><code>Ans-&amp;&amp;</code></td><td>&hellip;and the conjunctive counterpart. This is how a <em>side condition</em> reaches a rule: an operation has exactly its arity many slots, so a condition that is not itself an argument has nowhere of its own to sit, and gets conjoined with the whole node.</td></tr>
<tr><td><code>Ans-ofDec</code></td><td>Any decision is an answer. The one door a side condition comes through.</td></tr>
<tr><td><code>Ans-node</code></td><td>Answers at the arguments give an answer at the node.</td></tr>
</table>

<h4>Two refinements, and the asymmetry between them</h4>

<p><code>CovariantAnswer</code> adds a plain <code>fmap</code> and an <em>empty answer</em> at any grammar. <code>Dec</code> has neither, and the second refusal is the interesting one: <code>⊤Ty ⊢ DecTy A</code> at an arbitrary <code>A</code> <em>is</em> a decision procedure, not a default. One cannot decline to decide.</p>

<p><code>CommittingAnswer</code> adds <code>Ans-route</code>, which answers an indexed sum <code>⊕[ y ∈ Y ] Φ y</code> by consulting a <code>Route</code> &mdash; a cover of the model by <code>Maybe Y</code> &mdash; instead of asking every alternative. This is the field the framework was missing, and it is what a judgment whose <em>premise index is an output</em> needs. See <a href="#cresolve">instance resolution</a>, where the route&rsquo;s <code>disjoint</code> turns out to be coherence.</p>

<div class="note"><span class="k">The split, stated once</span>
<p>An answer that can <strong>commit</strong> routes; an answer that can <strong>give up</strong> enumerates. <code>Ans-route</code> needs a cover and gives you back which alternative was taken. <code>Ans-anyFin</code> needs <code>Ans-empty</code>, asks everything, and cannot tell you &mdash; because more than one may have fired. So a judgment whose alternatives are <em>not</em> known exclusive is available at <code>Maybe</code> and <code>ND</code> and <strong>unwritable at <code>Dec</code></strong>. That is not a hole to patch; an answer has to say what it does with the alternatives it did not take.</p></div>

<h4>Why <code>Ans-map&amp;</code> carries a hypothesis</h4>

<p>A checker constantly needs to move between a grammar and its one-step unfolding &mdash; between &ldquo;<code>t</code> is well-scoped&rdquo; and &ldquo;<code>t</code> is an application whose parts are well-scoped&rdquo;. Going one way is fine. Going back is <em>not</em>: from &ldquo;<code>t</code> is well-scoped&rdquo; alone you cannot produce an application node, because <code>t</code> might be a variable.</p>

<p>Unless you already know the head. Which is exactly what the cover&rsquo;s class gives you. So:</p>

<pre><code>Ans-map&amp; : ty A &amp; H ⊢ ty B → ty B &amp; H ⊢ ty A → ty (Ans A) &amp; H ⊢ ty (Ans B)</code></pre>

<p>with <code>H = NodeAt o</code>. Both directions become writable, and both are honest <code>⊢</code>-terms rather than one-off functions at a single element. Plain <code>Ans-map</code> falls out by taking <code>H = ⊤Ty</code>.</p>

<h3 id="core-comb">The combinators</h3>

<p>Parameterised by an answer, an index type <code>X</code>, and a well-founded order. <code>X</code> is &ldquo;one component per what?&rdquo; &mdash; per nonterminal in a grammar, per context in the scope checker, per (context, type) pair in the type checker. Nothing constrains it, which is why an unbounded index costs nothing.</p>

<table>
<tr><th>Name</th><th>In words</th></tr>
<tr><td><code>Step A</code></td><td>What you write: an answer at every index, <em>given</em> answers at all strictly smaller elements.</td></tr>
<tr><td><code>Checker A</code></td><td>What you get: an answer at every index, unconditionally.</td></tr>
<tr><td><code>fix</code></td><td>Turns the first into the second. This is Löb induction; the guard is what makes it sound.</td></tr>
<tr><td><code>callAt</code></td><td>The recursive call. Takes a proof that you are descending; without one it does not typecheck.</td></tr>
<tr><td><code>_&lt;|&gt;_</code></td><td>Alternation.</td></tr>
<tr><td><code>side</code></td><td>A decidable side condition, read by whatever the answer is.</td></tr>
</table>

<div class="note"><span class="k">Compare</span>
<p>In the string framework the recursive call is <code>call</code>/<code>callAt</code>/<code>pApp</code>, and it has to thread a continuation through. Here, with no leftover input, it is <em>literally just</em> <code>▷app</code> &mdash; open the &ldquo;later&rdquo; box at a smaller element.</p></div>

HTML
code Theory/Combinator/Core.agda

cat <<'HTML'
<h2 id="dec">Answer 1 &mdash; <code>Dec</code>: decide, with a refutation</h2>

<p><code>DecTy A = A ⊕ ¬A</code>. The answer is a proof or a disproof, so the checker is sound <em>and</em> complete because that is what its type says. No separate theorem.</p>

<p>Two things do real work. <code>decΠFin</code> decides a finite conjunction &mdash; a node holds when all its slots hold, and an operation has finitely many arguments, so this fold is the entire search a node performs. And <code>Ans-node</code>&rsquo;s <code>no</code> case is the only place <code>Precise</code> is used: to refute the node from a refuted slot you must know the term does not decompose some other way.</p>

<div class="note"><span class="k">Cost</span>
<p>Alternation at <code>Dec</code> cannot short-circuit. To build a refutation of <code>A ⊕ B</code> you genuinely need refutations of both, so <code>_&lt;|&gt;_</code> runs every branch. Nested alternation is exponential, and no choice of answer can fix that &mdash; only committing via a cover can.</p></div>

HTML
code Theory/Combinator/Answer/Decidable.agda

cat <<'HTML'
<h2 id="maybe">Answer 2 &mdash; <code>Maybe</code>: at most one</h2>

<p>Returns a derivation or nothing, with no refutation. <code>Ans-⊕&amp;</code> is <code>orElse</code>, which commits to the left &mdash; so this is the PEG reading of a grammar, and an ambiguous one silently drops derivations. <code>Ans-node</code> ignores <code>Precise</code> entirely: with nothing to refute, a node is just a traversal.</p>

HTML
code Theory/Combinator/Answer/Incomplete.agda

cat <<'HTML'
<h2 id="nd">Answer 3 &mdash; <code>ND</code>: all of them</h2>

<p><code>Ans-⊕&amp;</code> is <code>appendND</code> where <code>Maybe</code>&rsquo;s is <code>orElse</code>, so nothing is dropped. <code>Ans-node</code> is the cartesian product of the slots&rsquo; enumerations &mdash; the one place the string framework&rsquo;s binary strength genuinely becomes n-ary, since an operation has as many arguments as it has.</p>

<p><code>ND A</code> is a <code>μ</code>, so <code>ndToList</code>/<code>ndFromList</code> exist to reach the fold and come back.</p>

<div class="note warn"><span class="k">The honest gap</span>
<p>Completeness here is a claim about the grammar, not a consequence of the type. <code>ND A</code> is a list of derivations and nothing types &ldquo;these are all of them&rdquo;. Only <code>Dec</code> is intrinsic. An <em>exhaustive</em> answer &mdash; a list together with a proof that every derivation is in it &mdash; would close this, and would be the most interesting backend to add.</p></div>

HTML
code Theory/Combinator/Answer/NonDet.agda

cat <<'HTML'
<h2 id="term">What a free term algebra gives you for free</h2>

<p>The core asks a signature for two things: precision, and a well-founded order. A free term presentation has both, for every operation, and neither depends on the signature &mdash; so they are proved once, generically, and every future client inherits them.</p>

<table>
<tr><th>Added</th><th>In words</th></tr>
<tr><td><code>opT-inj</code></td><td>A node determines its arguments. Constructor injectivity for the indexed W-type.</td></tr>
<tr><td><code>preciseTerm</code></td><td>&hellip;which is exactly <code>Precise o</code>, stated where the core can use it.</td></tr>
<tr><td><code>headOpT</code></td><td>The head operation, for the no-confusion a checker needs.</td></tr>
<tr><td><code>termSize</code>, <code>argSize&lt;</code></td><td>The measure the guard descends on, and the fact that every argument is smaller.</td></tr>
</table>

<p>Contrast the string world, which has neither: a word splits many ways, so it needs bespoke token rules; and its order is the proper-suffix relation, justified separately with a length measure.</p>

HTML
code Theory/Free/Term.agda

cat <<'HTML'
<h2 id="lguard">Client 1 &mdash; the scope checker</h2>

<p>&ldquo;Are all the variables in this lambda term bound?&rdquo; A predicate on terms, indexed by the context you are checking against.</p>

<h3>Guard: what the theory owes</h3>

<p>Three obligations, all discharged mechanically:</p>

<table>
<tr><th>Obligation</th><th>How</th></tr>
<tr><td><code>preciseλ</code></td><td>Constructor injectivity, by <em>projection</em> rather than matching &mdash; a total function that reads a field out with a default.</td></tr>
<tr><td><code>tmSize</code> + <code>Subterm</code></td><td>A size measure, fed to <code>ilexOrder</code>. Gives <code>callFun</code>/<code>callArg</code>/<code>callBody</code>: the descent proofs the recursive calls need.</td></tr>
<tr><td><code>nodeCover</code></td><td>Every term is a node of exactly one operation. <code>total</code> is the term algebra&rsquo;s induction; <code>disjoint</code> is no-confusion via the head classifier <code>clsL</code>.</td></tr>
</table>

<div class="note"><span class="k">Read the cover carefully</span>
<p><code>nodeCover</code> is fourteen lines, and it is the analogue of the string framework&rsquo;s <code>Λ-total</code> and <code>Λ-disjoint</code> &mdash; which cost a page of reasoning about how a word splits. That difference is the whole story of why term algebras are easier to predict than strings.</p></div>

HTML
code Theory/Instances/Lambda/Guard.agda

cat <<'HTML'
<h3 id="lscope">The scope checker itself</h3>

<p>Nothing in this file mentions <code>Dec</code>, <code>Maybe</code> or <code>ND</code>. Read it in four parts.</p>

<h4>1. Membership, as a grammar</h4>
<p><code>memB</code> is a <code>Bool</code>, and <code>InCtx Γ x = memB x Γ ≡ true</code>. Using a boolean makes it a <em>proposition</em> and <em>decidable</em> at the same time, with no extra work. <code>decInCtx</code> packages that as a <code>Decidable</code>, which any answer can read via <code>Ans-ofDec</code>.</p>

<h4>2. The grammar</h4>
<pre><code>Scope Γ (tvar x)   = InCtx Γ x
Scope Γ (tapp t u) = Scope Γ t × Scope Γ u
Scope Γ (tlam x t) = Scope (x ∷ Γ) t</code></pre>
<p>Note what falls out: this is built from propositions by products, so <code>Scope Γ t</code> is itself a proposition. <strong>Unambiguity is definitional</strong>, not a theorem &mdash; which is also why <code>ND</code> will find exactly one derivation rather than several.</p>

<h4>3. Slots</h4>
<p>One entry per operation, saying what each argument must satisfy. The <code>lamOp</code> line is the payoff of <code>⊗ᴰ</code>:</p>
<pre><code>Slots lamOp Γ ms (suc zero) = ScopeSet (ms zero ∷ Γ)</code></pre>
<p>The body&rsquo;s grammar mentions <code>ms zero</code> &mdash; the bound name, which is <em>slot zero&rsquo;s value</em>. With independent slots this line cannot be written at all.</p>

<h4>4. Unfolding and the step</h4>
<p><code>rollNode</code> and <code>unrollNode</code> are the one-step unfolding, both directions, both <code>⊢</code>-terms. <code>unrollNode</code> takes the cover&rsquo;s cell as a hypothesis, for the reason given earlier: knowing the head is what makes the backward direction possible.</p>
<p>Then <code>step</code> is three lines: <code>look</code> over the cover, and in each branch, build the node answer and relabel it. The recursive calls appear as <code>callAt</code> with a descent proof, and the <code>lam</code> case calls at a <em>different index</em> &mdash; <code>ms zero ∷ Γ</code> &mdash; which is how the binder extends the context.</p>

HTML
code Theory/Instances/Lambda/Scope.agda

cat <<'HTML'
<h3 id="lname">What the derivation was for</h3>

<p>A checker that only says <em>yes</em> is a checker nobody ships. <code>Scope Γ t</code> is data, and the data answers a question the checker already asked: <code>InCtx</code> is not a boolean but a chain of &ldquo;not this binder&rdquo; steps ending in a hit, and <strong>counting the steps is the de Bruijn index</strong>. So conversion to nameless form is a <em>fold of the derivation</em>, not a second walk over the context.</p>

<p>The boundary out of the language is crossed exactly once, and it is spelled the same way in every client that has a readout:</p>

<pre><code>compile Γ = observe (CD.scoped Γ) (semact-dec (nameAction Γ))</code></pre>

<p>Three internal terms composed &mdash; the checker <code>⊤Ty ⊢ DecTy (Scope Γ)</code>, the action <code>semact-dec</code> builds from <code>nameAction</code>, and <code>observe</code>, the one place a <code>⊤Ty</code>-map is read out. Nothing is hand-rolled, and <code>db-shadow</code> is <code>refl</code>, so the typechecker performs the conversion.</p>

HTML
code Theory/Instances/Lambda/Nameless.agda

cat <<'HTML'
<h3 id="ltests">Running it three ways</h3>

<p>Every test is <code>refl</code>, so they are executed by the typechecker: the combinators, the guarded fixpoint and all three answers reduce on concrete input. Worth reading for what it demonstrates rather than for the code:</p>

<table>
<tr><th>Test</th><th>What it pins down</th></tr>
<tr><td><code>dec-capture</code> is <code>false</code></td><td><code>λx. x y</code> is not closed &mdash; the binder does not capture <code>y</code>.</td></tr>
<tr><td><code>dec-capture-in-ctx</code> is <code>true</code></td><td>&hellip;but it is fine with <code>y</code> in scope.</td></tr>
<tr><td><code>dec-shadow</code> is <code>true</code></td><td><code>λx.λx. x</code> &mdash; the inner binder shadows.</td></tr>
<tr><td><code>nd-*</code> are all <code>0</code> or <code>1</code></td><td>Never 2: <code>Scope</code> is a proposition, so the enumerator cannot find duplicates.</td></tr>
<tr><td><code>no-open</code></td><td>At <code>Dec</code> an out-of-scope term returns an actual <em>refutation</em>, not a bit.</td></tr>
</table>

HTML
code Theory/Instances/Lambda/ScopeTests.agda

cat <<'HTML'
<h2 id="abase">Client 2 &mdash; the type checker</h2>

<p>A simply typed lambda calculus, checked against a type. The interesting design decision is in the signature.</p>

<h3>The signature, with annotations in the operations</h3>

<p>Operations may be <em>indexed by external data</em>. Here <code>appOp B</code> is &ldquo;apply, at argument type <code>B</code>&rdquo; and <code>lamOp B</code> is &ldquo;abstract, at domain <code>B</code>&rdquo;. That is how an annotation enters a signature, and it makes the calculus syntax-directed:</p>

<pre><code>Γ ⊢ var x       ⇐ A   iff  Γ(x) = A
Γ ⊢ app[B] f a  ⇐ A   iff  Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B
Γ ⊢ lam[B] x t  ⇐ A   iff  A = B ⇒ C      and  Γ,x:B ⊢ t ⇐ C</code></pre>

<p>Every premise&rsquo;s type is determined by the conclusion&rsquo;s plus the node&rsquo;s annotation. No search, no existential.</p>

<div class="note warn"><span class="k">This is the load-bearing choice</span>
<p>Drop <code>B</code> from application and the rule becomes <code>∃B. Γ ⊢ f ⇐ B ⇒ A and Γ ⊢ a ⇐ B</code> &mdash; a search over infinitely many types. See <a href="#boundary">Where it stops</a>.</p></div>

<p>Types are a plain datatype with decidable equality, deliberately: keeping them <em>outside</em> the theory means type equality is an ordinary decision rather than another grammar problem. The rest of the file is the term model &mdash; a plain <code>data</code>, chosen so everything reduces and the <code>refl</code> tests work.</p>

HTML
code Theory/Instances/Annotated/Base.agda

cat <<'HTML'
<h3 id="aguard">Guard</h3>

<p>Identical in shape to the lambda one: precision by projection, a size measure, the subterm order, and the node cover. The classifier <code>clsA</code> returns the <em>operation</em> including its annotation, so <code>aapp ι f a</code> and <code>aapp (ι⇒ι) f a</code> land in different classes &mdash; which is right, and costs nothing.</p>

<div class="note"><span class="k">An infinite cover is fine</span>
<p><code>AOp</code> is infinite, since <code>appOp B</code> carries a type. A <code>Cover</code> does not care: <code>total</code> and <code>disjoint</code> say nothing about the size of the index. What <em>would</em> care is a sum <em>over</em> the cells &mdash; and avoiding that sum is precisely what <code>Ans-map&amp;</code>&rsquo;s hypothesis buys.</p></div>

HTML
code Theory/Instances/Annotated/Guard.agda

cat <<'HTML'
<h3 id="atyping">The type checker</h3>

<p>Same four-part shape as the scope checker.</p>

<h4>Index and side conditions</h4>
<p>The index is <code>Ctx × Ty</code> &mdash; a checking judgment. Two side conditions, each a grammar with a decision: <code>Look Γ A</code> (&ldquo;this variable has type <code>A</code>&rdquo;) and <code>ArrHead A B</code> (&ldquo;<code>A</code> is an arrow with domain <code>B</code>&rdquo;). Both are propositions; both are decided by ordinary equality tests.</p>

<h4>The judgment</h4>
<p>Defined by recursion on the term, so &mdash; as with <code>Scope</code> &mdash; it is a proposition, and &ldquo;an annotated term has at most one derivation at a given type&rdquo; is definitional.</p>

<h4>Slots &mdash; the dependency used twice</h4>
<pre><code>Slots (lamOp B) (Γ , A) ms (suc zero) = DerSet ((ms zero , B) ∷ Γ , cod A)</code></pre>
<p>The body&rsquo;s <em>context</em> is extended with <code>ms zero</code>, the bound name from slot zero; and the body&rsquo;s <em>type</em> is <code>cod A</code>, read off the index. Two dependencies in one line, neither expressible with independent slots.</p>

<h4>The step</h4>
<p>Identical structure to the scope checker: <code>look</code> over the cover, a node answer per branch, relabel. The recursive calls go to <em>different indices</em> &mdash; the function position at <code>Γ ⊢ ⇐ B ⇒ A</code>, the argument at <code>Γ ⊢ ⇐ B</code>, the lambda body at an extended context and a smaller type.</p>

HTML
code Theory/Instances/Annotated/Typing.agda

cat <<'HTML'
<h3 id="aelab">Elaboration: the same trick, one level up</h3>

<p>Worth repeating because it is the argument for proof-relevance generally. <code>Der (Γ , A) t</code> could have had a variable rule reading <code>lookC Γ x ≡ just A</code>. That is the same proposition &mdash; and it carries nothing. <code>Lookup Γ A x</code> carries the <em>position</em>, so <code>elab</code> emits <code>cvar (deBruijn …)</code> by reading rather than by searching.</p>

<p><code>elab</code> has no failure case, and that is the point: a derivation <em>is</em> the proof that the term checks, so elaboration is total on derivations. Ill-typed input never reaches the fold &mdash; <code>elab-bad</code> is <code>nothing</code> because the checker refuted, not because the fold gave up.</p>

HTML
code Theory/Instances/Annotated/Elaborate.agda

cat <<'HTML'
<h3 id="atests">Running it three ways</h3>

<table>
<tr><th>Test</th><th>What it pins down</th></tr>
<tr><td><code>dec-id-wrong-dom</code> is <code>false</code></td><td>The annotation must match the type being checked against.</td></tr>
<tr><td><code>dec-id-not-arrow</code> is <code>false</code></td><td>A lambda cannot have a base type.</td></tr>
<tr><td><code>dec-konst-wrong</code> is <code>false</code></td><td>Shadowing resolves the way it should.</td></tr>
<tr><td><code>dec-bad-dom</code> is <code>false</code></td><td>The application&rsquo;s annotation and the function&rsquo;s must agree.</td></tr>
<tr><td><code>dec-nested</code> is <code>true</code></td><td><code>λf:ι⇒ι. λx:ι. f x</code> &mdash; nesting, application and lookup together.</td></tr>
<tr><td><code>nd-*</code> are <code>0</code> or <code>1</code></td><td>Typing is a proposition, so no duplicate derivations.</td></tr>
</table>

HTML
code Theory/Instances/Annotated/TypingTests.agda

cat <<'HTML'
<h2 id="alin">Client 3 &mdash; linear typing: the same terms, a different discipline</h2>

<p>This is the client that was expected to break the framework. The multiplicative rule splits the context:</p>

<pre><code>Γ₁ ⊢ f : B ⊸ A     Γ₂ ⊢ a : B
------------------------------  Γ = Γ₁ ⊎ Γ₂
         Γ ⊢ f a : A</code></pre>

<p>and <code>Γ₁</code>, <code>Γ₂</code> look like <em>outputs</em> &mdash; which by the rule of thumb would owe a <code>Route</code> over exponentially many splits.</p>

<div class="note"><span class="k">They are not outputs</span>
<p>Which variables <code>f</code> consumes is a <em>syntactic</em> fact about <code>f</code>. So <code>Γ₁ = keep Γ f</code> is a function of the conclusion&rsquo;s context and slot zero&rsquo;s <em>value</em> &mdash; and a slot index computed from another slot&rsquo;s value is exactly what <code>⊗ᴰ</code> is. No search, no route.</p>
<p>Stated generally: <strong><code>⊗ᴰ</code>&rsquo;s dependency <em>is</em> the leftover/threading discipline.</strong> In the string framework the same idea is the continuation &mdash; what the head leaves for the tail; here it is what the function leaves for the argument. Same shape, different theory.</p></div>

<p>What is genuinely out of reach is linear <em>inference</em>. If the types were unknown the split would stop being computable, and then it would be a route after all. Checking is syntax-directed; inference is not. That is the honest boundary, and it is the same one the annotation on <code>appOp B</code> draws.</p>

<h4>Where the side condition lives, and why it moved</h4>

<p><code>keep</code> computes the split, but nothing so far says the halves <em>partition</em> &mdash; that every variable is used exactly once rather than zero times or twice. That is a condition on the <em>application</em>, and an operation has exactly its arity many slots, so there is no third slot to put it in.</p>

<p>An earlier version of this file hung it off the function&rsquo;s slot, <code>Slots (appOp B) … theFun = PartSet … &amp;Set LinSet …</code>. It typechecks, and it misstates the rule: the partition constrains the application, not the function, and <code>Slots</code> stopped being a list of premises. The condition now sits at the <em>node</em>,</p>

<pre><code>Cell o i = ⊗ᴰSet o (Slots o i) &amp;Set SideSet i</code></pre>

<p>which leaves <code>Slots</code> character for character <a href="#atyping"><code>Typing</code></a>&rsquo;s, but for <code>keep</code>, and collects every rule&rsquo;s condition in one place. <a href="#yoffside">Layout</a> is <em>forced</em> into the same shape by a nullary operation, which is the argument for making it the house rule rather than a local trick; see <a href="#conventions">the conventions</a>.</p>

<h4 id="alintests">Two disciplines, one syntax</h4>

<p><code>LinearTests</code> reports each term as <code>(intuitionistic , linear)</code> against the same syntax, the same node cover and the same <code>fix step</code>; only the <code>Slots</code> differ. <code>konst</code> is <code>(true , false)</code> &mdash; weakening. <code>dbl</code>, which uses <code>f</code> twice, is <code>(true , false)</code> &mdash; contraction. Where they agree the term is linear; where they differ it is the discipline talking, not the framework.</p>

HTML
code Theory/Instances/Annotated/Linear.agda
code Theory/Instances/Annotated/LinearTests.agda

cat <<'HTML'
<h2 id="mbase">Client 4 &mdash; pattern matching, and what a nullary operation costs</h2>

<p>The index/model split here is the mirror image of the type checker&rsquo;s. There the index was a type and the guard descended on the term; here the index is a <em>pattern</em> and the guard descends on the scrutinee. Patterns are an ordinary Agda datatype, external to the theory, exactly as <code>Ty</code> is &mdash; the theory presents the things being analysed, not the things analysing them.</p>

<p>The theory is values: booleans and pairs. Two of its three operations are <strong>nullary</strong>, and that is why this client is here.</p>

<div class="note warn"><span class="k">A nullary operation has no slot</span>
<p><code>Ans-node</code> refutes a node by refuting one of its slots. <code>vtrueOp</code> has none &mdash; so <code>Match pfalse vtrue</code>, which is plainly empty, cannot be refuted through the node rule at all. The refutation has to travel somewhere else, and the somewhere else is <code>Ans-map&amp;</code>&rsquo;s hypothesis: &ldquo;this value is a node of <code>o</code>&rdquo; is precisely the knowledge that makes the grammar empty <em>here and nowhere else</em>. That is <code>clashAt</code>. A signature all of whose operations have arity ≥ 1 never notices the gap; two clients found it independently.</p></div>

<p><code>V = ⊥</code> here, so the free model is the <em>initial</em> algebra and every scrutinee is closed. The annotated instance has <code>V = ℕ</code> because a term may be a variable; a scrutinee may not, and a judgment descending on an open term would have to say what to do at a generator.</p>

HTML
code Theory/Instances/Match/Base.agda

cat <<'HTML'
<h3 id="mguard">Guard</h3>

<p>Shorter than the annotated one, because <code>VOp</code> is <em>finite</em>: no external annotation on an operation, so the node cover has three cells and a branch may be written by listing them. That finiteness is also what makes <a href="#mexh">exhaustiveness</a> a statement one can write down.</p>

HTML
code Theory/Instances/Match/Guard.agda

cat <<'HTML'
<h3 id="mjudg">The judgment, and two rules that are not nodes</h3>

<p><code>pwild</code> and <code>pvar n</code> are not syntax-directed on the value at all: they hold at <em>every</em> head. A rule with no premises and no restriction on the scrutinee is not a node &mdash; it is a decision &mdash; so those two indices go through <code>side</code> and never reach <code>look</code>. Pretending otherwise means writing the same trivial node three times, once per cell of the cover.</p>

<p>Matching a <em>single</em> pattern is a proposition. The proof-relevance is one level up: a clause list is the pointwise <em>sum</em> of its patterns, which is <code>⊕</code> and nothing more, so <code>matchAny</code> is a fold with <code>&lt;|&gt;</code>. That is where the three answers genuinely disagree rather than merely differing in packaging.</p>

<table>
<tr><th>Answer</th><th>Reads a clause list as</th><th>So it computes</th></tr>
<tr><td><code>Dec</code></td><td>a decision</td><td>does <em>anything</em> match?</td></tr>
<tr><td><code>Maybe</code></td><td>a left-biased choice</td><td>first-match semantics &mdash; what every real language does</td></tr>
<tr><td><code>ND</code></td><td>an enumeration</td><td>a <em>count</em> of the clauses that fired</td></tr>
</table>

HTML
code Theory/Instances/Match/Judgment.agda

cat <<'HTML'
<h3 id="mbind">The readout: substitutions</h3>

<p>The honest statement first, because it is narrower than <a href="#aelab">elaboration</a>&rsquo;s. <code>Match p</code> is a proposition, so a single pattern&rsquo;s derivation carries nothing the index and the scrutinee do not already have: <code>bind</code> reads <code>n</code> off <code>pvar n</code> and <code>v</code> off the model, and the derivation only certifies that it may.</p>

<p>The content is in <code>anyAction</code>, which tags each summand of the clause list with its <em>position</em>. That sum is the only proof-relevant thing in the development, and it is exactly what the three front ends disagree about &mdash; <code>decideMatch</code>, <code>firstMatch</code> and <code>allMatches</code> are one grammar and one action at three answers.</p>

HTML
code Theory/Instances/Match/Bindings.agda

cat <<'HTML'
<h3 id="mexh">The identification: exhaustiveness <em>is</em> a cover</h3>

<p>This is the payoff of the client, and it is a two-line observation with a lot behind it. <code>Cover Y Λ</code> has two fields. A clause list has two properties.</p>

<table>
<tr><th><code>Cover</code> field</th><th>Clause list</th></tr>
<tr><td><code>total</code></td><td>every value matches some clause &mdash; <strong>exhaustiveness</strong></td></tr>
<tr><td><code>disjoint</code></td><td>no value matches two &mdash; <strong>irredundancy</strong></td></tr>
</table>

<p>So &ldquo;this clause list is exhaustive and irredundant&rdquo; is not a pair of ad hoc lemmas; it is <code>Cover (Fin n) (λ i → Match (clause i))</code>, the same record <code>look</code> consumes. And the concrete cover is the <em>node cover relabelled</em>: <code>full</code> has one clause per head constructor, so <code>disjoint</code> is no-confusion for <code>Val</code> transported along an injection <code>Fin 3 ↪ VOp</code>, and nothing about patterns is used. A complete irredundant clause list at depth one <em>is</em> a cover by head; deeper ones are covers of covers.</p>

<p><code>tally full v ≡ 1</code> is the computational shadow, one value at a time. <code>tally shared both ≡ 2</code> is a redundant clause list exhibited as a number, and <code>tally partial ff' ≡ 0</code> is a counterexample to exhaustiveness. Only <code>ND</code> can say either.</p>

<div class="note"><span class="k">What is not proved</span>
<p>Nothing general. This is one list. There is no theorem &ldquo;<code>Cover</code> implies <code>tally ≡ 1</code>&rdquo; &mdash; that would have to relate the <code>ND</code> enumeration to the cover&rsquo;s index type, and the enumeration is a list with an order while the cover is not.</p></div>

HTML
code Theory/Instances/Match/Exhaustive.agda

cat <<'HTML'
<h3 id="mtests">Running it</h3>

<p>Every test is <code>refl</code>. The three-answer rows are the ones to read: <code>shared</code> is a redundant list and <code>partial</code> a non-exhaustive one, and each answer has a different opinion about them &mdash; which is the point of leaving the answer abstract.</p>

HTML
code Theory/Instances/Match/Tests.agda

cat <<'HTML'
<h2 id="ybase">Client 5 &mdash; the offside rule</h2>

<p>Layout is the standard counterexample to &ldquo;syntax is context-free&rdquo;. Whether a token opens a block, closes three of them, or does nothing depends on a column and on a stack of columns, and no context-free grammar has either. The claim tested here is narrower and it survives: <strong>layout is not context-free, but it <em>is</em> syntax-directed in this framework&rsquo;s sense</strong>, because the state after a token is a function of the state before it and of the token&rsquo;s own column.</p>

<p>A lexer&rsquo;s output is a list, and a list over <code>Tok</code> is the free algebra for the signature <code>{nilOp, consOp t}</code>. Putting the token in the <em>operation</em> is the same trick <code>appOp B</code> plays, and it buys the same three things: a node cover by head, so prediction is LL(1); an infinite <code>LOp</code>, which a <code>Cover</code> does not care about; and precision everywhere, because a free term algebra has it.</p>

<div class="note"><span class="k">Why not the free monoid</span>
<p>The data <em>is</em> a string, and the string framework would accept it. It is still the wrong model. Layout is not associative in any useful sense &mdash; the state after a prefix is not a monoid element &mdash; and the rule needs to look at <em>the next token</em>, which the monoid presentation reaches only through a lookahead cover. Cons cells give it for free.</p></div>

HTML
code Theory/Instances/Layout/Base.agda

cat <<'HTML'
<h3 id="yguard">Guard: the degenerate case, named</h3>

<p><code>consOp t</code> has one argument, so the &ldquo;subterm order&rdquo; is the proper <em>suffix</em> order and the measure is the length. That is precisely the order the string framework builds by hand out of <code>Suffix</code>; here it falls out of <code>ilexOrder</code> applied to the term size, because a token stream&rsquo;s only subterm is its tail.</p>

HTML
code Theory/Instances/Layout/Guard.agda

cat <<'HTML'
<h3 id="yoffside">The judgment, and the condition with nowhere to sit</h3>

<p>The family is indexed by the layout state &mdash; a mode and a stack of open block columns &mdash; and the guard descends on the token list. For a one-argument operation <code>⊗ᴰ</code> degenerates to exactly a state machine&rsquo;s transition function, which is the honest shape of the thing.</p>

<p><code>nilOp</code> has arity <em>zero</em>, so the &ldquo;end of input&rdquo; rule has no slot to hang its condition on &mdash; and it needs one, because end of input is <em>accepted</em> in <code>scanning</code> (close every open block) and <em>rejected</em> in <code>opening</code> (a block opener with no block). This is <a href="#mbase">the nullary gap</a> from the other side: not a refutation with nowhere to travel, but a condition with nowhere to sit. <code>Ans-&amp;&amp;</code> attaches it to the node:</p>

<pre><code>Cell o S = ⊗ᴰSet o (Slots o S) &amp;Set SideSet o S</code></pre>

<p>Stating <em>every</em> operation&rsquo;s condition that way &mdash; rather than only <code>nilOp</code>&rsquo;s &mdash; keeps <code>Slots</code> a pure recursive call and puts all the arithmetic in one place. This client is where the house convention comes from, and <a href="#alin">linear typing</a> now follows it.</p>

<h4>Two functions of the same fact, and why there are two</h4>
<p><code>popTo</code> computes the surviving stack: a <em>function</em> of the index and the token, which is what makes the tail&rsquo;s index computable and the judgment syntax-directed. It is not read off the derivation, and it could not be &mdash; <code>⊗ᴰ</code>&rsquo;s slot indices may mention sibling slots&rsquo; <em>model values</em>, never their proofs. <code>Close</code> is the proof-relevant counterpart: a chain of &ldquo;this block closes&rdquo; steps ending in a trichotomy at the first block that survives. The two never meet in the checker, and <code>survivors≡popTo</code> is the one coherence fact worth stating &mdash; if they disagreed, the renderer&rsquo;s braces would not match the checker&rsquo;s state.</p>

<div class="note warn"><span class="k">What is not implemented, and this is the honest one</span>
<p>No <code>parse-error(t)</code> rule. Haskell closes an implicit block when the enclosing parser would otherwise fail, which makes layout depend on the parser it feeds &mdash; a mutual recursion this framework has no reason to want. The omission is <em>visible</em>: a one-line <code>let x = 1 in x</code> is accepted, but its <code>in</code> is indented past the block, so the closing brace lands at end of input rather than before the <code>in</code>, and the rendered stream is one a parser would reject. <code>OffsideTests</code>&rsquo; <code>oneLine</code> records exactly that. Also absent: line tracking, empty blocks, and explicit braces in the input.</p></div>

HTML
code Theory/Instances/Layout/Offside.agda

cat <<'HTML'
<h3 id="yrender">Rendering: the derivation <em>is</em> the punctuation</h3>

<p>Layout is a tree-to-tree pass, so the interesting object is not the decision but the output &mdash; and the output is already sitting in the derivation. <code>Close</code>&rsquo;s &ldquo;this block closes&rdquo; steps are the <code>}</code>s, and its terminal case is the <code>;</code> or its absence, so <code>closeOut</code> reads them off exactly as <code>deBruijn</code> reads an index off a <code>Lookup</code>. Nothing recomputes <code>popTo</code>; nothing compares two columns twice.</p>

<p>Note the division of labour, which is what the framework is for. The mode-and-stack state is <em>not</em> carried in the derivation &mdash; it is the <em>index</em>, so it is available for free at every recursive call. The derivation carries only what the index cannot compute.</p>

HTML
code Theory/Instances/Layout/Render.agda

cat <<'HTML'
<h3 id="ytests">Running it three ways</h3>

<p><code>ND</code> counts one derivation for every accepted stream and zero for every rejected one, and that is the expected answer rather than a lucky one: the judgment is a proposition by construction, because each token&rsquo;s rule is selected by the head constructor and each premise&rsquo;s index is a function of the state and the token. <strong>Layout is deterministic, and here that is a typing fact rather than a theorem about the algorithm.</strong></p>

HTML
code Theory/Instances/Layout/OffsideTests.agda

cat <<'HTML'
<h2 id="cbase">Client 6 &mdash; instance resolution, and what <code>disjoint</code> means</h2>

<p>Every other client puts terms in the model and types in the index. This one is the other way round. <code>Resolve C τ</code> asks whether class <code>C</code> has an instance at type <code>τ</code>, and it is <code>τ</code> that the rules take apart &mdash; there is no term at all. So the model is the type language, <code>X</code> is the set of class names, and the guard descends on the subterm order of <em>types</em>.</p>

<p><code>V = ⊥</code> again, and here the reason is sharp: a type variable in the model would make <code>Resolve</code> a judgment about <em>open</em> types, which is exactly where instance resolution stops being decidable.</p>

<p>One more restriction is doing work. An instance head is a <em>constructor</em>, not a pattern: the table records <code>head = lstOp</code>, never <code>instance Eq (List ι)</code>. That is what makes resolution syntax-directed at all, it is what Haskell&rsquo;s instance heads obey up to arity, and a two-level head is precisely the shape that makes overlap possible.</p>

HTML
code Theory/Instances/Class/Base.agda

cat <<'HTML'
<h3 id="cresolve">The identification: <code>disjoint</code> is coherence</h3>

<p>The node, the guard and the slots are the ordinary story &mdash; <code>Eq a =&gt; Eq (List a)</code> fires at <code>List a</code> and its one premise sits at <code>a</code>, a proper subtype. What is <em>not</em> determined is <strong>which instance</strong>. The judgment is an indexed sum:</p>

<pre><code>Resolve C τ  =  ⊕[ i ∈ Inst C ] (instance i applies at τ)</code></pre>

<p>and answering an indexed sum is what <code>AnswerFunctor</code> could not do before <code>Ans-route</code>. A checker cannot consult all of <code>Y</code>: it need not be finite, and even when it is, asking every alternative is not what a resolver does. A <code>Route</code> supplies a cover of the type language by <code>Maybe (Inst C)</code> &mdash; the cell of <code>just i</code> is &ldquo;<code>τ</code>&rsquo;s head is instance <code>i</code>&rsquo;s head&rdquo;, the cell of <code>nothing</code> is &ldquo;no instance&rsquo;s head matches&rdquo; &mdash; and then:</p>

<table>
<tr><th><code>Route</code> field</th><th>Instance resolution</th></tr>
<tr><td><code>cov .total</code></td><td>resolution <em>terminates</em>: some instance&rsquo;s head matches, or provably none does. The finite search over the table, and where a <em>decidable</em> table is used.</td></tr>
<tr><td><code>cov .disjoint</code></td><td><strong>COHERENCE</strong>: no two distinct instances of a class match the same type.</td></tr>
<tr><td><code>into</code></td><td>an instance that applies does match its own head.</td></tr>
</table>

<div class="note"><span class="k">This is not an analogy</span>
<p>Spelled out, <code>disjoint (just i) (just j)</code> for <code>i ≠ j</code> asks for <code>NodeAt (head i) &amp; NodeAt (head j) ⊢ ⊥Ty</code>, and the only way to get it is to know the heads differ. That is <code>Coherent T</code>, verbatim &mdash; the exact hypothesis <code>Routed.route</code> needs, and the exact thing GHC&rsquo;s coherence check verifies.</p></div>

<h4>The other half, which is the better half</h4>

<p>An <em>incoherent</em> table has no <code>Route</code>, so it has no routed resolver &mdash; <strong>statically</strong>, at the type level, not as a failure at run time. What it does have is <code>Ans-anyFin</code>: ask every instance, keep every answer. That needs <code>Ans-empty</code>, so it is available at <code>Maybe</code> and <code>ND</code> and never at <code>Dec</code>.</p>

<p>So the two <code>Pick</code>s are the whole design tension in two lines: <code>routed</code> demands coherence and commits, <code>ambig</code> demands nothing and counts. <code>ResolveTests</code> declares <code>Eq a =&gt; Eq (List a)</code> <em>twice</em> &mdash; the smallest possible incoherence, and a real one, since that is what importing the same instance from two modules looks like. Then <code>incoherent</code> refutes <code>Coherent T₁</code>, so <code>Routed.routed</code> cannot be applied and that table has no decision procedure here at all; while at <code>ND</code>, <code>count₁ eqC (lst ι) ≡ 2</code> &mdash; the incoherence, exhibited as a number. At <code>Maybe</code> the same table returns one derivation and says nothing about the other, which is precisely the silent instance selection a PEG-shaped resolver performs.</p>

<h4>And the dictionary</h4>
<p>A derivation of <code>Resolve C τ</code> is a tree of instance choices &mdash; which is to say it <em>is</em> the dictionary a compiler passes at run time. <code>toDict</code> folds it, <code>dictAction</code> makes that a <code>SemanticAction</code>, and <code>resolve</code> is <code>observe checker (semact-dec dictAction)</code>: the same three-term composition as <a href="#aelab">elaboration</a>, one more time.</p>

HTML
code Theory/Instances/Class/Resolve.agda

cat <<'HTML'
<h3 id="ctests">Running it</h3>

HTML
code Theory/Instances/Class/ResolveTests.agda

cat <<'HTML'
<h2 id="conventions">House conventions, and where they came from</h2>

<p>Six clients, written by different hands at different times, and they drifted. What follows is what they converged on. It is kept in the tree as <code>Theory/Combinator/README.agda</code> &mdash; a module with no definitions, deliberately, because a convention that could be enforced by a type would <em>be</em> a type.</p>

<table>
<tr><th>#</th><th>Convention</th><th>Because</th></tr>
<tr><td>1</td><td>Define the judgment by recursion on the model, not as an indexed <code>data</code>.</td><td>An indexed family gets <code>UnificationStuck</code> in every branch of the checker, and the recursive form makes <code>isProp</code> a two-line induction rather than a theorem.</td></tr>
<tr><td>2</td><td>Dispatch with <code>look nodeCover</code>, never with a match on the model element.</td><td>Everything else hangs off this. Matching on the term forces a <em>pointwise</em> relabelling, and going through the cover hands you <code>NodeAt o</code> as the hypothesis <code>Ans-map&amp;</code> wants.</td></tr>
<tr><td>3</td><td><code>Slots o i</code> is a list of premises and nothing else.</td><td>If reading it does not read like the rule&rsquo;s premises, something is in the wrong place.</td></tr>
<tr><td>4</td><td>Side conditions go at the <em>node</em>: <code>Cell o i = ⊗ᴰSet o (Slots o i) &amp;Set SideSet i</code>.</td><td><a href="#yoffside">Layout</a> is forced into it by a nullary operation; <a href="#alin">Linear</a> is merely honest for it. A condition on a <em>name</em> argument is not a side condition &mdash; it is a slot, and stays one.</td></tr>
<tr><td>5</td><td>Every side condition comes with a <code>Decidable</code> and enters via <code>Ans-ofDec</code>.</td><td>The only door by which an answer learns something it did not compute. Keeping it single is what lets one source text run at three answers.</td></tr>
<tr><td>6</td><td><code>rollNode</code> and <code>unrollNode</code> are <code>⊢</code>-terms; <code>unroll</code> takes <code>&amp; NodeAt o</code>.</td><td>A grammar and its unfolding agree only where the head is known.</td></tr>
<tr><td>7</td><td>Premises carry their evidence: <code>InCtx</code>, <code>Lookup</code>, <code>Close</code>, not booleans.</td><td>A boolean says the name is bound; a chain of &ldquo;not here&rdquo; steps says <em>where</em>. All three are still propositions, so proof-relevance and unambiguity are not in tension.</td></tr>
<tr><td>8</td><td>Readouts are <code>SemanticAction</code> + <code>observe</code>.</td><td><code>compile = observe checker (semact-dec action)</code>, in five clients, letter for letter. Do not write a boundary by hand.</td></tr>
<tr><td>9</td><td>Tests are <code>refl</code>.</td><td>A test that needs a proof is a test that did not reduce, and a checker that does not reduce is a checker nobody can run.</td></tr>
</table>

<p>And a negative one: <strong>nothing in a judgment module mentions <code>Dec</code>, <code>Maybe</code> or <code>ND</code></strong>. If it does, the client has picked an answer, and the point of the framework was not to.</p>

<div class="note"><span class="k">Two documented exceptions, both in <code>Match</code>, both arguments rather than lapses</span>
<p><code>pwild</code> and <code>pvar n</code> do not go through <code>look</code>, because a rule that holds at every head is a decision and not a node. And <code>observeAll</code> is a hand-rolled boundary, because <code>observe</code> reads <em>one</em> value out of a <code>⊤Ty</code>-map while <code>ND</code> is a list &mdash; supplying the missing combinator means changing the backend interface, which is worth doing deliberately rather than in passing.</p></div>

HTML
code Theory/Combinator/README.agda

cat <<'HTML'
<h2 id="internal">Reflection: is this internal to the DSL?</h2>

<p>A fair question to ask of any embedded language: is the code written <em>in</em> the language, or does it keep dropping into the host? The first version of this port dropped out in three places. All three were the same leak.</p>

<table>
<tr><th></th><th>Before</th><th>Now</th></tr>
<tr><td>Case analysis</td><td><code>step</code> matched on the term</td><td><code>look</code> over a <code>Cover</code></td></tr>
<tr><td>Relabelling</td><td><code>Ans-mapAt</code>, pointwise</td><td><code>Ans-map&amp;</code>, a <code>⊢</code>-term</td></tr>
<tr><td>Side conditions</td><td><code>Ans-dec</code>, a raw sum</td><td><code>Ans-ofDec : DecSet A ⊢ Ans A</code></td></tr>
</table>

<p>They were connected: matching on the term is what made a pointwise relabelling necessary, and a pointwise relabelling is what let a term unroll to <em>one</em> node instead of a sum over head constructors &mdash; which is how the obligation discussed below got dodged rather than paid.</p>

<p>Fixing the first fixed the rest. Once the head comes from a cover cell, that cell is available as a hypothesis, and the backward map becomes writable. Deleting the metalevel head machinery removed about 60 lines.</p>

<h4>What is deliberately still in the host language</h4>
<p><code>Scope</code> and <code>Der</code> are defined by recursion on the term rather than as <code>μ</code> of a functor code. That is a choice, not an omission &mdash; see the next section. And the <em>justifications</em> &mdash; precision proofs, size measures, the classifier &mdash; live outside, exactly as their counterparts do in the string framework. Those are properties of the theory, not programs in the language.</p>

<h2 id="trade">A real design choice: dependent slots vs. summed indices</h2>

<p>Binders can be expressed two ways, and the difference is instructive.</p>

<h4>Option A &mdash; the dependency (what this code does)</h4>
<pre><code>Slots lamOp Γ ms (suc zero) = ScopeSet (ms zero ∷ Γ)</code></pre>
<p>&ldquo;This slot&rsquo;s index is <em>determined</em> by that slot&rsquo;s value.&rdquo; Needs <code>⊗ᴰ</code>. Nothing is searched.</p>

<h4>Option B &mdash; sum over the binder, pin it with a representable</h4>
<pre><code>⊕e Name λ n → ⊗e lamOp (two (k ⌈ n ⌉) (Var (n ∷ Γ)))</code></pre>
<p>&ldquo;It is <em>one of</em> infinitely many, and here is a constraint saying which.&rdquo; This works with the codes the library already has, so the grammar becomes a genuine <code>μ</code> &mdash; first-class data, with <code>roll</code>/<code>unroll</code> and a recursor for free.</p>

<div class="note"><span class="k">The trade</span>
<p>Option B is more uniform and reifies the grammar. But it converts a <em>determined</em> index into a <em>searched</em> one, so the answer then owes a routing argument for the binder name &mdash; and for the type annotation, in the typing client. Option A says instead that the index is determined, which is true, and costs nothing.</p>
<p>Given both judgments here are propositions (no parse trees to extract, so the recursor is not needed), Option A wins on this evidence. If you wanted the grammars reified, Option B is a contained change and needs no new machinery.</p></div>

<h2 id="boundary">Where it stops</h2>

<p>The annotation on application is not laziness. Remove it and the rule reads</p>

<pre><code>Γ ⊢ f a ⇐ A   iff   ∃B. Γ ⊢ f ⇐ B ⇒ A  and  Γ ⊢ a ⇐ B</code></pre>

<p>an existential over an infinite index. Deciding that is exactly what the library&rsquo;s <code>Route</code> is for &mdash; a cover of the alternatives, where</p>

<table>
<tr><th><code>Route</code> field</th><th>Bidirectional typing</th></tr>
<tr><td><code>B : Maybe Y → grammar</code></td><td><code>Maybe Ty</code> — <code>nothing</code> is &ldquo;does not synthesise&rdquo;</td></tr>
<tr><td><code>cov .total</code></td><td>every term synthesises a type, or provably none</td></tr>
<tr><td><code>cov .disjoint</code></td><td><strong>uniqueness of synthesis</strong></td></tr>
<tr><td><code>into</code></td><td>each rule lands in the class its conclusion claims</td></tr>
</table>

<p>So &ldquo;the grammar is LL(1)&rdquo; and &ldquo;the calculus is bidirectionally typeable&rdquo; are the same condition, discharged by the same record. The annotation buys precisely that discipline; without it, a checker owes uniqueness-of-synthesis as a side theorem, and the combinators will not supply it.</p>

<p>That paragraph used to end the document. It no longer does: <code>Ans-route</code> exists, and <a href="#cresolve">instance resolution</a> is a client that pays the obligation rather than dodging it &mdash; with the same record, and with <code>disjoint</code> reading as <em>coherence</em> rather than as uniqueness of synthesis. The boundary has moved; it has not disappeared. A judgment whose alternatives are not known exclusive still has no decision procedure here, and cannot.</p>

<h4>Other limits, stated plainly</h4>
<table>
<tr><th>Limit</th><th>Why</th></tr>
<tr><td>No left recursion</td><td>The guard is on the term. A rule that recurses without descending is a type error &mdash; the right failure, but a failure.</td></tr>
<tr><td>Alternation does not short-circuit at <code>Dec</code></td><td>Building a refutation of <code>A ⊕ B</code> needs refutations of both.</td></tr>
<tr><td><code>ND</code>&rsquo;s completeness is not typed</td><td>A list of derivations, with no proof it is exhaustive.</td></tr>
<tr><td>Quotiented theories lose the cover</td><td>For bags, &ldquo;contains <code>c</code>&rdquo; is total but <em>not</em> disjoint &mdash; <code>{a,b}</code> is in two classes at once. The node cover, and with it prediction, needs a chosen head.</td></tr>
</table>

<h2 id="build">Building it</h2>

<p>Everything above typechecks under Agda 2.9.0 with <code>cubical</code> and <code>cubical-categorical-logic</code>. The tests are <code>refl</code>, so <em>typechecking the test files runs them</em>.</p>

<pre><code>cd src
agda Theory/Instances/Lambda/ScopeTests.agda
agda Theory/Instances/Lambda/Nameless.agda
agda Theory/Instances/Annotated/TypingTests.agda
agda Theory/Instances/Annotated/Elaborate.agda
agda Theory/Instances/Annotated/LinearTests.agda
agda Theory/Instances/Match/Tests.agda
agda Theory/Instances/Match/Exhaustive.agda
agda Theory/Instances/Layout/OffsideTests.agda
agda Theory/Instances/Class/ResolveTests.agda</code></pre>

<p>This page is generated from the sources by <code>docs/build.sh</code>, so the code shown is always the code that compiles. Re-run it after any change.</p>

</main></div></body></html>
HTML
