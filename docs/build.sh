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
<a href="#alin">Annotated/Linear</a>
<a href="#atests">TypingTests</a>
<b>Reflection</b>
<a href="#internal">Is it internal?</a>
<a href="#trade">⊗ᴰ vs. summed indices</a>
<a href="#boundary">Where it stops</a>
<a href="#build">Building it</a>
</nav>
<main>

<h1>Combinators for an arbitrary theory</h1>
<p class="sub">A port of the parser-combinator framework off the free monoid, with a scope checker and a type checker written once and run at three different notions of &ldquo;answer&rdquo;.</p>

<h2 id="what">What this is</h2>

<p class="lede">The existing framework in this repository parses <em>strings</em>. This is that framework with the strings taken out, plus two clients that are not parsers at all.</p>

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

<p>Five fields. This is the entire interface a new backend must implement.</p>

<table>
<tr><th>Field</th><th>In words</th></tr>
<tr><td><code>Ans</code></td><td>What an answer about a grammar <em>is</em>.</td></tr>
<tr><td><code>Ans-map&amp;</code></td><td>Relabel an answer along a renaming of grammars &mdash; given a hypothesis both directions may use.</td></tr>
<tr><td><code>Ans-⊕&amp;</code></td><td>An answer about <code>A</code> and one about <code>B</code> combine into one about <code>A</code>&nbsp;or&nbsp;<code>B</code>. <em>This single field is the entire difference between the three backends.</em></td></tr>
<tr><td><code>Ans-ofDec</code></td><td>Any decision is an answer. How side conditions get in.</td></tr>
<tr><td><code>Ans-node</code></td><td>Answers at the arguments give an answer at the node.</td></tr>
</table>

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
agda Theory/Instances/Annotated/TypingTests.agda</code></pre>

<p>This page is generated from the sources by <code>docs/build.sh</code>, so the code shown is always the code that compiles. Re-run it after any change.</p>

</main></div></body></html>
HTML
