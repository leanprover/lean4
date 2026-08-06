# Documentation Style Guide

This is a style guide for Lean documentation. Please use it for all
documentation that’s officially provided by the project, where
authorship and responsibility are attributed to the project as a
whole. Existing documentation should be brought progressively more in
line with this style, rather than less, as it’s edited, but changes to
code that require documentation changes for correctness do not
necessarily require style updates at the same time. Maintaining
internal consistency in a page or document is more important than
updating one subsection of it to match these guidelines.

Individuals writing texts where they are named as the author do not
need to follow all of these guidelines. It’s good to maintain internal
consistency, but a book or blog post with a named author may use a
different standard (e.g. British, Indian, or Canadian English) or
adopt a register that is more or less formal than that which we use
for reference materials or official tutorials.

This guide is based on advice provided in the Chicago Manual of Style,
18th Edition, the [MDN style guide](https://developer.mozilla.org/en-US/docs/MDN/Writing_guidelines/Writing_style_guide),
the [Rust API documentation style guide](https://github.com/rust-lang/rfcs/blob/master/text/1574-more-api-documentation-conventions.md#appendix-a-full-conventions-text),
and to a lesser extent the [Google](https://developers.google.com/style)
and [Microsoft](https://learn.microsoft.com/en-us/style-guide/welcome/)
style guides. If something isn’t mentioned here, use these resources in
that order for guidance (and consider updating this document).

The most important principles are:

* Be clear and consistent. Remove ambiguity when possible, use the
  same technical terms for the same concepts everywhere, and work
  towards a consistent register within any given class of documents.
* Write according to the context in which the information will be
  consumed. Text intended for quick reference in hover popups in text
  editors should be written differently than text intended to be
  consulted in a larger browser window, though the former can be
  effectively used as part of the latter.
* Be accessible to our most important target audiences. In order, this
  is: software developers and mathematicians who are learning Lean but
  have not used related tools before, current Lean users with
  backgrounds in mathematics or programming, and experts with
  backgrounds in related tools who are learning Lean.


## General Rules

These overall principles apply to all Lean documentation, including
docstrings, the reference manual, the developer’s guide, and
examples. Their purpose is to give a common and consistent “voice” to
the documentation, to help writers with varied linguistic, academic,
and cultural backgrounds work together productively, and to help make
sure we take our whole intended audience into account.

Many of these guidelines are essentially arbitrary. There’s no
fundamental reason to choose US English over another written standard,
nor to choose the *Chicago Manual of Style* as a default arbiter of
disputes. Like a standardized coding style, it’s more important to
*have* a broadly acceptable standard than to customize the one that
fits any particular taste, and spending time debating which
punctuation or spelling standard to adopt takes time away from
actually writing documentation.

Other guidelines come from our practical experiences in a diverse
community. Even though we use US English, we should avoid Americanisms
that are not widely understood internationally. By identifying and
avoiding specific language usage that is popular among research
mathematicians or software developers, but not common to both, we can
write texts that are useful to as many readers as possible.


### Readers First

If adherence to one of the rules described here would make the text
more difficult to understand, and there’s no clear way to rewrite the
text to be both consistent and comprehensible, then the rule should be
broken. If you are writing with a tool that supports it, leave a
comment that documents this decision.


### Audience

All texts should be written for a particular audience. For most Lean
documentation, this audience consists of mathematicians, working
software developers, computer scientists, and students learning these
fields. The audience consists of readers with many first languages and
cultural backgrounds. Texts should be as accessible as possible to
these readers, and generally not assume that they’ve completed a
standard undergraduate mathematics or computer science curriculum,
though it’s acceptable to assume knowledge that is common to both but
not shared by the general public. As an exception to this principle,
it’s usually also acceptable to assume familiarity with functional
programming concepts such as monads.

It is not always feasible to make all text accessible to all
readers. If part of the documentation is specific to programming
applications, or is necessary for experts in a particular sub-field,
try to place it in an independent section. This allows the readers who
can benefit from it to do so, while others can more easily skip it.

It’s acceptable to write documentation that assumes a different
audience. For example, tutorials may assume even less background
knowledge of logic and mathematics, while documentation that describes
how to build custom proof automation can assume more knowledge of
functional programming and Lean’s type theory. When a document has a
non-default audience, please document this explicitly.


### US English, Chicago Style

There are multiple codified written standards for English. We use US
English spelling and grammar, and unless otherwise specified, we
follow the *Chicago Manual of Style*, 18th Edition, Part II. We use
*Chicago* to resolve conflicts or disagreements about style, but
there’s no need to memorize it. Specific points to be aware of, or
explicitly-chosen deviations from it, will be summarized in this
document as necessary.

There’s no need to precisely adhere to *Chicago* for citations of
academic publications. Please choose any format that readers will
understand and that appropriately credits the work. In formats that
use inline citations, prefer author-year styles over numbered styles.


### Conservative Usage

Outside of technical terminology, avoid words that are not well
established. When the meaning of a word has changed recently or is in
the process of changing (such as “literally”), or when it has
different meanings to different language communities, choose a
different word.

If new terminology is needed, choose established terminology from
mathematics, computer science, and other formal reasoning tools. Don’t
adopt existing terminology with a slightly different meaning.

Avoid figures of speech that may not be understood globally, like
quotes from literature, even if they make a point very well. Many
members of our audience do not have English as a first language and
are not familiar with US or European culture.

Some fake grammar rules may be ignored. To boldly split infinitives is
perfectly acceptable in English. And it’s OK to start a sentence with
a conjunction if that has the right impact. But do consider alternate
formulations that won’t annoy some readers.


### Picky Usage

There are certain distinctions that should be maintained in the text,
but that we should not expect readers to know. Use the correct term in
the correct context, but never contrast the two; the text should make
sense if both were replaced by the same term. An important part of our
audience will be bothered if we get these wrong, and another part has
no idea that the distinction even exists.

* *Parameters* are variables bound in a declaration, while *arguments*
  are the values actually provided at a use site. In a recursive
  function definition, the parameters are listed in the signature,
  while recursive call sites may use some of those parameters as
  arguments.
* The *codomain* of a function is its return type, while the *range*
  is the set of values in that type that the function actually
  returns. Use *image* when talking about those values returned for
  some subset of the domain.
* *Functions* are actually functions - not all constants in Lean are
  functions. Call them “defined constants” if they’re not necessarily
  functions.


### Quotation and Punctuation

US English requires that commas and periods be inside quotation
marks. Follow this rule unless it might lead to confusion, in which
case the punctuation may be moved outside the quotation marks. This is
particularly relevant when quoting code.


### Passive Voice

Prefer the active voice, but don’t jump through hoops to avoid the
passive voice. Be consistent in a given passage.


### Avoid Overly Academic Writing

Write in a style that’s also accessible to those without academic
training. Consider whether there’s a way to say what you want to say
that uses a more widely-accessible register of English.

Avoid unnecessary Latin, but use it when there’s not a good non-Latin
alternative. It’s fine to use Latin loanwords that are established in
English (like “establish”) - these are not Latin words anymore. Avoid
phrases such as *ceteris paribus*, *viz.*, *ergo*, and *desideratum*,
as well as Latin abbreviations that are not common in both US and
international English. In particular, *N.B.* and *cf.* are only widely
used and understood in some regions and should be avoided. Generally,
*N.B.* should just be deleted, with facts stated directly, and *cf.*
should be replaced with a phrase like “see …” or “this is similar to
….”

The following Latin phrases and abbreviations are acceptable and
should not be italicized:

* ad hoc
* per se
* etc (but not “et cetera” or “&c”)
* vice versa

Domain-specific terms such as *modus ponens*, *modus tollens*, and *ex
falso quodlibet* are also acceptable, but prefer “excluded middle”
over “tertium non datur.” The abbreviations “i.e.” and “e.g.” should
be used only at the start of a parenthetical aside (i.e. like this),
and “et al.” only in the author list in a citation of an academic
work.

Avoid “iff”: write “if and only if” or “is logically equivalent to”
instead. Readers who do not know the abbreviation may assume it is a
typo. Don’t use “just in case” to mean “if and only if”.

Avoid non-standard grammatical constructions and turns of phrase that
primarily exist in research papers, such as “allows to” (without a
direct object that says who is allowed to do something). Instead of
“This system allows to generate faster code”, write something like
“This system makes it possible to generate faster code.” It’s even
better to be more specific in the causal relationship, like “The
compact intermediate representation consumes less cache, so the
resulting code runs faster.”


### Examples and Explanations

Documentation should both explain the rules that apply in a given
situation and provide concrete examples that illustrate the
rules. Examples are not a substitute for explanations, and readers
shouldn’t have to generalize themselves. At the same time,
explanations without examples can be very difficult to
understand. When writing, know which one you’re writing at any given
time.

Try to use meaningful examples when possible; it’s better to have a
list of strings as input than a list of metavariables. Toy examples
are fine, but they should hint at something actually useful. Avoid
allusions to classical literature, popular culture, politics, or
mathematical in-jokes in examples. It’s OK to have an answer be 42,
but don’t pair that with something about mice that readers who are not
familiar with Douglas Adams might be flummoxed by. If a classical
example would help a part of the audience, then use it, but insert a
brief explanation. Instead of “foo”, “bar”, and “baz”, use something
like color names or the days of the week.


### Readers Determine Difficulty

Don’t state to readers that something is easy—for many, it won’t
be. Don’t tell them that they already know something (but it’s good to
cross-reference a prior explanation).

In mathematical writing, it is common to signpost statements that
should be easy to indicate that readers should backtrack if this is
not the case. This convention can come across as patronizing or
insulting to readers who are not formally trained in math.


### Typographical Unicode

The advice in this section should be adapted as appropriate to the
tool being used to prepare the documentation.

Use typographical Unicode where appropriate. Quotations should use
left and right double or single quotes (e.g. “this” and ‘that’) rather
than ASCII vertical quotes or LaTeX-style backtick quotes, and double
quotes should be used for the outermost level. For example, it’s
correct to nest them like this: “‘Quotation’ can’t be spelled without
‘Q’.” Use em dashes to delimit parenthetical remarks, and don’t put
spaces around them—this sentence is itself an example of this
style. Use en dashes for numeric or date ranges. Don’t represent en or
em dashes with doubled or tripled hyphens. Use right single quotation
marks for apostrophes (here’s an example) rather than ASCII single
quotes.

Only use ellipses in contexts where symbolic formulae would make sense
(e.g. 1+2+…+n). Use a Unicode ellipsis for this purpose, rather than
three periods.


### Proper Theorem Names

Named theorems and axioms are proper names and are capitalized as
such. Write “Axiom of Choice”, “Fermat’s Last Theorem”, “Excluded
Middle”, and “Yoneda Lemma”. Numbered theorems are not names; write
“see theorem 5.3”.


### Trademarks, Software Names, and Human Names

Capitalize trademarks according to the owner’s wishes. If needed,
rewrite a sentence to avoid a lowercase trademark name (e.g. “iOS”) at
the beginning. Software systems should be capitalized as preferred by
the project (e.g. “JavaScript”, “Wasm”, “Lean”). Don’t write system names in
small caps. Prefer conventions chosen by the creator of an idea unless
there’s a good reason not to. If no guidance is provided, follow the
usual English conventions for proper names.

Capitalize human names according to the wishes of the human in
question. Adjectives derived from human names, such as “Abelian” and
“Boolean”, should also be capitalized.

As an exception to the rules for proper names, don’t capitalize “web”
when used in the sense of “World Wide Web,” except as part of that
particular phrase. Write “web content,” “web technologies,” or “on the
web” instead of “Web content,” “Web technologies,” or “on the Web.”


### Contractions

Established contractions such as “can’t” are permitted but not
mandatory. Be consistent with the surrounding text and think about the
general formality of the register in which it is written.


### Plurals

Use English plurals for loanwords, rather than those of the lending
language: “lemmas” instead of “lemmata”, “syllabuses” instead of
“syllabi”, and “emojis” instead of “emoji”.


### Inline Code

Treat identifiers and short snippets as if they were words. Do not
change their capitalization. If the first character of a code snippet
is not a capital letter, avoid using it at the start of a sentence; if
this can’t be reasonably avoided, do not capitalize it. It’s perfectly
fine to refer to functions or type constructors by name; there’s no
need to write `f x` or `List α` to refer to `f` or `List` independent of
any particular parameter.


### Code Blocks

Multi-line code samples should be in a suitable block-level
form. Depending on the format used to author the documentation, they
may be:

* “Displayed” as part of a paragraph (analogous to `displaymath` in
  LaTeX), in which case they should be treated as if they were a
  sentence. The preceding sentence should be a grammatically complete
  sentence, and it may end with a colon to indicate its relationship
  to the code block. In systems such as Markdown that don’t permit
  paragraphs to contain code blocks, “displayed” code should be
  typeset as its own block, with the preceding sentence indicating
  that the code is logically part of the paragraph.
* In a figure, numbered listing, or other similar environment, in
  which case they should be referred to from the text by a number or
  other indicator.
* Paragraph-level content in their own right, which is typically used
  for longer and more involved code examples.

A single sentence should not include a multi-line code example the way
that it may include a short snippet or identifier.


### Avoid Lean-Specific Confusion

When a common English term overlaps with a technical term for Lean,
don’t use it. Here are phrases to avoid, or at least carefully
consider:

* “for instance” (clashes with “instance of a type class”)
* “class” (in the usual sense of a collection)
* “list” (when not referring to a lean `List`)
* “derive” (when not referring to the `deriving` mechanism)

Also, try to avoid metaphorical use of mathematical concepts, because
it might be unclear that the mathematical concept is not *really*
being invoked. Don’t refer to things as sets or functions informally
unless it’s very important. It’s perfectly acceptable to use
mathematical concepts for their precise meanings; in “The priority of
an instance is a function of its declared priority and its declaration
order relative to other instances,” the term “function” expresses a
formal specification for the system, and is being used with its usual
mathematical meaning. Avoid using these terms humorously, imprecisely,
or superfluously, however. Examples to avoid include:

* “The set of all possible user interactions makes up Lean’s user
  interface.” Here, “set” does not contribute meaning and risks being
  a red herring.
* “Hash tables are functions from keys to values.” This is almost
  true, if extra details are added (it’s only a partial function, for
  instance, and it has additional observable structure such as bucket
  sizes). Without this precision, it’s unclear to readers when a
  precise specification is being provided.
* “It's a theorem that cats are better than dogs.” Here, “theorem” is
  used ironically to express that the speaker believes the statement,
  but it doesn’t express that there's an axiomatic pet system within
  which the statement has been derived.


### Carefully Quarantine Foundations and Metatheory

Unless it’s necessary to understand the practical functioning of Lean,
avoid discussion of foundational issues outside of specific materials
dedicated to this topic. For most users, it’s irrelevant. When
foundations are relevant to practice, it’s often for a reason that is
easier to understand. For example, decision procedures that use
excluded middle are less useful because excluded middle isn’t
computable, which is easier to understand than a discussion of
classical vs constructive logic. Users who care about foundations can
refer to specific sections. Don’t “apologize” for being insufficiently
constructive: either it has practical impact, in which case the
tradeoffs are what’s relevant, or it doesn’t, in which case it can be
ignored.


### Write From a Classical Perspective

Prefer to talk about a proposition as being true or false. Prefer the
conventions of mainstream mathematics, computer science, and analytic
philosophy over those of intuitionistic mathematics, type theory, and
programming languages. There’s nothing wrong with those fields, but we
want our text to have as broad an appeal as possible and they’re a
minority.


### Use Paragraphs Deliberately

Each paragraph should contain related sentences. When writing in a
format that makes it possible, think about the boundaries of logical
paragraphs and indicate them accordingly, even in the presence of
bulleted or numbered lists and “display-mode” mathematics or
code. This is possible in Verso using the `paragraph` directive and in
LaTeX by omitting a blank line, but it is impossible in Markdown.


### Pronouns

Generally speaking, use “I” or “we” to refer to the author, authors,
or provider of the documentation, if necessary. Explicitly mentioning
the party in question is often clearer (e.g. “the Lean FRO” or “the
Lean developers” rather than “we”).

In reference documentation, running examples are typically short
enough that the conversational “mathematical ‘we’” is not
well-suited. In tutorials or other documentation with longer-running
examples, the “mathematical ‘we’” can be used so long as it never
denotes the authors in the same document.

“We” should never refer to the Lean community as a whole in
documentation, nor the authors of the standard library. Don’t write
“We make the search efficient by globulating the hypotheses”; instead,
write “Globulating the hypotheses prior to the search makes it
efficient.” Prefer the passive voice to potentially ambiguous uses of
“we”. In many cases, the imperative mood is useful here - “We use X
for Y” can be “Use X for Y”.

Use “you” to refer to the reader, rather than abstractions like “the
reader”, but consider whether the fact being described is indeed one
in which the reader is a participant. “The user” is particularly prone
to misunderstanding, because it can be difficult to tell if the user
in question is the person using Lean to build a tool or the person
using the tool that was built in Lean.

The pronoun “they” can be used either to refer to a group of people or
to an individual of indeterminate or unknown gender. Prefer “they”
over “he or she” or “(s)he.” It’s often even better to rewrite the
sentence to remove the need for a pronoun, because the resulting
sentence is often more clear.


### Notes (Footnotes and Marginal Notes)

Notes that fall outside of the text flow, such as footnotes or
marginal notes, may be used for remarks that are important for some
readers but would distract from the flow of the text. Don’t put key
information in notes, and write the text on the assumption that
they’ll be skipped. Don’t overuse notes.

For web content, prefer marginal notes or collapsing notes over
footnotes that link to the bottom of the page. If the platform
supports notes, use them for complete citations of works, rather than
linking to a separate bibliography, so readers who are familiar with
the literature can tell at a glance if the reference is what they
expect.


## API Reference Documentation (Docstrings)

This section describes conventions for API reference material that’s
extracted from source files. This includes documentation comments for
defined constants, inductive types, and axioms, along with syntax
categories, syntax rules, and parsers. Essentially, if a documentation
comment might appear in a hover, these conventions should
apply. Module docstrings are outside the scope of this section.


### Goals

**There should be a consistent user experience with respect to
documentation.** Documentation should be structured in a predictable
manner. Lean users should be able to find relevant information without
needing to guess where to look first. The documentation should be
written in a consistent style and voice. Technical terminology and
jargon should be internally consistent even when there are multiple
competing traditions.

**In-source documentation should take its viewing contexts into
account.** Docstrings are primarily viewed in editor hovers, as part
of search results in tools like `doc-gen` or Loogle, and in the
reference manual (in this order of importance). They should be
suitable to all these contexts. They are not primarily viewed in the
context of the source module in which they are defined, but they are
always viewed together with the corresponding signature.

**Documentation should be written in a register of English that is as
accessible as possible to those who are not yet Lean users**, whether
they are mathematicians or software developers. Sentences should be
short and jargon should be carefully considered.

**Lean should be self-contained.** Avoid linking to sources outside of
the Lean repository or the reference manual. If a concept needs
explaining, explain it in the reference manual and link there. Don’t
explain any feature solely by reference to other systems—credit them
for their innovations, but explain it from scratch too. Learning
another system should not be a prerequisite for learning
Lean. Exceptions may be made for standard references that have a long
history of stability, when these are used to explain one of the
following topics:

* mathematical concepts that are out of scope for explanation in the
  language reference and for which understanding is not required for
  effective use of Lean, such as Wikipedia articles about specific
  axioms
* specific industry-wide standards or definitions implemented by Lean,
  such as parts of the Unicode standard or IETF RFCs

**Use structured documentation information**. Use attributes like
`tactic_alias` and commands like `recommended_spelling` instead of
ad-hoc text. This helps maintain consistency.

**Conventions should facilitate an automated migration from Markdown
to Verso.** Using Verso in docstrings will make it possible to check
for out-of-date cross-references, to have machine-checked examples,
and for documentation structures (e.g. new kinds of checked examples)
to be defined.


### Non-Goals

Docstrings do not exist to document the details or internals of the
implementation for other developers. This purpose should be served by
ordinary comments.

### General Conventions

* Docstrings should not refer to the surrounding context of the module
  in which they’re defined. Avoid phrases like “`This can be seen in
  `otherFunction`, defined above`” and “`this module's other
  functions`”.
* Docstrings may assume that parameter names in the corresponding
  signature are in scope. They may be referred to by
  name. Specifically, any name in the signature that can be used as a
  named argument at a call site may be referred to by name in the
  docstring; this includes names that are “after the colon.”
* Docstrings should not assume that the body of the definition, the
  constructors of the inductive type, or the fields of the structure
  are visible. They should each make sense in a hover.
* Prefer independently-useful documentation over cross-referencing
  when inheritance doesn’t make sense. This is because following
  cross-references is difficult in many contexts, such as editor
  hovers. It’s useful to relate an operation to existing ones, but the
  description should also stand alone. Instead of “`Variant of `f`
  that also receives the index`”, write a standalone description. The
  relationship to the other function is an additional comment that’s
  useful to include.
* When a concept is used in multiple places, centralize its
  description in the reference manual rather than in one of these
  places.
* When possible, accurately annotate code samples with their syntactic
  category and role. Until this is possible, try to prefix or suffix
  tactic names with `tactic` to help tools disambiguate.
* There’s no need to say what kind of declaration is being documented
  in the docstring.


### Layout and Indentation

Format the docstrings as follows:

* The `/--` should be at the same column as the start of the
  declaration or constructor being documented.
* If the docstring fits within the line length limit, it may be on one
  line that begins with `/--` and ends with `-/`.
* If it does not fit within the length limit, then the `/--` and `-/`
  should each be on their own line. This is also acceptable if the
  docstring could have fit on one line. The contents should be
  indented to the same level as `/--` (or more if demanded by Markdown
  syntax) and lines should break at the column limit. Don’t use a
  one-sentence-per-line or a one-grammatical-clause-per-line
  formatting. Rewrap in VS Code is useful for this.
* Use exactly one blank line between paragraphs.

### Reference Manual

Docstrings can link to the reference manual using the special
`lean-manual://` URL scheme. `lean-manual://section/TAG` links to the
section with tag `TAG`. Tags can be found in the URL on the permalink
indicator in the manual (`🔗`).

### Structure

Docstrings are grouped into the following categories:

* Theorems and Axioms
* Declarations of new propositions or predicates, whether as inductive
  types, structures, or definitions
* Other constants, such as definitions, axioms, opaque constants, and
  instances
* Inductive type declarations
* Structure declarations
* Type classes
* Syntax
* Tactics or conv tactics

Docstrings should note any special notation used for the name being documented.


#### Theorems and Axioms

Docstrings for theorems should be the theorem statement in
English. Not all theorems need docstrings—they should be used for
major theorems.

Docstrings for axioms should begin with common names by which the
axiom is known, followed by the statement in English. They may
additionally elaborate on consequences of the axiom or special
treatment it receives from Lean, but should do so briefly, and link to
further documentation sources for details.

In docstrings for both theorems and axioms, try to formulate the
English-language statement with limited symbols and metavariables. Two
separate presentations (the signature and the docstring) are more
likely to be useful to diverse readers than a transcription of the
symbols from the statement. Remember that our audience includes both
software developers and mathematicians.


##### Examples


```
/--
Equality is symmetric: if `a = b` then `b = a`.
-/
@[symm] theorem Eq.symm {α : Sort u} {a b : α} (h : Eq a b) : Eq b a :=
  h ▸ rfl

/--
Propositional inequality of natural numbers implies Boolean inequality.
-/
theorem Nat.ble_eq_true_of_le (h : LE.le n m) : Eq (Nat.ble n m) true :=
  match h with
  | Nat.le.refl   => Nat.ble_self_eq_true n
  | Nat.le.step h => Nat.ble_succ_eq_true (ble_eq_true_of_le h)
```


```
/--
Propositional Extensionality.

If two propositions are logically equivalent (that is, if each implies the other),
then they are equal; each may replace the other in all contexts.
-/
axiom propext {a b : Prop} : (a ↔ b) → a = b

/--
The Axiom of Choice.

`Nonempty α` is a proof that `α` has an element, but the element itself is
erased. The axiom `choice` supplies a particular element of `α` given only
this proof.

In particular, this axiom is
[global choice](https://en.wikipedia.org/wiki/Axiom_of_global_choice), which
is slightly stronger than the axiom of choice in ZFC.

The axiom of choice is used to derive the law of the excluded middle
(`Classical.em`), so it may show up in axiom listings for proofs that do
not obviously use choice.

This axiom can be used to construct “data” (that is, elements of non-Prop
types). There is no algorithmic interpretation of this axiom, so any definition
that would involve executing `Classical.choice` or other axioms must be marked
`noncomputable`. The compiler will not produce executable code for such
definitions, but they can be reasoned about in the logic.
-/
axiom Classical.choice {α : Sort u} : Nonempty α → α
```



#### Predicates and Propositions

Predicates and new propositions should be documented either with an
English-language translation of their meaning or with a noun phrase
that describes their function. Try to phrase the docstring differently
from the Lean syntax to increase accessibility. For the most basic
connectives, the docstring should also include the words that are
commonly used to refer to the concept, like “conjunction”, “logical
equivalence”, or “bi-implication”.

For most inductively defined predicates, constructors and projections
should be documented according to a plain reading of their logical
meaning.

For basic connectives, constructors and projections should be
documented according to how they are used in proofs. In particular,
constructors should be documented as the corresponding introduction
rule and projections should be documented as elimination rules.

Definitions of predicates should include the meaning of the right-hand
side of the definition in the docstring, because the docstring is
visible in situations where the definition is not (e.g. hovers).


##### Examples


```
/--
The conjunction of two propositions. `And a b` is typically written `a ∧ b`.
-/
@[pp_using_anonymous_constructor]
structure And (a b : Prop) : Prop where
  /-- Proves `a ∧ b`, given a proof of `a` and a proof of `b`. -/
  intro ::
  /-- Given a proof `h : a ∧ b`, proves the left conjunct `a`. -/
  left : a
  /-- Given a proof `h : a ∧ b`, proves the right conjunct `b`. -/
  right : b

/--
The disjunction of two propositions. `Or a b` is typically written `a ∨ b`.
-/
inductive Or (a b : Prop) : Prop where
  /-- Proves `a ∨ b`, given a proof of `a`. -/
  | inl (h : a) : Or a b
  /-- Proves `a ∨ b`, given a proof of `b`. -/
  | inr (h : b) : Or a b

 /--
An equivalence relation `(· ~ ·) : α → α → Prop` is a relation that is:

* reflexive: `x ~ x`
* symmetric: `x ~ y` implies `y ~ x`
* transitive: `x ~ y` and `y ~ z` implies `x ~ z`

Equality is an equivalence relation, and equivalence relations share many of
the properties of equality. In particular, `Quot α r` is most well behaved
when `r` is an equivalence relation. In this case, use `Quotient` instead.
-/
structure Equivalence {α : Sort u} (r : α → α → Prop) : Prop where
  /-- An equivalence relation is reflexive: `x ~ x`. -/
  refl  : ∀ x, r x x
  /-- An equivalence relation is symmetric: `x ~ y` implies `y ~ x`. -/
  symm  : ∀ {x y}, r x y → r y x
  /-- An equivalence relation is transitive: `x ~ y` and `y ~ z` implies `x ~ z`. -/
  trans : ∀ {x y z}, r x y → r y z → r x z

/--
Lexicographical order for products.

A pair is lexicographically less than another pair if its first projection is
smaller, or if its first projection is equal and its second projection is smaller.
That is, `(x₁, y₁) < (x₂, y₂)` when `x₁ < x₂` or `x₁ = x₂` and `y₁ < y₂`.
-/
def Prod.lexLt [LT α] [LT β] (s : α × β) (t : α × β) : Prop :=
  s.1 < t.1 ∨ (s.1 = t.1 ∧ s.2 < t.2)

/--
`xs` is a permutation of `ys`.

`Perm xs ys` is normally written `xs ~ ys`.
-/
inductive Perm : (xs : List α) → (ys : List α) → Prop
  /-- The empty list is a permutation of itself. -/
  | nil : Perm [] []
  /--
  If one list is a permutation of another, then adding the same element to the head of each yields
  a permutation.
  -/
  | cons (x : α) {xs ys : List α} : Perm xs ys → Perm (x :: xs) (x :: ys)
  /--
  Swapping the first two elements of a list yields a permutation.
  -/
  | swap (x y : α) (xs : List α) : Perm (y :: x :: xs) (x :: y :: xs)
  /-- `Perm` is transitive. -/
  | trans {xs ys zs : List α} : Perm xs ys → Perm ys zs → Perm xs zs
```



#### Constants

Docstrings for constants should have the following structure:

* Short summary
* Details
* Examples

The **short summary** should be 1–3 sentences (ideally 1) and provide
enough information for most readers to quickly decide whether the
constant is relevant to their task. The first (or only) sentence of
the short summary should be a *sentence fragment* in which the subject
is implied to be the documented item, written in present tense
indicative, or a *noun phrase* that characterizes the documented
item. Subsequent sentences should be complete sentences. If no verb
seems to make sense, a noun phrase punctuated as a sentence is
acceptable. If the signature names parameters, then the short summary
may refer to them. The summary should be written as a single
paragraph.

**Details**, if needed, may be 1-3 paragraphs that describe further
relevant information. They may insert links as needed. The details may
include explanatory examples that can’t necessarily be machine checked
and don’t fit the format.

**Examples** should be in one of two formats, following the line
`Examples:` (or `Example:` if there’s exactly one):

* A bulleted list of short examples, following the line
  `Examples:`. Short examples are equalities, written in inline code
  elements, where both sides should be equal terms with the same
  type. Free variables are treated equivalently to automatically
  inserted implicit parameters. Typically, the left side reduces to
  the right. The two sides don’t need to be definitionally
  equal. Eventually, a variety of strategies will be used to validate
  the examples, including definitional equality, equality of
  propositions modulo the default simp set, and equality of closed
  terms modulo `#eval`. For types, short examples may alternately be
  terms that illustrate the usage of the type together with very brief
  explanations.
* Alternating code blocks that indicate input and output, following
  the line `Examples:`. The input should be marked as Lean using
  Markdown’s language indication notation, with the `example` class,
  and the output should be marked as `output`. Each input should
  contain one or more Lean commands. There may be zero or more outputs
  for each input, and they should be compared as with the default
  settings for `#guard_msgs` (though this isn't yet automatically
  checked).


##### Examples


````lean
/--
Applies the function `f` to each element of the list `xs`, returning a list of the results.

The results are in the same order as the corresponding inputs. This takes linear time: O(|`xs`|).

Examples:
* `map String.length ["a", "21", ""] = [1, 2, 0]`
* `map Nat.succ [] = []`
-/
@[specialize] def map (f : α → β) : (xs : List α) → List β
  | []  => []
  | a::as => f a :: map f as

/--
Returns the current thread's standard input stream.

Use `IO.setStdin` to replace the current thread's standard input stream.
-/
@[extern "lean_get_stdin"] opaque getStdin  : BaseIO FS.Stream

/--
Computes a value by iteration from a starting state `a`.

At each step, `f` is applied to the current state. `f` may return either a new state for further
iteration or a final value that stops iteration.

Example:
```lean example
#eval iterate 6 fun x => do
  if x < 5 then
    pure (.inr ())
  else
    IO.println x
    pure (.inl (x - 1))
```
```output
6
5
```
-/
@[specialize] partial def iterate (a : α) (f : α → IO (Sum α β)) : IO β := do
  let v ← f a
  match v with
  | Sum.inl a => iterate a f
  | Sum.inr b => pure b

/--
Checks whether the provided proposition `c` is true or false and invokes the corresponding
branch `t` or `e` with a suitable proof.

The "dependent" `if-then-else`, normally written via the notation `if h : c then t else e`, is
syntactic sugar for `dite c (fun h => t) (fun h => e)`. As a result, the code in each branch
can observe the truth or falsity of the condition.

For example, `GetElem.getElem arr i h`, normally written `arr[i]` with `h` found automatically,
expects a proof `h : i < arr.size` in order to avoid a bounds check. This bounds check can be
lifted to a branch: `if h : i < arr.size then arr[h] else ...`, and one bounds check can be used
for multiple array accesses.
-/
@[macro_inline] def dite {α : Sort u} (c : Prop) [h : Decidable c] (t : c → α) (e : Not c → α) : α :=
  h.casesOn e t
````



#### Inductive Types

Type constructors and constructors follow the same conventions as
other constants. The short description will often use a noun phrase to
characterize them. Logical content should follow the conventions
described for theorems.


##### Examples


```
/--
A linked list with elements of type `α`.

Like `Array`, `List` represents an ordered sequence. Their performance
characteristics differ, however, and are described in [the Lean Language Reference](manual://...).
-/
inductive List (α : Type u) where
  /-- The empty list, typically written `[]`. -/
  | nil : List α
  /--
  A list in which the first element is `head` and the rest of the list is `tail`,
  typically written `head :: tail`.
  -/
  | cons (head : α) (tail : List α) : List α
```



#### Structures

Type constructors, projections, and constructors follow the same
conventions as other constants. The short description will often use a
noun phrase to characterize all three; fields should be described
according to what they contain, rather than as functions that retrieve
the contents. Logical content should follow the conventions described
for theorems. Structure field docstrings may refer to any of the
fields, in addition to names bound in the signature.


##### Examples


```
/--
All the elements of some base type that satisfy a predicate.

`Subtype p`, usually written as `{x : α // p x}`, is a type which
represents all the elements `x : α` for which `p x` is true.
Logically, it is a pair-like type. If `v : α` and `h : p x`, then
`⟨v, h⟩ : {x // p x}`. There is a coercion from `⟨v, h⟩ : {x // p x}`
to `v : α`.
-/

@[pp_using_anonymous_constructor]
structure Subtype {α : Sort u} (p : α → Prop) where
  /--
  The underlying element in the base type.

  This is applied as a coercion when the expected type is `α`.
  -/
  val : α
  /--
  The value `val` satisfies the predicate.
  -/
  property : p val

/--
A section or “slice” of an array that shares the underlying memory allocation.

Subarrays can be used to avoid unnecessary copying and allocation of arrays. However,
subarrays retain a reference to their underlying array. The existence of multiple
subarrays from the same array will thus prevent array operations from being optimized
into mutation, even if the subarrays are disjoint.
-/
structure Subarray (α : Type u) where
  /--
  The underlying array.
  -/
  array : Array α
  /--
  The first index in the subarray, inclusive.
  -/
  start : Nat
  /--
  The last index in the subarray, exclusive.
  -/
  stop : Nat
  /--
  The start of the subarray is not greater than the end.
  -/
  start_le_stop : start ≤ stop
  /--
  The end of the subarray is within bounds for the underlying array.
  -/
  stop_le_array_size : stop ≤ array.size
```



#### Classes

Docstrings for class declarations are likely to appear in hovers in
error messages experienced by new users. It’s important that the
docstring is clearly connected to any notation that the class
overloads and that it uses accessible language.


##### Examples


```
/--
Addition of two terms that don't necessarily have the same type. Instances are used to assign
meaning to the `+` operator.

`HAdd` is short for "heterogeneous addition."
-/
class HAdd (α : Type u) (β : Type v) (γ : outParam (Type w)) where
  /--
  `a + b` computes the sum of `a` and `b`.

  The precise meaning of this operation depends on the types of `a`, `b`, and the
  entire term.
  -/
  hAdd : α → β → γ
```



#### Syntax Categories

Syntax categories should be described by what they represent. Their
documentation should consist of a noun phrase that describes the
category, pluralized and punctuated as a sentence, followed by any
additional necessary information in complete sentences in paragraph
form. If the docstring contains only a noun phrase, don’t punctuate
it.


##### Examples


```
/-- JSON literals -/
declare_syntax_cat json (behavior := symbol)
```



#### Syntax Rules

Syntax rules and parsers should be described by singular noun
phrases. Test the docstrings and ensure that they make sense in the
context of hovers. Remember to use a suitable `recommended_spelling`
command for term notation.


##### Examples


```
/-- JSON array -/
syntax "[" json,* "]" : json
/--
JSON identifier.

This is used as a key in an object.
-/
syntax jsonIdent := ident <|> str
/-- JSON key/value pair -/
syntax jsonField := jsonIdent ": " json
/-- JSON object -/
syntax "{" jsonField,* "}" : json

/-- A JSON literal as a Lean term -/
syntax "json% " json : term

/-- An `rcases` pattern is an `rintro` pattern -/
syntax (name := rintroPat.one) rcasesPat : rintroPat
/--
A multi-argument binder for a sequence of patterns.

The pattern `(pat1 ... : ty)` binds the variables in the pattern and ensures that each
has type `ty`.
-/
syntax (name := rintroPat.binder) (priority := default+1) -- to override rcasesPat.paren
  "(" rintroPat+ (" : " term)? ")" : rintroPat

/--
A bijection between two types is a pair of mutually inverse functions between them.
-/
structure Bijection (α β) where
  into : α → β
  outOf : β → α
  /- Properties omitted -/

@[inherit_doc Bijection]
infix:50 " ⇔ " => Bijection

recommended_spelling "bij" for "⇔" in [Bijection, «term_⇔_»]
```

#### Tactics

Docstrings for tactics should have the following structure:

* Short summary
* Details
* Variants
* Examples

Sometimes more than one declaration is needed to implement what the user
sees as a single tactic. In that case, only one declaration should have
the associated docstring, and the others should have the `tactic_alt`
attribute to mark them as an implementation detail.

The **short summary** should be 1–3 sentences (ideally 1) and provide
enough information for most readers to quickly decide whether the
tactic is relevant to their task. The first (or only) sentence of
the short summary should be a full sentence in which the subject
is an example invocation of the tactic, written in present tense
indicative. If the example tactic invocation names parameters, then the
short summary may refer to them. For the example invocation, prefer the
simplest or most typical example. Explain more complicated forms in the
variants section. If needed, abbreviate the invocation by naming part of
the syntax and expanding it in the next sentence. The summary should be
written as a single paragraph.

**Details**, if needed, may be 1-3 paragraphs that describe further
relevant information. They may insert links as needed. This section
should fully explain the scope of the tactic: its syntax format,
on which goals it works and what the resulting goal(s) look like. It
should be clear whether the tactic fails if it does not close the main
goal and whether it creates any side goals. The details may include
explanatory examples that can’t necessarily be machine checked and
don’t fit the format.

If the tactic is extensible using `macro_rules`, mention this in the
details, with a link to `lean-manual://section/tactic-macro-extension`
and give a one-line example. If the tactic provides an attribute or a
command that allows the user to extend its behavior, the documentation
on how to extend the tactic belongs to that attribute or command. In the
tactic docstring, use a single sentence to refer the reader to this
further documentation.

**Variants**, if needed, should be a bulleted list describing different
options and forms of the same tactic. The reader should be able to parse
and understand the parts of a tactic invocation they are hovering over,
using this list. Each list item should describe an individual variant
and take one of two formats: the **short summary** as above, or a
**named list item**. A named list item consists of a title in bold
followed by an indented short paragraph.

Variants should be explained from the perspective of the tactic's users, not
their implementers. A tactic that is implemented as a single Lean parser may
have multiple variants from the perspective of users, while a tactic that is
implemented as multiple parsers may have no variants, but merely an optional
part of the syntax.

**Examples** should start with the line `Examples:` (or `Example:` if
there’s exactly one). The section should consist of a sequence of code
blocks, each showing a Lean declaration (usually with the `example`
keyword) that invokes the tactic. When the effect of the tactic is not
clear from the code, you can use code comments to describe this. Do
not include text between examples, because it can be unclear whether
the text refers to the code before or after the example.

##### Example

````
`rw [e]` uses the expression `e` as a rewrite rule on the main goal,
then tries to close the goal by "cheap" (reducible) `rfl`.

If `e` is a defined constant, then the equational theorems associated with `e`
are used. This provides a convenient way to unfold `e`. If `e` has parameters,
the tactic will try to fill these in by unification with the matching part of
the target. Parameters are only filled in once per rule, restricting which
later rewrites can be found. Parameters that are not filled in after
unification will create side goals. If the `rfl` fails to close the main goal,
no error is raised.

`rw` may fail to rewrite terms "under binders", such as `∀ x, ...` or `∃ x,
...`. `rw` can also fail with a "motive is type incorrect" error in the context
of dependent types. In these cases, consider using `simp only`.

* `rw [e₁, ... eₙ]` applies the given rules sequentially.
* `rw [← e]` or `rw [<- e]` applies the rewrite in the reverse direction.
* `rw [e] at l` rewrites with `e` at location(s) `l`.
* `rw (occs := .pos L) [e]`, where `L` is a literal list of natural numbers,
  only rewrites the given occurrences in the target. Occurrences count from 1.
* `rw (occs := .neg L) [e]`, where `L` is a literal list of natural numbers,
  skips rewriting the given occurrences in the target. Occurrences count from 1.

Examples:

```lean
example {a b : Nat} (h : a + a = b) : (a + a) + (a + a) = b + b := by rw [h]
```

```lean
example {f : Nat -> Nat} (h : ∀ x, f x = 1) (a b : Nat) : f a = f b := by
  rw [h] -- `rw` instantiates `h` only once, so this is equivalent to: `rw [h a]`
  -- goal: ⊢ 1 = f b
  rw [h] -- equivalent to: `rw [h b]`
```
````


## Dictionary

Use the following terminology:

| **Preferred term** | **Other terms** |
| --- | --- |
| lexicographical | lexicographic |
| discriminant (of a match) | scrutinee, target |
| recursor | eliminator, induction principle |
| syntax category | nonterminal |
| term (for Lean terms) | expression, statement |
| heterogeneous equality | John Major equality |
| inductive type/structure | datatype |
| instance synthesis | typeclass search, typeclass resolution |

Some of the other terms are suitable as more specific terms than the
preferred terms. For example, while “induction principle” should not
be used for generated recursors in general, it's a great description
of a special-purpose reasoning tool provided by a library.
