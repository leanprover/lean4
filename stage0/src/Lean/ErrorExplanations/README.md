# Error Explanations

## Overview

This directory contains explanations for named errors in Lean core.
Explanations associate to each named error or warning a long-form
description of its meaning and causes, relevant background
information, and strategies for correcting erroneous code. They also
provide examples of incorrect and corrected code. While error
explanations are declared in source, they are viewed as part of
external documentation linked from error messages.

Explanations straddle the line between diagnostics and documentation:
unlike the error messages they describe, explanations serve not only
to aid the debugging process but also to help users understand the
principles of the language that underlie the error. Accordingly, error
explanations should be written with both of these aims in mind. Refer
to existing explanations for examples of the formatting and content
conventions described here.

Once an error explanation has been registered, use the macros
`throwNamedError`, `logNamedError`, `throwNamedErrorAt` and
`logNamedErrorAt` to tag error messages with the appropriate
explanation name. Doing so will display a widget in the Infoview with
the name of the error and a link to the corresponding explanation.

## Registering Explanations

New error explanations are declared using the
`register_error_explanation` command. Each explanation should
appear in a separate submodule of `Lean.ErrorExplanations` whose name
matches the error name being declared; the module should be marked
with `prelude` and import only `Lean.ErrorExplanation`. The
`register_error_explanation` keyword is preceded by a doc
comment containing the explanation (written in Markdown, following the
structure guidelines below) and is followed by the name of the
explanation and a `Lean.ErrorExplanation.Metadata` structure
describing the error. All errors have two-component names: the first
identifies the package or "domain" to which the error belongs (in
core, this will nearly always be `lean`); the second identifies the
error itself. Error names are written in upper camel case and should
be descriptive but not excessively verbose. Abbreviations in error
names are acceptable, but they should be reasonably clear (e.g.,
abbreviations that are commonly used elsewhere in Lean, such as `Ctor`
for "constructor") and should not be ambiguous with other vocabulary
likely to appear in error names (e.g., use `Indep` rather than `Ind`
for "independent," since the latter could be confused with
"inductive").


## Structure

### Descriptions

Error explanations consist of two parts: a prose description of the
error and code examples. The description should begin by explaining
the meaning of the error and why it occurs. It should also briefly
explain, if appropriate, any relevant context, such as related errors
or relevant entries in the reference manual. The latter is especially
useful for directing users to important concepts for understanding an
error: while it is appropriate to provide brief conceptual exposition
in an error explanation, avoid extensively duplicating content that
can be found elsewhere in the manual. General resolution or debugging
strategies not tied to specific examples can also be discussed in the
description portion of an explanation.

### Examples

The second half of an explanation (set off by the level-1 header
"Examples") contains annotated code examples. Each of these consists
of a level-2 header with the name of the example, followed immediately
by a sequence of code blocks containing self-contained minimal working
(or error-producing) examples (MWEs) and outputs. The first MWE should
have the Markdown info string `lean broken` and demonstrate the error
in question; it should be followed by an `output` code block with the
corresponding error message. Subsequent MWEs should have the info
string `lean fixed` and illustrate how to rewrite the code correctly.
Finally, after these MWEs, include explanatory text describing the
example and the cause and resolution of the error it demonstrates.

Note that each MWE in an example will be rendered as a tab, and the
full example (including its explanatory text) will appear in a
collapsible "Example" block like those used elsewhere in the manual.
Include `(title := "Title")` in the info string of an MWE to assign it
a custom title (for instance, if there are multiple "fixed" MWEs).
Examples should center on code: prose not specific to the example
should generally appear in the initial half of the explanation.
However, an example should provide sufficient commentary for users to
understand how it illustrates relevant ideas from the preceding
description and what was done to resolve the exemplified error.

Choose examples carefully: they should be relatively minimal, so as to
draw out the error itself, but not so contrived as to impede
comprehension. Each should contain a distinct, representative instance
of the error to avoid the need for excessively many.
