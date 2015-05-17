lstlean.tex
===========

The file `lstlean.tex` contains /Lean/ style definitions for the
`listings` package, which can be used to typeset Lean code in a
Latex document. For more information, see the documentation for the
`listings` package and the sample document `sample.tex`.

You need the following packages installed:

- `listings`
- `inputenc`
- `color`

Because `listings` does not work well with unicode, the style
replaces all unicode characters with Latex equivalents. Some of the
replacment symbols require the `amssymb` package.

To use the style, all you need to do is include `lstlean.tex` in
the same directory as your Latex source, and include the following
preamble in your document:
```
\documentclass{article}

\usepackage[utf8x]{inputenc}
\usepackage{amssymb}

\usepackage{color}
\definecolor{keywordcolor}{rgb}{0.7, 0.1, 0.1}   % red
\definecolor{tacticcolor}{rgb}{0.1, 0.2, 0.6}    % blue
\definecolor{commentcolor}{rgb}{0.4, 0.4, 0.4}   % grey
\definecolor{symbolcolor}{rgb}{0.0, 0.1, 0.6}    % blue
\definecolor{sortcolor}{rgb}{0.1, 0.5, 0.1}      % green
\definecolor{attributecolor}{rgb}{0.7, 0.1, 0.1} % red

\usepackage{listings}
\def\lstlanguagefiles{lstlean.tex}
\lstset{language=lean}
```

The `inputenc` package is needed to handle unicode input. Of
course, you can set the colors any way you want. In your document,
you can then in-line code with the `\lstinline{...}`, and add a code
block with the `\begin{lstlisting} ... \end{lstlisting}`
environment.

Note that if you use a unicode symbol that is not currently handled in
`lstlean.tex`, you can simply add it to the list there, together
with the Latex equivalent you would like to use.
