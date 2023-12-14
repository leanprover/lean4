You can copy highlighted code [straight from VS Code](https://code.visualstudio.com/updates/v1_10#_copy-with-syntax-highlighting) to any rich text editor supporting HTML input. For highlighting code in LaTeX, there are two options:
* [listings](https://ctan.org/pkg/listings), which is a common package and simple to set up, but you may run into some restrictions of it and LaTeX around Unicode
* [`minted`](https://ctan.org/pkg/minted), a LaTeX package wrapping the [Pygments](https://pygments.org/) syntax highlighting library. It needs a few more steps to set up, but provides unrestricted support for Unicode when combined with XeLaTeX or LuaLaTex.

## Example with `listings`

Save [`lstlean.tex`](https://raw.githubusercontent.com/leanprover/lean4/master/doc/latex/lstlean.tex) into the same directory, or anywhere in your `TEXINPUTS` path, as the following test file:
```latex
\documentclass{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{listings}
\usepackage{amssymb}

\usepackage{color}
\definecolor{keywordcolor}{rgb}{0.7, 0.1, 0.1}   % red
\definecolor{tacticcolor}{rgb}{0.0, 0.1, 0.6}    % blue
\definecolor{commentcolor}{rgb}{0.4, 0.4, 0.4}   % grey
\definecolor{symbolcolor}{rgb}{0.0, 0.1, 0.6}    % blue
\definecolor{sortcolor}{rgb}{0.1, 0.5, 0.1}      % green
\definecolor{attributecolor}{rgb}{0.7, 0.1, 0.1} % red

\def\lstlanguagefiles{lstlean.tex}
% set default language
\lstset{language=lean}

\begin{document}
\begin{lstlisting}
theorem funext {f₁ f₂ : ∀ (x : α), β x} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by
  show extfunApp (Quotient.mk f₁) = extfunApp (Quotient.mk f₂)
  apply congrArg
  apply Quotient.sound
  exact h
\end{lstlisting}
\end{document}
```
Compile the file via
```bash
$ pdflatex test.tex
```

* for older LaTeX versions, you might need to use `[utf8x]` instead of `[utf8]` with `inputenc`

## Example with `minted`

First [install Pygments](https://pygments.org/download/). Then save [`lean4.py`](https://raw.githubusercontent.com/leanprover/lean4/master/doc/latex/lean4.py), which contains an version of the Lean highlighter updated for Lean 4, and the following sample LaTeX file `test.tex` into the same directory:

```latex
\documentclass{article}
\usepackage{fontspec}
% switch to a monospace font supporting more Unicode characters
\setmonofont{FreeMono}
\usepackage{minted}
% instruct minted to use our local theorem.py
\newmintinline[lean]{lean4.py:Lean4Lexer -x}{bgcolor=white}
\newminted[leancode]{lean4.py:Lean4Lexer -x}{fontsize=\footnotesize}
\usemintedstyle{tango}  % a nice, colorful theme

\begin{document}
\begin{leancode}
theorem funext {f₁ f₂ : ∀ (x : α), β x} (h : ∀ x, f₁ x = f₂ x) : f₁ = f₂ := by
  show extfunApp (Quotient.mk' f₁) = extfunApp (Quotient.mk' f₂)
  apply congrArg
  apply Quotient.sound
  exact h
\end{leancode}
\end{document}
```

If your version of `minted` is v2.7 or newer, but before v3.0,
you will additionally need to follow the workaround described in https://github.com/gpoore/minted/issues/360.

You can then compile `test.tex` by executing the following command:

```bash
xelatex --shell-escape test.tex
```

Some remarks:

 - either `xelatex` or `lualatex` is required to handle Unicode characters in the code.
 - `--shell-escape` is needed to allow `xelatex` to execute `pygmentize` in a shell.
 - If the chosen monospace font is missing some Unicode symbols, you can direct them to be displayed using a fallback font or other replacement LaTeX code.
``` latex
\usepackage{newunicodechar}
\newfontfamily{\freeserif}{DejaVu Sans}
\newunicodechar{✝}{\freeserif{✝}}
\newunicodechar{𝓞}{\ensuremath{\mathcal{O}}}
```
 - minted has a "helpful" feature that draws red boxes around characters the chosen lexer doesn't recognize.
 Since the Lean lexer cannot encompass all user-defined syntax, it is advisable to [work around](https://tex.stackexchange.com/a/343506/14563) this feature.
