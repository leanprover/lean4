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

First [install Pygments](https://pygments.org/download/) (version 2.18 or newer).
Then save the following sample LaTeX file `test.tex` into the same directory:

```latex
\documentclass{article}
\usepackage{fontspec}
% switch to a monospace font supporting more Unicode characters
\setmonofont{FreeMono}
\usepackage{minted}
\newmintinline[lean]{lean4}{bgcolor=white}
\newminted[leancode]{lean4}{fontsize=\footnotesize}
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
 - If you are using an old version of Pygments, you can copy 
   [`lean.py`](https://raw.githubusercontent.com/pygments/pygments/master/pygments/lexers/lean.py) into your working directory,
   and use `lean4.py:Lean4Lexer -x` instead of `lean4` above.
   If your version of `minted` is v2.7 or newer, but before v3.0,
   you will additionally need to follow the workaround described in https://github.com/gpoore/minted/issues/360.
