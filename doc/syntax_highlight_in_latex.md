The [Pygments](https://pygments.org/) syntax highlighting library has official support for Lean (however, Lean 4 keywords have not been added yet), which can be used in LaTeX via the [`minted`](https://ctan.org/pkg/minted) package.

# Example

Save the following sample LaTeX file as `test.tex`:

```latex
\documentclass{article}
\usepackage{minted}
\usepackage{fontspec}
\setmainfont{FreeSerif}
\setmonofont{FreeMono}
\usepackage{fullpage}
\begin{document}
\begin{minted}[mathescape,
               linenos,
               numbersep=5pt,
               frame=lines,
               framesep=2mm]{Lean}
theorem mul_cancel_left_or {a b c : ℤ} (H : a * b = a * c) : a = 0 ∨ b = c :=
have H2 : a * (b - c) = 0, by simp,
have H3 : a = 0 ∨ b - c = 0, from mul_eq_zero H2,
or.imp_or_right H3 (assume H4 : b - c = 0, sub_eq_zero H4)
\end{minted}
\end{document}
```

You can compile `test.tex` by executing the following command:

```bash
xelatex --shell-escape test
```

Some remarks:

 - either `xelatex` or `lualatex` is required to handle Unicode characters in the code.
 - `--shell-escape` is needed to allow `xelatex` to execute `pygmentize` in a shell.
 - If the chosen monospace font is missing some Unicode symbols, you can direct them to be displayed using a fallback font.
``` latex
\usepackage{newunicodechar}
\newfontfamily{\freeserif}{DejaVu Sans}
\newunicodechar{✝}{\freeserif{✝}}
```
 - minted has a "helpful" feature that draws red boxes around characters the chosen lexer doesn't recognize.
 Since the Lean lexer cannot encompass all user-defined syntax, it is advisable to [work around](https://tex.stackexchange.com/a/343506/14563) this feature.
