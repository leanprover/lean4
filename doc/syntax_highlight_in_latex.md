We provide a way to syntax-highlight Lean code in LaTeX documents.
It requires a Python package `Pygments` and a LaTeX package `minted`.


Python Package: `Pygments`
--------------------------

Checkout [Leanprover's Pygments repository][lean-pygments] and build Pygments:

```bash
hg clone https://bitbucket.org/leanprover/pygments-main
cd pygments-main
make mapfiles
sudo ./setup.py install
````

[lean-pygments]: https://bitbucket.org/leanprover/pygments-main


LaTeX package: `minted`
-----------------------

Save the latest version of [minted.sty][minted.sty] at the working directory.

[minted]: https://github.com/gpoore/minted
[minted.sty]: https://raw.githubusercontent.com/gpoore/minted/master/source/minted.sty


How to use them (example)
-------------------------

Please save the following sample LaTeX file as `test.tex`:

```latex
\documentclass{article}
\usepackage{minted}
\setminted{encoding=utf-8}
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

 - `xelatex` is required to handle unicode in LaTeX.
 - `--shell-escape` option is needed to allow `xelatex` to execute `pygmentize` in a shell.


Contribute
----------

Please fork [Leanprover's Pygments repository][lean-pygments], improve it, and make a pull-request.
