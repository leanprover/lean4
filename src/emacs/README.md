lean-mode
=========

Emacs mode for [lean theorem prover][lean]

[lean]: https://github.com/leanprover/lean

Requirement
-----------

``lean-mode`` requires [Emacs 24][emacs24] and following (optional)
packages which can be installed via ``M-x package-install``.

 - [flycheck][flycheck]
 - [fill-column-indicator][fci]
 - [whitespace-cleanup-mode][wcm]

To install them, you need to have [MELPA][MELPA] in your
``package-archives``. You can add it by evaluating the following elisp
code:

```elisp
(add-to-list 'package-archives
             '("marmalade" . "http://marmalade-repo.org/packages/") t)
```

[emacs24]: http://www.gnu.org/software/emacs/
[flycheck]: http://flycheck.readthedocs.org/en/latest/
[fci]: https://github.com/alpaker/Fill-Column-Indicator
[wcm]: https://github.com/purcell/whitespace-cleanup-mode
[MELPA]: http://melpa.milkbox.net/

Setup
-----

Put the following elisp code on your emacs setup:

```elisp
(setq lean-rootdir "~/projects/lean")
(setq-local lean-emacs-path
            (concat (file-name-as-directory lean-rootdir)
                    (file-name-as-directory "src")
                    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)

;; lean customization
(customize-set-variable 'lean-show-rule-column-method 'vline)
(customize-set-variable 'lean-rule-column 100)
(customize-set-variable 'lean-rule-color "#ff0000")
(customize-set-variable 'lean-delete-trailing-whitespace t)
```
