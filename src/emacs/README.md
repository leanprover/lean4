lean-mode
=========

Requirement
-----------

 - [Emacs 24][emacs24]
 - [flycheck][flycheck]
 - [fill-column-indicator][fci]

[emacs24]: http://www.gnu.org/software/emacs/
[flycheck]: http://flycheck.readthedocs.org/en/latest/
[fci]: https://github.com/alpaker/Fill-Column-Indicator

Setup
-----

```elisp
(setq lean-rootdir "~/projects/lean")
(setq-local lean-emacs-path
            (concat (file-name-as-directory lean-rootdir)
                    (file-name-as-directory "src")
                    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)

;; customization
(customize-set-variable 'lean-show-rule-column-method 'vline)
(customize-set-variable 'lean-rule-column 100)
(customize-set-variable 'lean-delete-trailing-whitespace t)
```
