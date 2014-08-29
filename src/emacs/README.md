lean-mode
=========

Emacs mode for [lean theorem prover][lean]

[lean]: https://github.com/leanprover/lean

Requirement
-----------

``lean-mode`` requires [Emacs 24][emacs24] and following (optional)
packages which can be installed via <kbd>M-x package-install</kbd>.

 - [company][company]
 - [dash][dash]
 - [dash-functional][dash]
 - [fill-column-indicator][fci]
 - [flycheck][flycheck]
 - [whitespace-cleanup-mode][wcm]


[emacs24]: http://www.gnu.org/software/emacs
[flycheck]: http://flycheck.readthedocs.org/en/latest
[fci]: https://github.com/alpaker/Fill-Column-Indicator
[wcm]: https://github.com/purcell/whitespace-cleanup-mode
[MELPA]: http://melpa.milkbox.net
[dash]: https://github.com/magnars/dash.el
[company]: http://company-mode.github.io/

Install
-------

Put the following elisp code on your emacs setup (e.g. ``.emacs.d/init.el``):

```elisp
(require 'package)
(add-to-list 'package-archives
             '("melpa" . "http://melpa.milkbox.net/packages/") t)
(package-initialize)
(package-refresh-contents)

;; Install required packages for lean-mode
(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck whitespace-cleanup-mode fill-column-indicator))
(dolist (p lean-mode-required-packages)
  (when (not (package-installed-p p))
    (package-install p)))

;; Set up lean-root path
(setq lean-rootdir "~/projects/lean")
(setq-local lean-emacs-path
            (concat (file-name-as-directory lean-rootdir)
                    (file-name-as-directory "src")
                    "emacs"))
(add-to-list 'load-path (expand-file-name lean-emacs-path))
(require 'lean-mode)

;; Customization for lean-mode
(customize-set-variable 'lean-delete-trailing-whitespace t)
(customize-set-variable 'lean-flycheck-use t)
(customize-set-variable 'lean-eldoc-use t)
```

Key Bindings
------------

|Key                | Function                          |
|-------------------|-----------------------------------|
|<kbd>C-c C-x</kbd> | lean-std-exe                      |
|<kbd>C-c C-l</kbd> | lean-std-exe                      |
|<kbd>C-c C-t</kbd> | lean-eldoc-documentation-function |
|<kbd>C-c C-f</kbd> | lean-fill-placeholder             |
|<kbd>M-.</kbd>     | lean-find-tag                     |
|<kbd>TAB</kbd>     | lean-complete-tag                 |
|<kbd>C-c C-o</kbd> | lean-set-option                   |
|<kbd>C-c C-e</kbd> | lean-eval-cmd                     |
