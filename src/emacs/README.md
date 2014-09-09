lean-mode
=========

Emacs mode for [lean theorem prover][lean]

[lean]: https://github.com/leanprover/lean

Requirement
-----------

``lean-mode`` requires [Emacs 24][emacs24] and following
packages which can be installed via <kbd>M-x package-install</kbd>.

 - [dash][dash]
 - [dash-functional][dash]
 - [s][s]

[emacs24]: http://www.gnu.org/software/emacs
[MELPA]: http://melpa.milkbox.net
[dash]: https://github.com/magnars/dash.el
[s]: https://github.com/magnars/s.el

The following packages are *optional* but we recommend to install them
to use full features of ``lean-mode``.

 - [company][company]
 - [flycheck][flycheck]
 - [fill-column-indicator][fci]
 - [lua-mode][lua-mode]
 - [mmm-mode][mmm-mode]
 - [whitespace-cleanup-mode][wcm]

[company]: http://company-mode.github.io/
[flycheck]: http://flycheck.readthedocs.org/en/latest
[fci]: https://github.com/alpaker/Fill-Column-Indicator
[lua-mode]: http://immerrr.github.io/lua-mode/
[mmm-mode]: https://github.com/purcell/mmm-mode
[wcm]: https://github.com/purcell/whitespace-cleanup-mode

Install
-------

Put the following elisp code on your emacs setup (e.g. ``.emacs.d/init.el``):

```elisp
(require 'package)
(add-to-list 'package-archives
             '("melpa" . "http://melpa.milkbox.net/packages/") t)
(package-initialize)
(package-refresh-contents)

;; Install required/optional packages for lean-mode
(defvar lean-mode-required-packages
  '(company dash dash-functional flycheck whitespace-cleanup-mode
    fill-column-indicator s lua-mode mmm-mode))
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

If experience a problem reading unicode characters on emacs, consider
having the following setup:

```elisp
(when (member "DejaVu Sans Mono" (font-family-list))
  (set-face-attribute 'default nil :font "DejaVu Sans Mono-11"))
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
|<kbd>TAB</kbd>     | lean-tab-indent-or-complete       |
|<kbd>C-c C-o</kbd> | lean-set-option                   |
|<kbd>C-c C-e</kbd> | lean-eval-cmd                     |
