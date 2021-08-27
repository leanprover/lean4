Installation
============

To use `lean4-mode` in Emacs, add the following to your `init.el`:
```
;; You need to modify the following line
(setq load-path (cons "/path/to/lean4/lean4-mode" load-path))

(setq lean4-mode-required-packages '(dash f flycheck lsp-mode magit-section s))

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
(package-initialize)
(let ((need-to-refresh t))
  (dolist (p lean4-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))

(require 'lean4-mode)
```
Alternatively if you are a fan of `use-package` and `straight.el` you
can use:
```
(use-package lean4-mode
  :straight (lean4-mode :type git :host github :repo "leanprover/lean4"
             :files ("lean4-mode/lean4*.el"))
  ;; to defer loading the package until required
  :commands (lean4-mode))
```
If you are working on the `lean4` repository already and don't want to
have two separate checkouts you can use:
```
(use-package lean4-mode
  :straight (lean4-mode :local-repo "/path/to/your/lean4"
             :files ("lean4-mode/lean4*.el"))
  ;; to defer loading the package until required
  :commands (lean4-mode))
```


Trying It Out
=============

If things are working correctly, you should see the word ``Lean 4`` in the
Emacs mode line when you open a file with extension `.lean`. Emacs will ask you
to identify the "project" this file belongs to. If you then type
```lean
#check id
```
the word ``#check`` will be underlined, and hovering over it will show
you the type of ``id``. The mode line will show ``FlyC:0/1``, indicating
that there are no errors and one piece of information displayed.

Settings
========

Set these with e.g. `M-x customize-variable`.

* `lsp-headerline-breadcrumb-enable`: show a "breadcrumb bar" of namespaces and sections surrounding the current location (default: off)

Key Bindings and Commands
=========================

| Key                | Function                                                                        |
|--------------------|---------------------------------------------------------------------------------|
| <kbd>C-c C-k</kbd> | show the keystroke needed to input the symbol under the cursor                  |
| <kbd>C-c C-d</kbd> | recompile & reload imports (`lean4-refresh-file-dependencies`)                  |
| <kbd>C-c C-x</kbd> | execute Lean in stand-alone mode (`lean4-std-exe`)                              |
| <kbd>C-c C-i</kbd> | toggle info view showing goals and errors at point (`lean4-toggle-info-buffer`) |
| <kbd>C-c ! n</kbd> | flycheck: go to next error                                                      |
| <kbd>C-c ! p</kbd> | flycheck: go to previous error                                                  |

For `lsp-mode` bindings, see https://emacs-lsp.github.io/lsp-mode/page/keybindings/ (not all capabilities are supported currently).

In the default configuration, the Flycheck annotation `FlyC:n/n` indicates the
number of errors / responses from Lean; clicking on `FlyC` opens the Flycheck menu.
