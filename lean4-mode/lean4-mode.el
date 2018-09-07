;;; lean4-mode.el --- A major mode for the Lean language -*- lexical-binding: t -*-

;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Copyright (c) 2014, 2015 Soonho Kong. All rights reserved.

;; Author: Leonardo de Moura <leonardo@microsoft.com>
;;         Soonho Kong       <soonhok@cs.cmu.edu>
;;         Gabriel Ebner     <gebner@gebner.org>
;;         Sebastian Ullrich <sebasti@nullri.ch>
;; Maintainer: Sebastian Ullrich <sebasti@nullri.ch>
;; Created: Jan 09, 2014
;; Keywords: languages
;; Package-Requires: ((emacs "24.3") (dash "2.12.0") (dash-functional "1.2.0") (s "1.10.0") (f "0.19.0") (flycheck "30"))
;; URL: https://github.com/leanprover/lean4-mode

;; Released under Apache 2.0 license as described in the file LICENSE.

;;; Commentary:

;; Provides a major mode for the Lean programming language.

;; Provides highlighting, diagnostics, goal visualization,
;; and many other useful features for Lean users.

;; See the README.md for more advanced features and the
;; associated keybindings.

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'pcase)
(require 'flycheck)
(require 'lean4-eri)
(require 'lean4-util)
(require 'lean4-settings)
(require 'lean4-input)
(require 'lean4-syntax)
(require 'lean4-leanpkg)
;(require 'lean4-server)
(require 'lean4-flycheck)
;(require 'lean4-info)
;(require 'lean4-hole)
;(require 'lean4-type)
;(require 'lean4-message-boxes)
;(require 'lean4-right-click)
(require 'lean4-dev)

(defun lean4-compile-string (exe-name args file-name)
  "Concatenate EXE-NAME, ARGS, and FILE-NAME."
  (format "%s %s %s" exe-name args file-name))

(defun lean4-create-temp-in-system-tempdir (file-name prefix)
  "Create a temp lean file and return its name."
  (make-temp-file (or prefix "flymake") nil (f-ext file-name)))

(defun lean4-execute (&optional arg)
  "Execute Lean in the current buffer."
  (interactive)
  (when (called-interactively-p 'any)
    (setq arg (read-string "arg: " arg)))
  (let ((cc compile-command)
        (target-file-name
         (or
          (buffer-file-name)
          (flymake-init-create-temp-buffer-copy 'lean4-create-temp-in-system-tempdir))))
    (compile (lean4-compile-string
              (shell-quote-argument (f-full (lean4-get-executable lean4-executable-name)))
              (or arg "")
              (shell-quote-argument (f-full target-file-name))))
    ;; restore old value
    (setq compile-command cc)))

(defun lean4-std-exe ()
  (interactive)
  (lean4-execute))

(defun lean4-check-expansion ()
  (interactive)
  (save-excursion
    (if (looking-at (rx symbol-start "_")) t
      (if (looking-at "\\_>") t
        (backward-char 1)
        (if (looking-at "\\.") t
          (backward-char 1)
          (if (looking-at "->") t nil))))))

(defun lean4-tab-indent ()
  (interactive)
  (cond ((looking-back (rx line-start (* white)) nil)
         (lean4-eri-indent))
        (t (indent-for-tab-command))))

(defun lean4-set-keys ()
  (local-set-key lean4-keybinding-std-exe1                  #'lean4-std-exe)
  (local-set-key lean4-keybinding-std-exe2                  #'lean4-std-exe)
  (local-set-key lean4-keybinding-show-key                  #'quail-show-key)
  (local-set-key lean4-keybinding-find-definition           #'lean4-find-definition)
  (local-set-key lean4-keybinding-tab-indent                #'lean4-tab-indent)
  (local-set-key lean4-keybinding-hole                      #'lean4-hole)
  (local-set-key lean4-keybinding-lean4-toggle-show-goal     #'lean4-toggle-show-goal)
  (local-set-key lean4-keybinding-lean4-toggle-next-error    #'lean4-toggle-next-error)
  (local-set-key lean4-keybinding-lean4-message-boxes-toggle #'lean4-message-boxes-toggle)
  (local-set-key lean4-keybinding-leanpkg-configure         #'lean4-leanpkg-configure)
  (local-set-key lean4-keybinding-leanpkg-build             #'lean4-leanpkg-build)
  (local-set-key lean4-keybinding-leanpkg-test              #'lean4-leanpkg-test)
  ;; This only works as a mouse binding due to the event, so it is not abstracted
  ;; to avoid user confusion.
  (local-set-key (kbd "<mouse-3>")                         #'lean4-right-click-show-menu)
  )

(define-abbrev-table 'lean4-abbrev-table
  '())

(defvar lean4-mode-map (make-sparse-keymap)
  "Keymap used in Lean mode")

(defun lean4-mk-check-menu-option (text sym)
  `[,text (lean4-set-check-mode ',sym)
         :style radio :selected (eq lean4-server-check-mode ',sym)])

(easy-menu-define lean4-mode-menu lean4-mode-map
  "Menu for the Lean major mode"
  `("Lean 4"
    ["Execute lean"         lean4-execute                      t]
    ;; ["Create a new project" (call-interactively 'lean4-project-create) (not (lean4-project-inside-p))]
    "-----------------"
    ["Show type info"       lean4-show-type                    (and lean4-eldoc-use eldoc-mode)]
    ["Toggle goal display"  lean4-toggle-show-goal             t]
    ["Toggle next error display" lean4-toggle-next-error       t]
    ["Toggle message boxes" lean4-message-boxes-toggle         t]
    ["Highlight pending tasks"  lean4-server-toggle-show-pending-tasks
     :active t :style toggle :selected lean4-server-show-pending-tasks]
    ["Find definition at point" lean4-find-definition          t]
    "-----------------"
    ["List of errors"       flycheck-list-errors              flycheck-mode]
    "-----------------"
    ["Restart lean process" lean4-server-restart               t]
    "-----------------"
    ,(lean4-mk-check-menu-option "Check nothing" 'nothing)
    ,(lean4-mk-check-menu-option "Check visible lines" 'visible-lines)
    ,(lean4-mk-check-menu-option "Check visible lines and above" 'visible-lines-and-above)
    ,(lean4-mk-check-menu-option "Check visible files" 'visible-files)
    ,(lean4-mk-check-menu-option "Check open files" 'open-files)
    "-----------------"
    ("Configuration"
     ["Show type at point"
      lean4-toggle-eldoc-mode :active t :style toggle :selected eldoc-mode])
    "-----------------"
    ["Customize lean4-mode" (customize-group 'lean)            t]))

(defconst lean4-hooks-alist
  '(
    ;; server
    ;; (kill-buffer-hook                    . lean4-server-stop)
    ;; (after-change-functions              . lean4-server-change-hook)
    ;; (focus-in-hook                       . lean4-server-show-messages)
    ;; (window-scroll-functions             . lean4-server-window-scroll-function-hook)
    ;; Handle events that may start automatic syntax checks
    (before-save-hook                    . lean4-whitespace-cleanup)
    ;; info windows
    ;; (post-command-hook                   . lean4-show-goal--handler)
    (post-command-hook                   . lean4-next-error--handler)
    ;; (flycheck-after-syntax-check-hook    . lean4-show-goal--handler)
    (flycheck-after-syntax-check-hook    . lean4-next-error--handler)
    )
  "Hooks which lean4-mode needs to hook in.

The `car' of each pair is a hook variable, the `cdr' a function
to be added or removed from the hook variable if Flycheck mode is
enabled and disabled respectively.")

(defun lean4-mode-setup ()
  "Default lean4-mode setup"
  ;; server
  ;;(ignore-errors (lean4-server-ensure-alive))
  ;;(setq mode-name '("Lean" (:eval (lean4-server-status-string))))
  ;; Right click menu sources
  ;;(setq lean4-right-click-item-functions '(lean4-info-right-click-find-definition
  ;;                                        lean4-hole-right-click))
  ;; Flycheck
  (lean4-flycheck-turn-on)
  (setq-local flycheck-disabled-checkers '())
  ;; info buffers
  (lean4-ensure-info-buffer lean4-next-error-buffer-name)
  ;(lean4-ensure-info-buffer lean4-show-goal-buffer-name)
  ;; eldoc
  ;;(when lean4-eldoc-use
  ;;  (set (make-local-variable 'eldoc-documentation-function)
  ;;       'lean4-eldoc-documentation-function)
  ;;  (eldoc-mode t))
  )

;; Automode List
;;;###autoload
(define-derived-mode lean4-mode prog-mode "Lean 4"
  "Major mode for Lean
     \\{lean4-mode-map}
Invokes `lean4-mode-hook'.
"
  :syntax-table lean4-syntax-table
  :abbrev-table lean4-abbrev-table
  :group 'lean
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-start-skip) "[-/]-[ \t]*")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(-/\\|\\s>\\)")
  (set (make-local-variable 'comment-padding) 1)
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'font-lock-defaults) lean4-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set 'compilation-mode-font-lock-keywords '())
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (lean4-set-keys)
  (if (fboundp 'electric-indent-local-mode)
      (electric-indent-local-mode -1))
  ;; (abbrev-mode 1)
  (pcase-dolist (`(,hook . ,fn) lean4-hooks-alist)
    (add-hook hook fn nil 'local))
  (lean4-mode-setup))

;; Automatically use lean4-mode for .lean files.
;;;###autoload
(push '("\\.lean$" . lean4-mode) auto-mode-alist)
(push '("\\.hlean$" . lean4-mode) auto-mode-alist)

;; Use utf-8 encoding
;;;### autoload
(modify-coding-system-alist 'file "\\.lean\\'" 'utf-8)
(modify-coding-system-alist 'file "\\.hlean\\'" 'utf-8)

;; Flycheck init
(eval-after-load 'flycheck
  '(lean4-flycheck-init))

(provide 'lean4-mode)
;;; lean4-mode.el ends here
