;; -*- lexical-binding: t -*-
;;
;;; lean-mode.el --- Emacs mode for Lean theorem prover
;;
;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Copyright (c) 2014, 2015 Soonho Kong. All rights reserved.
;;
;; Author: Leonardo de Moura <leonardo@microsoft.com>
;;         Soonho Kong       <soonhok@cs.cmu.edu>
;; Maintainer: Soonho Kong   <soonhok@cs.cmu.edu>
;; Created: Jan 09, 2014
;; Keywords: languages
;; Version: 0.1
;; URL: https://github.com/leanprover/lean/blob/master/src/emacs
;;
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
(require 'cl-lib)
(require 'pcase)
(require 'lean-require)
(require 'eri)
(require 'lean-util)
(require 'lean-settings)
(require 'lean-input)
(require 'lean-syntax)
(require 'lean-project)
(require 'lean-company)
(require 'lean-server)
(require 'lean-flycheck)
(require 'lean-info)
(require 'lean-type)

(defun lean-compile-string (exe-name args file-name)
  "Concatenate exe-name, args, and file-name"
  (format "%s %s %s" exe-name args file-name))

(defun lean-create-temp-in-system-tempdir (file-name prefix)
  "Create a temp lean file and return its name"
  (make-temp-file (or prefix "flymake") nil (f-ext file-name)))

(defun lean-execute (&optional arg)
  "Execute Lean in the current buffer"
  (interactive)
  (when (called-interactively-p 'any)
    (setq arg (read-string "arg: " arg)))
  (let ((target-file-name
         (or
          (buffer-file-name)
          (flymake-init-create-temp-buffer-copy 'lean-create-temp-in-system-tempdir))))
    (compile (lean-compile-string
              (shell-quote-argument (f-full (lean-get-executable lean-executable-name)))
              (or arg "")
              (shell-quote-argument (f-full target-file-name))))))

(defun lean-show-goal-at-pos ()
  "Show goal at the current point."
  (interactive)
  (lean-server-sync)
  (lean-server-send-command
   (list :command "show_goal"
         :line (line-number-at-pos)
         :col (current-column))
   (cl-function
    (lambda (&key state) (with-output-to-lean-info (princ state))))
   (cl-function
    (lambda (&key message) (with-output-to-lean-info (princ message))))))

(defun lean-std-exe ()
  (interactive)
  (lean-execute))

(defun lean-check-expansion ()
  (interactive)
  (save-excursion
    (if (looking-at (rx symbol-start "_")) t
      (if (looking-at "\\_>") t
        (backward-char 1)
        (if (looking-at "\\.") t
          (backward-char 1)
          (if (looking-at "->") t nil))))))

(defun lean-tab-indent ()
  (cond ((looking-back (rx line-start (* white)) nil)
         (eri-indent))
        (t (indent-for-tab-command))))

(defun lean-tab-indent-or-complete ()
  (interactive)
  (if (minibufferp)
      (minibuffer-complete)
    (cond ((and lean-company-use (company-lean--check-prefix))
           (company-complete-common))
          (lean-company-use (lean-tab-indent))
          ((lean-check-expansion)
           (completion-at-point-functions))
          (t (lean-tab-indent)))))

(defun lean-set-keys ()
  (local-set-key lean-keybinding-std-exe1                  'lean-std-exe)
  (local-set-key lean-keybinding-std-exe2                  'lean-std-exe)
  (local-set-key lean-keybinding-show-key                  'quail-show-key)
  (local-set-key lean-keybinding-eval-cmd                  'lean-eval-cmd)
  (local-set-key lean-keybinding-server-restart            'lean-server-restart)
  (local-set-key lean-keybinding-find-definition           'lean-find-definition)
  (local-set-key lean-keybinding-tab-indent-or-complete    'lean-tab-indent-or-complete)
  (local-set-key lean-keybinding-lean-show-goal-at-pos     'lean-show-goal-at-pos)
  (local-set-key lean-keybinding-lean-show-id-keyword-info 'lean-show-id-keyword-info)
  (local-set-key lean-keybinding-lean-next-error-mode      'lean-next-error-mode)
  )

(defun lean-define-key-binding (key cmd)
  (local-set-key key `(lambda () (interactive) ,cmd)))

(define-abbrev-table 'lean-abbrev-table
  '())

(defvar lean-mode-map (make-sparse-keymap)
  "Keymap used in Lean mode")

(easy-menu-define lean-mode-menu lean-mode-map
  "Menu for the Lean major mode"
  `("Lean"
    ["Execute lean"         lean-execute                      t]
    ["Create a new project" (call-interactively 'lean-project-create) (not (lean-project-inside-p))]
    "-----------------"
    ["Show type info"       lean-show-type                    (and lean-eldoc-use eldoc-mode)]
    ["Show goal"            lean-show-goal-at-pos             t]
    ["Show id/keyword info" lean-show-id-keyword-info         t]
    ["Find definition at point" lean-find-definition          t]
    ["Global tag search"    lean-global-search                t]
    "-----------------"
    ["Run flycheck"         flycheck-compile                  (and lean-flycheck-use flycheck-mode)]
    ["List of errors"       flycheck-list-errors              (and lean-flycheck-use flycheck-mode)]
    "-----------------"
    ["Clear all cache"      lean-clear-cache                  t]
    ["Restart lean process" lean-server-restart               t]
    "-----------------"
    ("Configuration"
     ["Use flycheck (on-the-fly syntax check)"
      lean-toggle-flycheck-mode :active t :style toggle :selected flycheck-mode]
     ["Show type at point"
      lean-toggle-eldoc-mode :active t :style toggle :selected eldoc-mode]
     ["Show next error in dedicated buffer"
      lean-next-error-mode :active t :style toggle :selected lean-next-error-mode])
    "-----------------"
    ["Customize lean-mode" (customize-group 'lean)            t]))

(defconst lean-hooks-alist
  '(
    ;; Handle events that may start automatic syntax checks
    (before-save-hook                    . lean-whitespace-cleanup)
    ;; ;; Handle events that may triggered pending deferred checks
    ;; (window-configuration-change-hook . lean-perform-deferred-syntax-check)
    ;; (post-command-hook                . lean-perform-deferred-syntax-check)
    ;; ;; Teardown Lean whenever the buffer state is about to get lost, to
    ;; ;; clean up temporary files and directories.
    ;; (kill-buffer-hook                 . lean-teardown)
    ;; (change-major-mode-hook           . lean-teardown)
    ;; (before-revert-hook                  . lean-before-revert)
    ;; (after-revert-hook                   . lean-after-revert)
    ;; ;; Update the error list if necessary
    ;; (post-command-hook                . lean-error-list-update-source)
    ;; (post-command-hook                . lean-error-list-highlight-errors)
    ;; ;; Show or hide error popups after commands
    ;; (post-command-hook                . lean-display-error-at-point-soon)
    ;; (post-command-hook                . lean-hide-error-buffer)
    )
  "Hooks which lean-mode needs to hook in.

The `car' of each pair is a hook variable, the `cdr' a function
to be added or removed from the hook variable if Flycheck mode is
enabled and disabled respectively.")

(defun lean-mode-setup ()
  "Default lean-mode setup"
  (add-hook 'kill-buffer-hook 'lean-server-stop)
  ;; Flycheck
  (when lean-flycheck-use
    (lean-flycheck-turn-on)
    (setq-local flycheck-disabled-checkers '()))
  ;; company-mode
  (when lean-company-use
    (company-lean-hook))
  ;; eldoc
  (when lean-eldoc-use
    (set (make-local-variable 'eldoc-documentation-function)
         'lean-eldoc-documentation-function)
    (eldoc-mode t))
  ;; Draw a vertical line for rule-column
  (when (and lean-rule-column
             lean-show-rule-column-method)
    (cl-case lean-show-rule-column-method
      ('vline (require 'fill-column-indicator)
              (setq fci-rule-column lean-rule-column)
              (setq fci-rule-color lean-rule-color)
              (fci-mode t)))))

;; Automode List
;;;###autoload
(define-derived-mode lean-mode prog-mode "Lean"
  "Major mode for Lean
     \\{lean-mode-map}
Invokes `lean-mode-hook'.
"
  :syntax-table lean-syntax-table
  :abbrev-table lean-abbrev-table
  :group 'lean
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-start-skip) "[-/]-[ \t]*")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(-/\\|\\s>\\)")
  (set (make-local-variable 'comment-padding) 1)
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'font-lock-defaults) lean-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set 'compilation-mode-font-lock-keywords '())
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (lean-set-keys)
  (if (fboundp 'electric-indent-local-mode)
      (electric-indent-local-mode -1))
  ;; (abbrev-mode 1)
  (pcase-dolist (`(,hook . ,fn) lean-hooks-alist)
    (add-hook hook fn nil 'local))
  (lean-mode-setup))

;;; Automatically update TAGS file without asking
(setq tags-revert-without-query t)

;; Automatically use lean-mode for .lean files.
;;;###autoload
(push '("\\.lean$" . lean-mode) auto-mode-alist)
(push '("\\.hlean$" . lean-mode) auto-mode-alist)

;; Use utf-8 encoding
;;;### autoload
(modify-coding-system-alist 'file "\\.lean\\'" 'utf-8)
(modify-coding-system-alist 'file "\\.hlean\\'" 'utf-8)

;; Flycheck init
(when lean-flycheck-use
  (require 'flycheck)
  (eval-after-load 'flycheck
    '(lean-flycheck-init)))

(provide 'lean-mode)
;;; lean-mode.el ends here
