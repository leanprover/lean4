;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Leonardo de Moura
;;         Soonho Kong
;;
(require 'cl-lib)
(require 'eri)
(require 'generic-x)
(require 'compile)
(require 'flymake)
(require 'dash)
(require 'dash-functional)
(require 'lean-variable)
(require 'lean-util)
(require 'lean-settings)
(require 'lean-flycheck)
(require 'lean-input)
(require 'lean-type)
(require 'lean-tags)
(require 'lean-syntax)

(defun lean-compile-string (exe-name args file-name)
  "Concatenate exe-name, args, and file-name"
  (format "%s %s %s" exe-name args file-name))

(defun lean-create-temp-in-system-tempdir (file-name prefix)
  "Create a temp lean file and return its name"
  (make-temp-file (or prefix "flymake") nil ".lean"))

(defun lean-execute (&optional arg)
  "Execute Lean in the current buffer"
  (interactive "sarg: ")
  (let ((target-file-name
         (or
          (buffer-file-name)
          (flymake-init-create-temp-buffer-copy 'lean-create-temp-in-system-tempdir))))
    (compile (lean-compile-string
              (lean-get-executable lean-executable-name)
              (or arg "")
              target-file-name))))

(defun lean-std-exe ()
  (interactive)
  (lean-execute))


(defun lean-check-expansion ()
  (save-excursion
    (if (looking-at "\\_>") t
      (backward-char 1)
      (if (looking-at "\\.") t
        (backward-char 1)
        (if (looking-at "->") t nil)))))

(defun lean-tab-indent-or-complete ()
  (interactive)
  (if (minibufferp)
      (minibuffer-complete)
    (if (lean-check-expansion)
        (cond (lean-company-use (company-complete-common))
              (t (completion-at-point-functions)))
      (eri-indent))))

(defun lean-tab ()
  (interactive)
  (or (company-complete)
      (eri-indent)))

(defun lean-set-keys ()
  (local-set-key "\C-c\C-x" 'lean-std-exe)
  (local-set-key "\C-c\C-l" 'lean-std-exe)
  (local-set-key "\C-c\C-o" 'lean-set-option)
  (local-set-key "\C-c\C-e" 'lean-eval-cmd)
  (local-set-key "\C-c\C-t" 'lean-eldoc-documentation-function)
  (local-set-key "\C-c\C-f" 'lean-fill-placeholder)
  (local-set-key "\M-."     'lean-find-tag)
  (local-set-key [tab]      'lean-tab-indent-or-complete))

(define-abbrev-table 'lean-abbrev-table
  '(("var"    "variable")
    ("vars"   "variables")
    ("def"    "definition")
    ("th"     "theorem")))

(defconst lean-hooks-alist
  '(
    ;; Handle events that may start automatic syntax checks
    ;; (after-save-hook                  . lean-handle-save)
    (after-change-functions              . lean-after-change-function)
    (before-change-functions             . lean-before-change-function)
    ;; ;; Handle events that may triggered pending deferred checks
    ;; (window-configuration-change-hook . lean-perform-deferred-syntax-check)
    ;; (post-command-hook                . lean-perform-deferred-syntax-check)
    ;; ;; Teardown Lean whenever the buffer state is about to get lost, to
    ;; ;; clean up temporary files and directories.
    ;; (kill-buffer-hook                 . lean-teardown)
    ;; (change-major-mode-hook           . lean-teardown)
    ;; (before-revert-hook               . lean-teardown)
    ;; ;; Update the error list if necessary
    ;; (post-command-hook                . lean-error-list-update-source)
    ;; (post-command-hook                . lean-error-list-highlight-errors)
    ;; ;; Show or hide error popups after commands
    ;; (post-command-hook                . lean-display-error-at-point-soon)
    ;; (post-command-hook                . lean-hide-error-buffer)
    ;; ;; Immediately show error popups when navigating to an error
    ;; (next-error-hook                  . lean-display-error-at-point))
    )
    "Hooks which lean-mode needs to hook in.

The `car' of each pair is a hook variable, the `cdr' a function
to be added or removed from the hook variable if Flycheck mode is
enabled and disabled respectively.")

(defun lean-mode-setup ()
  "Default lean-mode setup"
  ;; Flycheck
  (when lean-flycheck-use (lean-flycheck-turn-on))
  ;; Draw a vertical line for rule-column
  (when (and lean-rule-column
             lean-show-rule-column-method)
    (cl-case lean-show-rule-column-method
      ('vline (require 'fill-column-indicator)
              (setq fci-rule-column lean-rule-column)
              (setq fci-rule-color lean-rule-color)
              (fci-mode t))))
  ;; Delete Trailing Whitespace
  (if lean-delete-trailing-whitespace
      (progn (require 'whitespace-cleanup-mode)
             (whitespace-cleanup-mode t))
    (whitespace-cleanup-mode nil))
  ;; eldoc
  (when lean-eldoc-use
    (set (make-local-variable 'eldoc-documentation-function)
         'lean-eldoc-documentation-function)
    (eldoc-mode t)
    (lean-eldoc-documentation-function))
  ;; company-mode
  (when lean-company-use
    (require 'company)
    (company-mode t)
    (set (make-local-variable 'company-backends) '(company-etags))))

;; Automode List
;;;###autoload
(define-derived-mode lean-mode prog-mode "Lean"
  "Major mode for Lean"
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
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (lean-set-keys)
  (abbrev-mode 1)
  (pcase-dolist (`(,hook . ,fn) lean-hooks-alist)
    (add-hook hook fn nil 'local))
  (lean-mode-setup))

;;; Automatically update TAGS file without asking
(setq tags-revert-without-query t)

;; Automatically use lean-mode for .lean files.
;;;###autoload
(push '("\\.lean$" . lean-mode) auto-mode-alist)

;; Use utf-8 encoding
;;;### autoload
(modify-coding-system-alist 'file "\\.lean\\'" 'utf-8)

;; Flycheck init
(when lean-flycheck-use
  (require 'flycheck)
  (eval-after-load 'flycheck
    '(lean-flycheck-init)))

(provide 'lean-mode)
