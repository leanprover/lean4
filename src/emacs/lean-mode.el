;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Leonardo de Moura
;;         Soonho Kong
;;
(require 'cl-lib)
(require 'generic-x)
(require 'compile)
(require 'flymake)
(require 'flycheck)
(require 'fill-column-indicator)
(require 'whitespace-cleanup-mode)
(require 'lean-util)
(require 'lean-settings)
(require 'lean-flycheck)
(require 'lean-input)

(defun lean-compile-string (exe-name args file-name)
  "Concatenate exe-name, args, and file-name"
  (format "%s %s %s" exe-name args file-name))

(defun lean-create-temp-in-system-tempdir (filename prefix)
  "Create a temp lean file and return its name"
  (make-temp-file (or prefix "flymake") nil ".lean"))

(defun lean-execute (&optional arg)
  "Execute Lean in the current buffer"
  (interactive "sarg: ")
  (let ((target-file-name
         (lean-get-this-if-true-or-that
          (buffer-file-name)
          (flymake-init-create-temp-buffer-copy 'lean-create-temp-in-system-tempdir))))
    (compile (lean-compile-string
              (lean-get-executable lean-executable-name)
              (lean-get-this-if-true-or-that arg "")
              target-file-name))))

(defun lean-std-exe ()
  (interactive)
  (lean-execute))

(defun lean-hott-exe ()
  (interactive)
  (lean-execute "--hott"))

(defun lean-set-keys ()
  (local-set-key "\C-c\C-x" 'lean-std-exe)
  (local-set-key "\C-c\C-l" 'lean-std-exe)
  (local-set-key "\C-c\C-k" 'lean-hott-exe))

(define-abbrev-table 'lean-mode-abbrev-table '(
    ("var"    "variable")
    ("vars"   "variables")
    ("def"    "definition")
    ("th"     "theorem")
    ))

(define-generic-mode
    'lean-mode     ;; name of the mode to create
  '("--")          ;; comments start with
  '("import" "abbreviation" "opaque_hint" "tactic_hint" "definition" "renaming" "inline" "hiding" "exposing" "parameter" "parameters" "proof" "qed" "conjecture" "hypothesis" "lemma" "corollary" "variable" "variables" "print" "theorem" "axiom" "inductive" "with" "structure" "universe" "alias" "help" "environment" "options" "precedence" "postfix" "prefix" "calc_trans" "calc_subst" "calc_refl" "infix" "infixl" "infixr" "notation" "eval" "check" "exit" "coercion" "end" "private" "using" "namespace" "builtin" "including" "instance" "section" "set_option" "add_rewrite" "extends") ;; some keywords
  '(("\\_<\\(bool\\|int\\|nat\\|real\\|Prop\\|Type\\|ℕ\\|ℤ\\)\\_>" . 'font-lock-type-face)
    ("\\_<\\(calc\\|have\\|obtains\\|show\\|by\\|in\\|let\\|forall\\|fun\\|exists\\|if\\|then\\|else\\|assume\\|take\\|obtain\\|from\\)\\_>" . font-lock-keyword-face)
    ("\"[^\"]*\"" . 'font-lock-string-face)
    ("\\(->\\|↔\\|/\\\\\\|==\\|\\\\/\\|[*+/<=>¬∧∨≠≤≥-]\\)" . 'font-lock-constant-face)
    ("\\(λ\\|→\\|∃\\|∀\\|:\\|:=\\)" . font-lock-constant-face)
    ("\\_<\\(\\b.*_tac\\|Cond\\|or_else\\|t\\(?:hen\\|ry\\)\\|when\\|assumption\\|apply\\|b\\(?:ack\\|eta\\)\\|done\\|exact\\)\\_>" . 'font-lock-constant-face)
    ("\\_<\\(universe\\|inductive\\|theorem\\|axiom\\|lemma\\|hypothesis\\|abbreviation\\|definition\\|variable\\|parameter\\)\\_>[ \t\{\[]*\\([^ \t\n]*\\)" (2 'font-lock-function-name-face))
    ("\\_<\\(variables\\|parameters\\)\\_>[ \t\(\{\[]*\\([^:]*\\)" (2 'font-lock-function-name-face))
    ("\\(set_opaque\\|set_option\\)[ \t]*\\([^ \t\n]*\\)" (2 'font-lock-constant-face))
    ("\\_<_\\_>" . 'font-lock-preprocessor-face)
    ("\\_<sorry\\_>" . 'font-lock-warning-face)
    ;;
    )
  '("\\.lean$")                    ;; files for which to activate this mode
  '((lambda()
      (set-input-method "Lean")
      (set (make-local-variable 'lisp-indent-function)
           'common-lisp-indent-function)
      (lean-set-keys)
      (setq local-abbrev-table lean-mode-abbrev-table)
      (abbrev-mode 1)
      (when (and lean-rule-column
                 lean-show-rule-column-method)
        (cl-case lean-show-rule-column-method
          ('vline (setq fci-rule-column lean-rule-column)
                  (add-hook 'lean-mode-hook 'fci-mode))))
      (if lean-delete-trailing-whitespace
          (add-hook 'lean-mode-hook 'whitespace-cleanup-mode)
        (remove-hook 'lean-mode-hook 'whitespace-cleanup-mode))
      ))
  "A mode for Lean files"          ;; doc string for this mode
  )
(provide 'lean-mode)
; (regexp-opt '("Int" "Bool" "Nat" "Type" "Real") t)
; (regexp-opt '("let" "in" "have" "calc" "forall" "exists") t)
; (regexp-opt '("=" "->" "≠" "∨" "∧" "¬" "/\\" "\\/" "+" "-" "*" "/" "<" ">" "≤" "≥" "==" "∀" "∃" "→" "λ" ":") t)
; (regexp-opt '("apply" "exact" "trivial" "absurd" "beta" "apply" "unfold" "done" "back" "Try" "Then" "OrElse" "OrElse" "Cond" "When" "unfold_all" ) t)
