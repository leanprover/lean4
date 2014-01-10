(require 'generic-x)
(require 'lean-input)
(require 'compile)

(defvar lean-exe "lean"
  "Path for the Lean executable")

(defun lean-execute ()
  "Execute Lean in the current buffer"
  (interactive)
  (compile (format "%s %s" lean-exe (buffer-file-name))))

(defun lean-set-keys ()
  (local-set-key "\C-c\C-x" 'lean-execute)
  (local-set-key "\C-c\C-l" 'lean-execute))

(define-abbrev-table 'lean-mode-abbrev-table '(
    ("var"    "variable")
    ("vars"   "variables")
    ("def"    "definition")
    ("th"     "theorem")
    ))

(define-generic-mode
    'lean-mode     ;; name of the mode to create
  '("--")          ;; comments start with
  '("import" "definition" "variable" "variables" "print" "theorem" "axiom" "universe" "alias" "help" "environment" "options" "infix" "infixl" "infixr" "notation" "eval" "check" "exit" "coercion" "end" "using" "namespace" "builtin" "scope" "pop_scope" "set_opaque" "set_option") ;; some keywords
  '(("\\<\\(Bool\\|Int\\|Nat\\|Real\\|Type\\|TypeU\\|ℕ\\|ℤ\\)\\>" . 'font-lock-type-face)
    ("\\<\\(calc\\|have\\|in\\|let\\|forall\\|exists\\|[λ→∃∀:]\\)\\>" . font-lock-keyword-face)
    ("\"[^\"]*\"" . 'font-lock-string-face)
    ("\\(->\\|/\\\\\\|==\\|\\\\/\\|[*+/<=>¬∧∨≠≤≥-]\\)" . 'font-lock-constant-face)
    ("\\(\\b.*_tac\\|Cond\\|OrElse\\|T\\(?:hen\\|ry\\)\\|When\\|apply\\|b\\(?:ack\\|eta\\)\\|done\\|exact\\)" . 'font-lock-constant-face)
    ("\\(universe\\|theorem\\|axiom\\|definition\\|variable\\|builtin\\)[ \t]*\\([^ \t\n]*\\)" (2 'font-lock-function-name-face))
    ("variables[ \t]\\([^:]*\\)" (1 'font-lock-function-name-face))
    ("\\(set_opaque\\|set_option\\)[ \t]*\\([^ \t\n]*\\)" (2 'font-lock-constant-face))
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
      ))
  "A mode for Lean files"          ;; doc string for this mode
  )

(provide 'lean-mode)

; (regexp-opt '("Int" "Bool" "Nat" "Type" "Real") t)
; (regexp-opt '("let" "in" "have" "calc" "forall" "exists") t)
; (regexp-opt '("=" "->" "≠" "∨" "∧" "¬" "/\\" "\\/" "+" "-" "*" "/" "<" ">" "≤" "≥" "==" "∀" "∃" "→" "λ" ":") t)
; (regexp-opt '("apply" "exact" "trivial" "absurd" "beta" "apply" "unfold" "done" "back" "Try" "Then" "OrElse" "OrElse" "Cond" "When" "unfold_all" ) t)
