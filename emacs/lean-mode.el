(require 'generic-x)
(require 'lean-input)

(define-generic-mode
    'lean-mode     ;; name of the mode to create
  '("--")          ;; comments start with
  '("import" "definition" "variable" "variables" "print" "axiom" "theorem" "universe" "alias" "help" "set_option" "set_opaque" "environment" "options" "infix" "infixl" "infixr" "notation" "eval" "check" "exit" "coercion" "end" "using" "namespace" "builtin" "scope" "pop_scope") ;; some keywords
  '(("\\<\\(Bool\\|Int\\|Nat\\|Real\\|Type\\|TypeU\\|ℕ\\|ℤ\\)\\>" . 'font-lock-type-face)
    ("\\<\\(calc\\|have\\|in\\|let\\)\\>" . font-lock-keyword-face)
    ("\"[^\"]*\"" . 'font-lock-string-face)
    ("\\(->\\|/\\\\\\|==\\|\\\\/\\|[*+/:<=>¬λ→∀∃∧∨≠≤≥-]\\)" . 'font-lock-constant-face))
  '("\\.lean$")                    ;; files for which to activate this mode
  '((lambda()
      (set-input-method "Lean")
      (set (make-local-variable 'lisp-indent-function)
           'common-lisp-indent-function)
      ))
  "A mode for Lean files"          ;; doc string for this mode
  )

(provide 'lean-mode)

; (regexp-opt '("Int" "Bool" "Nat" "Type" "Real") t)
; (regexp-opt '("let" "in" "have" "calc" "forall" "exists") t)
; (regexp-opt '("=" "->" "≠" "∨" "∧" "¬" "/\\" "\\/" "+" "-" "*" "/" "<" ">" "≤" "≥" "==" "∀" "∃" "→" "λ" ":") t)
