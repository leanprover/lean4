(require 'generic-x)

(define-abbrev-table 'lean-mode-abbrev-table '(
    ;; math/unicode symbols
    ("forall" "∀")
    ("exists" "∃")
    ("fun"    "λ")
    ("imp"    "→")
    ("and"    "∧")
    ("or"     "∨")
    ("not"    "¬")
    ("neq"     "≠")
    ("geq"     "≥")
    ("leq"     "≤")
    ("Nat"    "ℕ")
    ("Int"    "ℤ")
    ))

(define-generic-mode
    'lean-mode     ;; name of the mode to create
  '("--")          ;; comments start with
  '("import" "definition" "variable" "variables" "print" "axiom" "theorem" "universe" "alias" "help" "set::option" "set::opaque" "environment" "options" "infix" "infixl" "infixr" "notation" "eval" "check" "exit" "coercion" "end" "using" "namespace" "builtin" "scope" "pop::scope") ;; some keywords
  '(("\\<\\(Bool\\|Int\\|Nat\\|Real\\|Type\\|TypeU\\|ℕ\\|ℤ\\)\\>" . 'font-lock-type-face)
    ("\\<\\(calc\\|have\\|in\\|let\\)\\>" . font-lock-keyword-face)
    ("\"[^\"]*\"" . 'font-lock-string-face)
    ("\\(->\\|/\\\\\\|==\\|\\\\/\\|[*+/:<=>¬λ→∀∃∧∨≠≤≥-]\\)" . 'font-lock-constant-face))
  '("\\.lean$")                    ;; files for which to activate this mode
  '((lambda()
      (setq local-abbrev-table lean-mode-abbrev-table)
      (abbrev-mode 1)))
  "A mode for Lean files"          ;; doc string for this mode
  )


; (regexp-opt '("Int" "Bool" "Nat" "Type" "Real") t)
; (regexp-opt '("let" "in" "have" "calc" "forall" "exists") t)
; (regexp-opt '("=" "->" "≠" "∨" "∧" "¬" "/\\" "\\/" "+" "-" "*" "/" "<" ">" "≤" "≥" "==" "∀" "∃" "→" "λ" ":") t)
