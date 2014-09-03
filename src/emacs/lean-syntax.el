;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Leonardo de Moura
;;         Soonho Kong
;;

(require 'rx)

(defconst lean-keywords
  '("import" "abbreviation" "opaque_hint" "tactic_hint" "definition" "renaming"
    "inline" "hiding" "exposing" "parameter" "parameters" "begin" "proof" "qed" "conjecture"
    "hypothesis" "lemma" "corollary" "variable" "variables" "print" "theorem"
    "axiom" "inductive" "with" "structure" "universe" "alias" "help" "environment"
    "options" "precedence" "postfix" "prefix" "calc_trans" "calc_subst" "calc_refl"
    "infix" "infixl" "infixr" "notation" "eval" "check" "exit" "coercion" "end"
    "private" "using" "namespace" "builtin" "including" "instance" "class" "section"
    "set_option" "add_rewrite" "extends")
  "lean keywords")

(defconst lean-syntax-table
  (let ((st (make-syntax-table)))
    ;; Matching parens
    (modify-syntax-entry ?\[ "(]" st)
    (modify-syntax-entry ?\] ")[" st)
    (modify-syntax-entry ?\{ "(}" st)
    (modify-syntax-entry ?\} "){" st)

    ;; comment
    (modify-syntax-entry ?/ "_ 14nb" st)
    (modify-syntax-entry ?- "_ 123" st)
    (modify-syntax-entry ?\n ">" st)

    ;; ' and _ can be names
    (modify-syntax-entry ?' "w" st)
    (modify-syntax-entry ?_ "w" st)

    ;; Lean operator chars
    (mapc #'(lambda (ch) (modify-syntax-entry ch "_" st))
          "!#$%&*+.<=>@^|~:")

    ;; Whitespace is whitespace
    (modify-syntax-entry ?\  " " st)
    (modify-syntax-entry ?\t " " st)

    ;; Strings
    (modify-syntax-entry ?\" "\"" st)
    (modify-syntax-entry ?\\ "/" st)
    st))

(defconst lean-font-lock-defaults
  `((;; Types
     (,(rx symbol-start (or "bool" "int" "nat" "real" "Prop" "Type" "ℕ" "ℤ") symbol-end) . 'font-lock-type-face)
     ;; Keywords
     (,(rx symbol-start (or "calc" "have" "obtains" "show" "by" "in" "let" "forall" "fun"
                            "exists" "if" "then" "else" "assume" "take" "obtain" "from") symbol-end)
      . font-lock-keyword-face)
     ;; String
     ("\"[^\"]*\"" . 'font-lock-string-face)
     ;; Constants
     (,(rx (or "#" "@" "->" "∼" "↔" "/" "==" "=" ":=" "<->" "/\\" "\\/" "∧" "∨" "≠" "<" ">" "≤" "≥" "¬" "<=" ">=" "⁻¹" "⬝" "▸" "+" "*" "-" "/")) . 'font-lock-constant-face)
     (,(rx (or "λ" "→" "∃" "∀" ":=")) . 'font-lock-constant-face )
     (,(rx symbol-start
           (or "\\b.*_tac" "Cond" "or_else" "then" "try" "when" "assumption" "apply" "back" "beta" "done" "exact")
           symbol-end)
      . 'font-lock-constant-face)
     ;; universe/inductive/theorem... "names"
     (,(rx symbol-start
           (group (or "universe" "inductive" "theorem" "axiom" "lemma" "hypothesis"
                      "abbreviation" "definition" "variable" "parameter"))
           symbol-end
           (zero-or-more (or whitespace "(" "{" "["))
           (group (zero-or-more (not whitespace))))
      (2 'font-lock-function-name-face))
     ("\\(set_option\\)[ \t]*\\([^ \t\n]*\\)" (2 'font-lock-constant-face))
     ;; place holder
     (,(rx symbol-start "_" symbol-end) . 'font-lock-preprocessor-face)
     ;; modifiers
     (,(rx (or "\[protected\]" "\[private\]" "\[instance\]" "\[coercion\]" "\[inline\]")) . 'font-lock-doc-face)
     ;; sorry
     (,(rx symbol-start "sorry" symbol-end) . 'font-lock-warning-face)
     ;; ? query
     (,(rx "?") . 'font-lock-warning-face)
     ;; lean-keywords
     (, (concat "\\(" (regexp-opt lean-keywords 'words) "\\)")
        (1 'font-lock-keyword-face)))))
(provide 'lean-syntax)
