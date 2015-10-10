;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Leonardo de Moura
;;         Soonho Kong
;;

(require 'rx)

(defconst lean-keywords1
  '("import" "prelude" "tactic_hint" "protected" "private" "noncomputable" "definition" "renaming"
    "hiding" "exposing" "parameter" "parameters" "begin" "begin+" "proof" "qed" "conjecture" "constant" "constants"
    "hypothesis" "lemma" "corollary" "variable" "variables" "premise" "premises" "theory"
    "print" "theorem" "proposition" "example" "abbreviation" "abstract"
    "open" "as" "export" "override" "axiom" "axioms" "inductive" "with" "structure" "record" "universe" "universes"
    "alias" "help" "environment" "options" "precedence" "reserve"
    "match" "infix" "infixl" "infixr" "notation" "postfix" "prefix"
    "tactic_infix" "tactic_infixl" "tactic_infixr" "tactic_notation" "tactic_postfix" "tactic_prefix"
    "eval" "check" "end" "reveal" "this" "suppose"
    "using" "namespace" "section" "fields" "find_decl"
    "attribute" "local" "set_option" "extends" "include" "omit" "classes"
    "instances" "coercions" "metaclasses" "raw" "migrate" "replacing"
    "calc" "have" "show" "suffices" "by" "in" "at" "let" "forall" "Pi" "fun"
    "exists" "if" "dif" "then" "else" "assume" "assert" "take"
    "obtain" "from")
  "lean keywords ending with 'word' (not symbol)")
(defconst lean-keywords1-regexp
  (eval `(rx word-start (or ,@lean-keywords1) word-end)))
(defconst lean-keywords2
  '("by+")
  "lean keywords ending with 'symbol'")
(defconst lean-keywords2-regexp
  (eval `(rx word-start (or ,@lean-keywords2) symbol-end)))
(defconst lean-constants
  '("#" "@" "->" "∼" "↔" "/" "==" "=" ":=" "<->" "/\\" "\\/" "∧" "∨"
    "≠" "<" ">" "≤" "≥" "¬" "<=" ">=" "⁻¹" "⬝" "▸" "+" "*" "-" "/" "λ"
    "→" "∃" "∀")
  "lean constants")
(defconst lean-constants-regexp (regexp-opt lean-constants))
(defconst lean-modifiers
  (--map (s-concat "[" it "]")
         '("persistent" "notation" "visible" "instance" "trans_instance"
           "class" "parsing_only" "coercion" "unfold_full" "constructor"
           "reducible" "irreducible" "semireducible" "quasireducible" "wf"
           "whnf" "multiple_instances" "none" "decls" "declarations"
           "coercions" "classes" "symm" "subst" "refl" "trans" "simp" "congr"
           "notations" "abbreviations" "begin_end_hints" "tactic_hints"
           "reduce_hints" "unfold_hints" "aliases" "eqv"
           "localrefinfo"))
  "lean modifiers")
(defconst lean-modifiers-regexp
  (regexp-opt lean-modifiers))
(defconst lean-warnings '("sorry" "exit") "lean warnings")
(defconst lean-warnings-regexp (eval `(rx word-start (or ,@lean-warnings) word-end)))

(defconst lean-syntax-table
  (let ((st (make-syntax-table)))
    ;; Matching parens
    (modify-syntax-entry ?\[ "(]" st)
    (modify-syntax-entry ?\] ")[" st)
    (modify-syntax-entry ?\{ "(}" st)
    (modify-syntax-entry ?\} "){" st)

    ;; comment
    (modify-syntax-entry ?/ ". 14nb" st)
    (modify-syntax-entry ?- ". 123" st)
    (modify-syntax-entry ?\n ">" st)

    ;; Word constituent
    (--map (modify-syntax-entry it "w" st)
           (list ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k ?l ?m
                 ?n ?o ?p ?q ?r ?s ?t ?u ?v ?w ?x ?y ?z
                 ?A ?B ?C ?D ?E ?F ?G ?H ?I ?J ?K ?L ?M
                 ?N ?O ?P ?Q ?R ?S ?T ?U ?V ?W ?X ?Y ?Z))
    (--map (modify-syntax-entry it "w" st)
           (list ?0 ?1 ?2 ?3 ?4 ?5 ?6 ?7 ?8 ?9))
    (--map (modify-syntax-entry it "w" st)
           (list ?α ?β ?γ ?δ ?ε ?ζ ?η ?θ ?ι ?κ ;;?λ
                 ?μ ?ν ?ξ ?ο ?π ?ρ ?ς ?σ ?τ ?υ
                 ?φ ?χ ?ψ ?ω))
    (--map (modify-syntax-entry it "w" st)
           (list ?ϊ ?ϋ ?ό ?ύ ?ώ ?Ϗ ?ϐ ?ϑ ?ϒ ?ϓ ?ϔ ?ϕ ?ϖ
                 ?ϗ ?Ϙ ?ϙ ?Ϛ ?ϛ ?Ϝ ?ϝ ?Ϟ ?ϟ ?Ϡ ?ϡ ?Ϣ ?ϣ
                 ?Ϥ ?ϥ ?Ϧ ?ϧ ?Ϩ ?ϩ ?Ϫ ?ϫ ?Ϭ ?ϭ ?Ϯ ?ϯ ?ϰ
                 ?ϱ ?ϲ ?ϳ ?ϴ ?ϵ ?϶ ?Ϸ ?ϸ ?Ϲ ?Ϻ ?ϻ))
    (--map (modify-syntax-entry it "w" st)
           (list ?ἀ ?ἁ ?ἂ ?ἃ ?ἄ ?ἅ ?ἆ ?ἇ ?Ἀ ?Ἁ ?Ἂ ?Ἃ ?Ἄ
                 ?Ἅ ?Ἆ ?Ἇ ?ἐ ?ἑ ?ἒ ?ἓ ?ἔ ?ἕ ?἖ ?἗ ?Ἐ ?Ἑ
                 ?Ἒ ?Ἓ ?Ἔ ?Ἕ ?἞ ?἟ ?ἠ ?ἡ ?ἢ ?ἣ ?ἤ ?ἥ
                 ?ἦ ?ἧ ?Ἠ ?Ἡ ?Ἢ ?Ἣ ?Ἤ ?Ἥ ?Ἦ ?Ἧ ?ἰ ?ἱ
                 ?ἲ ?ἳ ?ἴ ?ἵ ?ἶ ?ἷ ?Ἰ ?Ἱ ?Ἲ ?Ἳ ?Ἴ ?Ἵ ?Ἶ ?Ἷ
                 ?ὀ ?ὁ ?ὂ ?ὃ ?ὄ ?ὅ ?὆ ?὇ ?Ὀ ?Ὁ ?Ὂ ?Ὃ
                 ?Ὄ ?Ὅ ?὎ ?὏ ?ὐ ?ὑ ?ὒ ?ὓ ?ὔ ?ὕ ?ὖ ?ὗ
                 ?὘ ?Ὑ ?὚ ?Ὓ ?὜ ?Ὕ ?὞ ?Ὗ ?ὠ ?ὡ ?ὢ
                 ?ὣ ?ὤ ?ὥ ?ὦ ?ὧ ?Ὠ ?Ὡ ?Ὢ ?Ὣ ?Ὤ ?Ὥ ?Ὦ
                 ?Ὧ ?ὰ ?ά ?ὲ ?έ ?ὴ ?ή ?ὶ ?ί ?ὸ ?ό ?ὺ ?ύ ?ὼ
                 ?ώ ?὾ ?὿ ?ᾀ ?ᾁ ?ᾂ ?ᾃ ?ᾄ ?ᾅ ?ᾆ ?ᾇ ?ᾈ
                 ?ᾉ ?ᾊ ?ᾋ ?ᾌ ?ᾍ ?ᾎ ?ᾏ ?ᾐ ?ᾑ ?ᾒ ?ᾓ ?ᾔ
                 ?ᾕ ?ᾖ ?ᾗ ?ᾘ ?ᾙ ?ᾚ ?ᾛ ?ᾜ ?ᾝ ?ᾞ ?ᾟ ?ᾠ ?ᾡ ?ᾢ
                 ?ᾣ ?ᾤ ?ᾥ ?ᾦ ?ᾧ ?ᾨ ?ᾩ ?ᾪ ?ᾫ ?ᾬ ?ᾭ ?ᾮ ?ᾯ ?ᾰ
                 ?ᾱ ?ᾲ ?ᾳ ?ᾴ ?᾵ ?ᾶ ?ᾷ ?Ᾰ ?Ᾱ ?Ὰ ?Ά ?ᾼ ?᾽
                 ?ι ?᾿ ?῀ ?῁ ?ῂ ?ῃ ?ῄ ?῅ ?ῆ ?ῇ ?Ὲ ?Έ ?Ὴ
                 ?Ή ?ῌ ?῍ ?῎ ?῏ ?ῐ ?ῑ ?ῒ ?ΐ ?῔ ?῕ ?ῖ ?ῗ
                 ?Ῐ ?Ῑ ?Ὶ ?Ί ?῜ ?῝ ?῞ ?῟ ?ῠ ?ῡ ?ῢ ?ΰ ?ῤ ?ῥ
                 ?ῦ ?ῧ ?Ῠ ?Ῡ ?Ὺ ?Ύ ?Ῥ ?῭ ?΅ ?` ?῰ ?῱ ?ῲ ?ῳ
                 ?ῴ ?῵ ?ῶ ?ῷ ?Ὸ ?Ό ?Ὼ ?Ώ ?ῼ ?´ ?῾))
    (--map (modify-syntax-entry it "w" st)
           (list ?℀ ?℁ ?ℂ ?℃ ?℄ ?℅ ?℆ ?ℇ ?℈ ?℉ ?ℊ ?ℋ ?ℌ ?ℍ ?ℎ
                 ?ℏ ?ℐ ?ℑ ?ℒ ?ℓ ?℔ ?ℕ ?№ ?℗ ?℘ ?ℙ ?ℚ ?ℛ ?ℜ ?ℝ
                 ?℞ ?℟ ?℠ ?℡ ?™ ?℣ ?ℤ ?℥ ?Ω ?℧ ?ℨ ?℩ ?K ?Å ?ℬ
                 ?ℭ ?℮ ?ℯ ?ℰ ?ℱ ?Ⅎ ?ℳ ?ℴ ?ℵ ?ℶ ?ℷ ?ℸ ?ℹ ?℺ ?℻
                 ?ℼ ?ℽ ?ℾ ?ℿ ?⅀ ?⅁ ?⅂ ?⅃ ?⅄ ?ⅅ ?ⅆ ?ⅇ ?ⅈ ?ⅉ ?⅊
                 ?⅋ ?⅌ ?⅍ ?ⅎ ?⅏))
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
  `((;; modifiers
     (,lean-modifiers-regexp . 'font-lock-doc-face)
     ;; Keywords
     ("\\(set_option\\)[ \t]*\\([^ \t\n]*\\)" (2 'font-lock-constant-face))
     (,lean-keywords2-regexp . 'font-lock-keyword-face)
     (,lean-keywords1-regexp . 'font-lock-keyword-face)
     ;; String
     ("\"[^\"]*\"" . 'font-lock-string-face)
     ;; ;; Constants
     (,lean-constants-regexp . 'font-lock-constant-face)
     ;; universe/inductive/theorem... "names"
     (,(rx word-start
           (group (or "inductive" "structure" "record" "theorem" "axiom" "axioms" "lemma" "proposition" "corollary" "hypothesis" "definition" "constant" "abbreviation"))
           word-end
           (zero-or-more (or whitespace "(" "{" "["))
           (group (zero-or-more (not (any " \t\n\r{([")))))
      (2 'font-lock-function-name-face))
     ;; place holder
     (,(rx symbol-start "_" symbol-end) . 'font-lock-preprocessor-face)
     (,(rx "\[priority" (zero-or-more (not (any "\]"))) "\]") . font-lock-doc-face)
     (,(rx "\[recursor" (zero-or-more (not (any "\]"))) "\]") . font-lock-doc-face)
     (,(rx "\[unfold" (zero-or-more (not (any "\]"))) "\]") . font-lock-doc-face)
     ;; tactics
     ("cases[ \t\n]+[^ \t\n]+[ \t\n]+\\(with\\)" (1 'font-lock-constant-face))
     (,(rx (not (any "\.")) word-start
           (group
            (or "\\b.*_tac" "Cond" "or_else" "then" "try" "when" "assumption" "eassumption" "rapply"
                "apply" "fapply" "eapply" "rename" "intro" "intros" "all_goals" "fold" "focus" "focus_at"
                "generalize" "generalizes" "clear" "clears" "revert" "reverts" "back" "beta" "done" "exact" "rexact"
                "refine" "repeat" "whnf" "rotate" "rotate_left" "rotate_right" "inversion" "cases" "rewrite"
                "xrewrite" "krewrite" "blast" "simp" "esimp" "unfold" "change" "check_expr" "contradiction"
                "exfalso" "split" "existsi" "constructor" "fconstructor" "left" "right" "injection" "congruence" "reflexivity"
                "symmetry" "transitivity" "state" "induction" "induction_using" "fail" "append"
                "substvars" "now" "with_options"))
           word-end)
      (1 'font-lock-constant-face))
     ;; Types
     (,(rx word-start (or "Prop" "Type" "Type'" "Type₊" "Type₀" "Type₁" "Type₂" "Type₃") symbol-end) . 'font-lock-type-face)
     (,(rx word-start (group "Type") ".") (1 'font-lock-type-face))
     ;; warnings
     (,lean-warnings-regexp . 'font-lock-warning-face)
     ;; extra-keywords
     (,(rx (or "∎")) . 'font-lock-keyword-face)
     )))

;; Syntax Highlighting for Lean Info Mode
(defconst lean-info-font-lock-defaults
  (let ((new-entries
         `(;; Please add more after this:
           (,(rx (group (+ symbol-start (+ (or word (char ?₁ ?₂ ?₃ ?₄ ?₅ ?₆ ?₇ ?₈ ?₉ ?₀))) symbol-end (* white))) ":")
            (1 'font-lock-variable-name-face))
           (,(rx white ":" white)
            . 'font-lock-keyword-face)
           (,(rx "⊢" white)
            . 'font-lock-keyword-face)
           (,(rx "[" (group "stale") "]")
            (1 'font-lock-warning-face))
           (,(rx line-start "No Goal" line-end)
            . 'font-lock-constant-face)))
        (inherited-entries (car lean-font-lock-defaults)))
    `(,(-concat new-entries inherited-entries))))

(provide 'lean-syntax)
