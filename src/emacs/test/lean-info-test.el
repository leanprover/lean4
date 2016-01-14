;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'ert)
(require 's)
(require 'lean-info)

(ert-deftest lean-test-info-type ()
  "Test lean-info-type"
  (should (lean-info-type-p 'TYPE))
  (should (lean-info-type-p "-- TYPE|121|2"))
  (should (lean-info-type-p '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
  (should (equal (lean-info-type-parse-header "-- TYPE|121|2")
                 '(121 2)))
  (should (equal (lean-info-type-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))"))
                 '(TYPE
                   (121 2)
                   ("not (eq zero (succ m'))"
                    "→ decidable (eq zero (succ m'))"))))
  (should (equal
           (lean-info-type-pos
            (lean-info-type-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
           '(121 2))))

(ert-deftest lean-test-info-overload ()
  "Test lean-info-overload"
  (should (lean-info-overload-p 'OVERLOAD))
  (should (lean-info-overload-p "-- OVERLOAD|121|2"))
  (should (lean-info-overload-p '("-- OVERLOAD|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
  (should (equal (lean-info-overload-parse-header "-- OVERLOAD|121|2")
                 '(121 2)))
  (should
   (equal
    (lean-info-overload-parse
     '("-- OVERLOAD|121|2"
       "not (eq zero (succ m'))"
       "→ decidable (eq zero (succ m'))"
       "--"
       "not (eq one (succ m'))"
       "→ decidable (eq zero (succ m'))"
       "--"
       "not (eq two (succ m'))"
       "→ decidable (eq zero (succ m'))"))
    '(OVERLOAD (121 2)
               (("not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")
                ("not (eq one (succ m'))" "→ decidable (eq zero (succ m'))")
                ("not (eq two (succ m'))" "→ decidable (eq zero (succ m'))")))))
  (should (equal
           (lean-info-overload-pos
            (lean-info-overload-parse
             '("-- OVERLOAD|121|2"
               "not (eq zero (succ m'))"
               "→ decidable (eq zero (succ m'))"
               "--"
               "not (eq one (succ m'))"
               "→ decidable (eq zero (succ m'))"
               "--"
               "not (eq two (succ m'))"
               "→ decidable (eq zero (succ m'))")))
           '(121 2)))
  (should (equal (lean-info-overload-names (lean-info-overload-parse
                                            '("-- OVERLOAD|121|2"
                                              "not (eq zero (succ m'))"
                                              "→ decidable (eq zero (succ m'))"
                                              "--"
                                              "not (eq one (succ m'))"
                                              "→ decidable (eq zero (succ m'))"
                                              "--"
                                              "not (eq two (succ m'))"
                                              "→ decidable (eq zero (succ m'))")))
                 '("not (eq zero (succ m'))\n→ decidable (eq zero (succ m'))"
                   "not (eq one (succ m'))\n→ decidable (eq zero (succ m'))"
                   "not (eq two (succ m'))\n→ decidable (eq zero (succ m'))"))))


(ert-deftest lean-test-info-synth ()
  "Test lean-info-synth"
  ;; -- Test
  (should (lean-info-synth-p 'SYNTH))
  (should (lean-info-synth-p "-- SYNTH|121|2"))
  (should (lean-info-synth-p '("-- SYNTH|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
  (should (equal (lean-info-synth-parse-header "-- SYNTH|121|2")
                 '(121 2)))
  (should (equal (lean-info-synth-parse '("-- SYNTH|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))"))
                 '(SYNTH
                   (121 2)
                   ("not (eq zero (succ m'))"
                    "→ decidable (eq zero (succ m'))"))))
  (should (equal
           (lean-info-synth-pos
            (lean-info-synth-parse '("-- SYNTH|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
           '(121 2))))

(ert-deftest lean-test-info-coercion ()
  "Test lean-info-coercion"
  ;; -- Test
  (should (lean-info-coercion-p 'COERCION))
  (should (lean-info-coercion-p "-- COERCION|121|2"))
  (should (lean-info-coercion-p '("-- COERCION|417|15"
                                  "of_nat m"
                                  "--"
                                  "int")))
  (should (equal (lean-info-coercion-parse-header "-- COERCION|121|2")
                 '(121 2)))
  (should (equal (lean-info-coercion-parse '("-- COERCION|417|15"
                                             "of_nat"
                                             "--"
                                             "int"))
                 '(COERCION
                   (417 15)
                   ("of_nat")
                   ("int"))))
  (should (equal
           (lean-info-coercion-pos
            (lean-info-coercion-parse '("-- COERCION|417|15"
                                        "of_nat")))
           '(417 15))))

(ert-deftest lean-test-info-extra ()
  "Test lean-info-extra"
  ;; -- Test
  (should (lean-info-extra-p 'EXTRA))
  (should (lean-info-extra-p "-- EXTRA_TYPE|121|2"))
  (should (lean-info-extra-p '("-- EXTRA_TYPE|417|15"
                               "rec_on b ff tt"
                               "--"
                               "bool")))
  (should (equal (lean-info-extra-parse-header "-- EXTRA_TYPE|121|2")
                 '(121 2)))
  (should (equal (lean-info-extra-parse '("-- EXTRA_TYPE|417|15"
                                          "rec_on b ff tt"
                                          "--"
                                          "bool"))
                 '(EXTRA
                   (417 15)
                   ("rec_on b ff tt")
                   ("bool"))))
  (should (equal
           (lean-info-extra-pos
            (lean-info-extra-parse '("-- EXTRA_TYPE|417|15"
                                     "of_nat")))
           '(417 15))))

(ert-deftest lean-test-info-identifier ()
  "Test lean-info-identifier"
  ;; -- Test
  (should (lean-info-identifier-p 'IDENTIFIER))
  (should (lean-info-identifier-p "-- IDENTIFIER|121|2"))
  (should (lean-info-identifier-p '("-- IDENTIFIER|121|2" "foo.f")))
  (should (equal (lean-info-identifier-parse-header "-- IDENTIFIER|121|2")
                 '(121 2)))
  (should (equal (lean-info-identifier-parse '("-- IDENTIFIER|121|2" "foo.f"))
                 '(IDENTIFIER
                   (121 2)
                   ("foo.f"))))
  (should (equal
           (lean-info-identifier-pos
            (lean-info-identifier-parse '("-- IDENTIFIER|121|2" "foo.f")))
           '(121 2))))

(ert-deftest lean-test-info-symbol ()
  "Test lean-info-symbol"
  ;; -- Test
  (should (lean-info-symbol-p 'SYMBOL))
  (should (lean-info-symbol-p "-- SYMBOL|121|2"))
  (should (lean-info-symbol-p (lean-info-symbol-parse '("-- SYMBOL|121|2" "→"))))
  (should (equal (lean-info-symbol-parse-header "-- SYMBOL|121|2")
                 '(121 2)))
  (should (lean-info-symbol-p '("-- SYMBOL|121|2" "→")))
  (should (equal (lean-info-symbol-parse '("-- SYMBOL|121|2" "→"))
                 '(SYMBOL
                   (121 2)
                   ("→"))))
  (should (equal
           (lean-info-symbol-pos
            (lean-info-symbol-parse '("-- SYMBOL|121|2" "→")))
           '(121 2))))

(ert-deftest lean-test-info-proofstate ()
  "Test lean-info-proofstate"
  (should (lean-info-proofstate-p 'PROOF_STATE))
  (should (lean-info-proofstate-p "-- PROOF_STATE|121|2"))
  (should (lean-info-proofstate-p '("-- PROOF_STATE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
  (should (equal (lean-info-proofstate-parse-header "-- PROOF_STATE|121|2")
                 '(121 2)))
  (should
   (equal
    (lean-info-proofstate-parse
     '("-- PROOF_STATE|6|17"
       "a : Prop,"
       "b : Prop,"
       "c : Prop,"
       "H_1 : a,"
       "H_2 : b,"
       "H_3 : c"
       "⊢ a"
       "--"
       "a : Prop,"
       "b : Prop,"
       "c : Prop,"
       "H_1 : a,"
       "H_2 : b,"
       "H_3 : c"
       "⊢ and b c"))
    '(PROOF_STATE (6 17)
                  (("a : Prop," "b : Prop," "c : Prop," "H_1 : a," "H_2 : b," "H_3 : c" "⊢ a")
                   ("a : Prop," "b : Prop," "c : Prop," "H_1 : a," "H_2 : b," "H_3 : c" "⊢ and b c")))))
  (should (equal
           (lean-info-proofstate-pos
            (lean-info-proofstate-parse
             '("-- PROOF_STATE|6|17"
               "a : Prop,"
               "b : Prop,"
               "c : Prop,"
               "H_1 : a,"
               "H_2 : b,"
               "H_3 : c"
               "⊢ a"
               "--"
               "a : Prop,"
               "b : Prop,"
               "c : Prop,"
               "H_1 : a,"
               "H_2 : b,"
               "H_3 : c"
               "⊢ and b c")))
           '(6 17)))
  (should (equal (lean-info-proofstate-states (lean-info-proofstate-parse
                                               '("-- PROOF_STATE|6|17"
                                                 "a : Prop,"
                                                 "b : Prop,"
                                                 "c : Prop,"
                                                 "H_1 : a,"
                                                 "H_2 : b,"
                                                 "H_3 : c"
                                                 "⊢ a"
                                                 "--"
                                                 "a : Prop,"
                                                 "b : Prop,"
                                                 "c : Prop,"
                                                 "H_1 : a,"
                                                 "H_2 : b,"
                                                 "H_3 : c"
                                                 "⊢ and b c")))

                 '(("a : Prop," "b : Prop," "c : Prop," "H_1 : a," "H_2 : b," "H_3 : c" "⊢ a")
                   ("a : Prop," "b : Prop," "c : Prop," "H_1 : a," "H_2 : b," "H_3 : c" "⊢ and b c"))))
  (should (equal (lean-info-proofstate-extract-conclusion
                  '("a : Prop,"
                    "b : Prop,"
                    "c : Prop,"
                    "H_1 : a,"
                    "H_2 : b,"
                    "H_3 : c"
                    "⊢ b ∧ c"
                    "..."))
                 '("⊢ b ∧ c" "...")))
  (should (equal (lean-info-proofstate-extract-premises
                  '("a : Prop,"
                    "b : Prop,"
                    "c : Prop,"
                    "H_1 : a,"
                    "H_2 : b,"
                    "H_3 : c"
                    "⊢ b ∧ c"
                    "..."))
                 '("a : Prop,"
                   "b : Prop,"
                   "c : Prop,"
                   "H_1 : a,"
                   "H_2 : b,"
                   "H_3 : c")))
  (should (equal (lean-info-proofstate-states-str
                  (lean-info-proofstate-parse
                   '("-- PROOF_STATE|6|17"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ a"
                     "--"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ and b c"))
                  'show-all)
                 (s-join "\n" '("a : Prop,"
                                "b : Prop,"
                                "c : Prop,"
                                "H_1 : a,"
                                "H_2 : b,"
                                "H_3 : c"
                                "⊢ a"
                                ""
                                "a : Prop,"
                                "b : Prop,"
                                "c : Prop,"
                                "H_1 : a,"
                                "H_2 : b,"
                                "H_3 : c"
                                "⊢ and b c"))))
  (should (equal (lean-info-proofstate-states-str
                  (lean-info-proofstate-parse
                   '("-- PROOF_STATE|6|17"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ a"
                     "--"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ and b c"))
                  'show-first)
                 (s-join "\n" '("a : Prop,"
                                "b : Prop,"
                                "c : Prop,"
                                "H_1 : a,"
                                "H_2 : b,"
                                "H_3 : c"
                                "⊢ a"))))
  (should (equal (lean-info-proofstate-states-str
                  (lean-info-proofstate-parse
                   '("-- PROOF_STATE|6|17"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ a"
                     "--"
                     "a : Prop,"
                     "b : Prop,"
                     "c : Prop,"
                     "H_1 : a,"
                     "H_2 : b,"
                     "H_3 : c"
                     "⊢ and b c"))
                  'show-first-and-other-conclusions)
                 (s-join "\n" '("a : Prop,"
                                "b : Prop,"
                                "c : Prop,"
                                "H_1 : a,"
                                "H_2 : b,"
                                "H_3 : c"
                                "⊢ a"
                                ""
                                "⊢ and b c")))))

(ert-deftest lean-test-info-pos ()
  "Test lean-info-pos"
  (should (equal
           (lean-info-pos
            (lean-info-type-parse '("-- TYPE|121|2" "not (eq zero (succ m'))" "→ decidable (eq zero (succ m'))")))
           '(121 2)))
  (should (equal
           (lean-info-pos
            (lean-info-overload-parse
             '("-- OVERLOAD|121|2"
               "not (eq zero (succ m'))"
               "→ decidable (eq zero (succ m'))"
               "--"
               "not (eq one (succ m'))"
               "→ decidable (eq zero (succ m'))"
               "--"
               "not (eq two (succ m'))"
               "→ decidable (eq zero (succ m'))")))
           '(121 2))))
