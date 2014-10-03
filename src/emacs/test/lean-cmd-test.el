;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'ert)
(require 'lean-cmd)

(ert-deftest lean-test-cmd-get ()
  "Test lean-cmd-*-get-*"
  (should (string= (lean-cmd-load-get-file-name (lean-cmd-load "nat.lean"))
                   "nat.lean"))
  (should (string= (lean-cmd-visit-get-file-name (lean-cmd-visit "nat.lean"))
                   "nat.lean"))
  (should (string=
           (lean-cmd-load-get-file-name (lean-cmd-load "library/standard/bool.lean"))
           "library/standard/bool.lean"))
  (should (string=
           (lean-cmd-load-get-file-name (lean-cmd-load "~/work/lean/basic.lean"))
           "~/work/lean/basic.lean"))
  (should (string=
           (lean-cmd-visit-get-file-name (lean-cmd-visit "library/standard/bool.lean"))
           "library/standard/bool.lean"))
  (should (string=
           (lean-cmd-visit-get-file-name (lean-cmd-visit "~/work/lean/basic.lean"))
           "~/work/lean/basic.lean"))
  (should (= (lean-cmd-replace-get-line-number
              (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
             34))
  (should (string= (lean-cmd-replace-get-line
                    (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
                   "∀ (n : nat), ne (succ n) zero"))
  (should (= (lean-cmd-insert-get-line-number
              (lean-cmd-insert 34 "∀ (n : nat), ne (succ n) zero"))
             34))
  (should (string= (lean-cmd-insert-get-line
                    (lean-cmd-insert 34 "∀ (n : nat), ne (succ n) zero"))
                   "∀ (n : nat), ne (succ n) zero"))
  (should (= (lean-cmd-insert-get-line-number (lean-cmd-remove 34))
             34))
  (should (= (lean-cmd-info-get-line-number (lean-cmd-info 34))
             34))
  (should (= (lean-cmd-info-get-column-number (lean-cmd-info 34 11))
             11))
  (should (= (lean-cmd-check-get-line-number
              (lean-cmd-check 34 "∀ (n : nat), ne (succ n) zero"))
             34))
  (should (string= (lean-cmd-check-get-line
                    (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
                   "∀ (n : nat), ne (succ n) zero"))
  (should (string= (lean-cmd-set-get-option-name
                    (lean-cmd-set "pp.implicit" "true"))
                   "pp.implicit"))
  (should (string= (lean-cmd-set-get-option-value
                    (lean-cmd-set "pp.implicit" "true"))
                   "true"))
  (should (string= (lean-cmd-eval-get-lean-cmd
                    (lean-cmd-eval "print 3"))
                   "print 3"))
  (should (= (lean-cmd-findp-get-line-number
              (lean-cmd-findp 10 "iff_"))
             10))
  (should (string= (lean-cmd-findp-get-prefix
                    (lean-cmd-findp 10 "iff_"))
                   "iff_"))

  (should (= (lean-cmd-findg-get-line-number
              (lean-cmd-findg 48 10 "+intro -and -elim"))
             48))
  (should (= (lean-cmd-findg-get-column-number
              (lean-cmd-findg 48 10 "+intro -and -elim"))
             10))
  (should (string= (lean-cmd-findg-get-patterns
                    (lean-cmd-findg 48 10 "+intro -and -elim"))
                   "+intro -and -elim"))


  (should (= (lean-cmd-sync-get-num-lines
              (lean-cmd-sync '("line 1"
                               "line 2"
                               "line 3")))
             3))
  (should (equal (lean-cmd-sync-get-lines
              (lean-cmd-sync '("line 1"
                               "line 2"
                               "line 3")))
             '("line 1"
               "line 2"
               "line 3"))))

(ert-deftest lean-test-cmd-to-string ()
  "Test lean-cmd-to-string"
  (should (string= (lean-cmd-to-string (lean-cmd-load "~/work/lean/basic.lean"))
                   (concat "LOAD " (expand-file-name "~/work/lean/basic.lean"))))
  (should (string= (lean-cmd-to-string (lean-cmd-visit "~/work/lean/basic.lean"))
                   (concat "VISIT " (expand-file-name "~/work/lean/basic.lean"))))
  (should (string= (lean-cmd-to-string (lean-cmd-replace 42 "∀ (n : nat), ne (succ n) zero"))
                   (concat "REPLACE 42" "\n" "∀ (n : nat), ne (succ n) zero")))
  (should (string= (lean-cmd-to-string (lean-cmd-insert 42 "∀ (n : nat), ne (succ n) zero"))
                   (concat "INSERT 42" "\n" "∀ (n : nat), ne (succ n) zero")))
  (should (string= (lean-cmd-to-string (lean-cmd-remove 42))
                   (concat "REMOVE 42")))
  (should (string= (lean-cmd-to-string (lean-cmd-info 42))
                   (concat "INFO 42")))
  (should (string= (lean-cmd-to-string (lean-cmd-info 42 11))
                   (concat "INFO 42 11")))
  (should (string= (lean-cmd-to-string (lean-cmd-check 42 "∀ (n : nat), ne (succ n) zero"))
                   (concat "CHECK 42" "\n" "∀ (n : nat), ne (succ n) zero")))
  (should (string= (lean-cmd-to-string (lean-cmd-set "pp.implicit" "true"))
                   (concat "SET" "\n" "pp.implicit true" )))
  (should (string= (lean-cmd-to-string (lean-cmd-eval "check 3"))
                   (concat "EVAL" "\n" "check 3" )))
  (should (string= (lean-cmd-to-string (lean-cmd-options))
                   (concat "OPTIONS")))
  (should (string= (lean-cmd-to-string (lean-cmd-clear-cache))
                   (concat "CLEAR_CACHE")))
  (should (string= (lean-cmd-to-string (lean-cmd-show))
                   (concat "SHOW")))
  (should (string= (lean-cmd-to-string (lean-cmd-valid))
                   (concat "VALID")))
  (should (string= (lean-cmd-to-string (lean-cmd-findp 42 "iff_"))
                   (concat "FINDP 42" "\n" "iff_")))
  (should (string= (lean-cmd-to-string (lean-cmd-findg 48 10 "+intro -and -elim"))
                   (concat "FINDG 48 10" "\n" "+intro -and -elim")))
  (should (string= (lean-cmd-to-string (lean-cmd-wait))
                   (concat "WAIT")))
  (should (string= (lean-cmd-to-string (lean-cmd-sync '("line 1"
                                                        "line 2"
                                                        "line 3")))
                   (concat "SYNC 3\n"
                           "line 1\n"
                           "line 2\n"
                           "line 3"))))
