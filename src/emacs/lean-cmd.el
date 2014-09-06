;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'lean-util)

;; Constructor
;; ===========
(defun lean-cmd-load (file-name)
  "Load the Lean file named [file-name].

Lean will create a \"snapshot\" (aka backtracking point) after
each command. Lean uses the “snapshots” to process incremental
updates efficiently."
  `(LOAD ,file-name))

(defun lean-cmd-visit (file-name)
  "sets [file-name] as the \"current\" file.

Lean can keep information about multiple files. This command The
remaining commands are all with respect to the current file. If
[file-name] has not been loaded yet, then this command will load
it. Some of the remaining commands apply  'changes'  to the current
file. The LOAD command can be used to discard all these changes,
and enforce the content of the file stored in file system."
  `(VISIT ,file-name))

(defun lean-cmd-replace (line-number new-line)
  "Replace the line [line-number] (in the current file) with [new-line].

 Lean uses the snapshots to process the request efficiently. If
 [line-number] is greater than the total number of lines in the
 lean buffer, then empty lines are introduced. The lines are
 indexed from 1."
  `(REPLACE ,line-number ,new-line))

(defun lean-cmd-insert (line-number new-line)
  "Insert [new-line] (in the current file) before line [line-number].

If [line-number] is greater than the total number of lines in the
lean buffer, then empty lines are introduced. The lines are
indexed from 1."
  `(INSERT ,line-number ,new-line))

(defun lean-cmd-remove (line-number)
  "Remove line [line-number] (in the current file).

The lines are indexed from 1. If [line-number] is greater than
the total number of lines in the lean buffer, then the command is
ignored."
  `(REMOVE ,line-number))

(defun lean-cmd-info (line-number &optional column-number)
  "Extracts typing information associated with line [line-number].

Lean produces a possible empty sequence of entries terminated with '--ENDINFO'"
  `(INFO ,line-number ,column-number))

(defun lean-cmd-check (line-number line)
  "Check whether the text editor and Lean have the 'same view' of the current file + modifications"
  `(CHECK ,line-number ,line))

(defun lean-cmd-set (option-name option-value)
  "Set a Lean option [option-name] with [option-value].

[option-name] must be a valid Lean option. Any option that can be
set using the command set_option in a ‘.lean’ file is supported."
  `(SET ,option-name ,option-value))

(defun lean-cmd-eval (lean-cmd)
  "Evaluates a Lean command [lean-cmd].

It has the effect of evaluating a command in the end of the current file"
  `(EVAL ,lean-cmd))

(defun lean-cmd-options ()
  "Display all configuration options available in Lean."
  `(OPTIONS))

(defun lean-cmd-clear-cache ()
  "Clear Cache"
  `(CLEAR-CACHE))

(defun lean-cmd-show ()
  "Display the \"lines\" associated with the current buffer, or at least"
  `(SHOW))

(defun lean-cmd-valid ()
  "Display valid/invalid lines. Invalid lines are the one we need to refresh type information"
  `(VALID))

(defun lean-cmd-findp (line-number prefix)
  "Find All auto-complete candidates matched with prefix at line-number"
  `(FINDP ,line-number ,prefix))


;; Type
;; ====
(defun lean-cmd-type (cmd)
  (cl-first cmd))

;; Get functions
;; =============
(defun lean-cmd-load-get-file-name (load-cmd)
  (cl-second load-cmd))
(defun lean-cmd-visit-get-file-name (visit-cmd)
  (cl-second visit-cmd))
(defun lean-cmd-replace-get-line-number (replace-cmd)
  (cl-second replace-cmd))
(defun lean-cmd-replace-get-line (replace-cmd)
  (cl-third replace-cmd))
(defun lean-cmd-insert-get-line-number (insert-cmd)
  (cl-second insert-cmd))
(defun lean-cmd-insert-get-line (insert-cmd)
  (cl-third insert-cmd))
(defun lean-cmd-remove-get-line-number (remove-cmd)
  (cl-second remove-cmd))
(defun lean-cmd-info-get-line-number (info-cmd)
  (cl-second info-cmd))
(defun lean-cmd-info-get-column-number (info-cmd)
  (cl-third info-cmd))
(defun lean-cmd-check-get-line-number (check-cmd)
  (cl-second check-cmd))
(defun lean-cmd-check-get-line (check-cmd)
  (cl-third check-cmd))
(defun lean-cmd-set-get-option-name (set-cmd)
  (cl-second set-cmd))
(defun lean-cmd-set-get-option-value (set-cmd)
  (cl-third set-cmd))
(defun lean-cmd-eval-get-lean-cmd (eval-cmd)
  (cl-second eval-cmd))
(defun lean-cmd-findp-get-line-number (findp-cmd)
  (cl-second findp-cmd))
(defun lean-cmd-findp-get-prefix (findp-cmd)
  (cl-third findp-cmd))

;; -- Test
(cl-assert (string= (lean-cmd-load-get-file-name (lean-cmd-load "nat.lean"))
                    "nat.lean"))
(cl-assert (string= (lean-cmd-visit-get-file-name (lean-cmd-visit "nat.lean"))
                    "nat.lean"))
(cl-assert (string=
            (lean-cmd-load-get-file-name (lean-cmd-load "library/standard/bool.lean"))
            "library/standard/bool.lean"))
(cl-assert (string=
            (lean-cmd-load-get-file-name (lean-cmd-load "~/work/lean/basic.lean"))
            "~/work/lean/basic.lean"))
(cl-assert (string=
            (lean-cmd-visit-get-file-name (lean-cmd-visit "library/standard/bool.lean"))
            "library/standard/bool.lean"))
(cl-assert (string=
            (lean-cmd-visit-get-file-name (lean-cmd-visit "~/work/lean/basic.lean"))
            "~/work/lean/basic.lean"))
(cl-assert (= (lean-cmd-replace-get-line-number
               (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
              34))
(cl-assert (string= (lean-cmd-replace-get-line
                     (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
                    "∀ (n : nat), ne (succ n) zero"))
(cl-assert (= (lean-cmd-insert-get-line-number
               (lean-cmd-insert 34 "∀ (n : nat), ne (succ n) zero"))
              34))
(cl-assert (string= (lean-cmd-insert-get-line
                     (lean-cmd-insert 34 "∀ (n : nat), ne (succ n) zero"))
                    "∀ (n : nat), ne (succ n) zero"))
(cl-assert (= (lean-cmd-insert-get-line-number (lean-cmd-remove 34))
              34))
(cl-assert (= (lean-cmd-info-get-line-number (lean-cmd-info 34))
              34))
(cl-assert (= (lean-cmd-info-get-column-number (lean-cmd-info 34 11))
              11))
(cl-assert (= (lean-cmd-check-get-line-number
               (lean-cmd-check 34 "∀ (n : nat), ne (succ n) zero"))
              34))
(cl-assert (string= (lean-cmd-check-get-line
                     (lean-cmd-replace 34 "∀ (n : nat), ne (succ n) zero"))
                    "∀ (n : nat), ne (succ n) zero"))
(cl-assert (string= (lean-cmd-set-get-option-name
                     (lean-cmd-set "pp.implicit" "true"))
                    "pp.implicit"))
(cl-assert (string= (lean-cmd-set-get-option-value
                     (lean-cmd-set "pp.implicit" "true"))
                    "true"))
(cl-assert (string= (lean-cmd-eval-get-lean-cmd
                     (lean-cmd-eval "print 3"))
                    "print 3"))
(cl-assert (= (lean-cmd-findp-get-line-number
               (lean-cmd-findp 10 "iff_"))
              10))
(cl-assert (string= (lean-cmd-findp-get-prefix
                     (lean-cmd-findp 10 "iff_"))
                    "iff_"))

;; to-string functions
;; ===================
(defun lean-cmd-load-to-string (cmd)
  "Convert LOAD command to string"
  (format "LOAD %s" (expand-file-name (lean-cmd-load-get-file-name cmd))))
(defun lean-cmd-visit-to-string (cmd)
  "Convert VISIT command to string"
  (format "VISIT %s" (expand-file-name (lean-cmd-load-get-file-name cmd))))
(defun lean-cmd-replace-to-string (cmd)
  "Convert Replace command to string"
  (format "REPLACE %d\n%s" (lean-cmd-replace-get-line-number cmd)
          (lean-cmd-replace-get-line cmd)))
(defun lean-cmd-insert-to-string (cmd)
  "Convert Insert command to string"
  (format "INSERT %d\n%s" (lean-cmd-insert-get-line-number cmd)
          (lean-cmd-insert-get-line cmd)))
(defun lean-cmd-remove-to-string (cmd)
  "Convert Remove command to string"
  (format "REMOVE %d" (lean-cmd-remove-get-line-number cmd)))
(defun lean-cmd-info-to-string (cmd)
  "Convert Info command to string"
  (let ((col (lean-cmd-info-get-column-number cmd)))
    (if col
        (format "INFO %d %d" (lean-cmd-info-get-line-number cmd) col)
      (format "INFO %d" (lean-cmd-info-get-line-number cmd)))))
(defun lean-cmd-check-to-string (cmd)
  "Convert Check command to string"
  (format "CHECK %d\n%s" (lean-cmd-check-get-line-number cmd)
          (lean-cmd-check-get-line cmd)))
(defun lean-cmd-set-to-string (cmd)
  "Convert Set command to string"
  (format "SET\n%s %s" (lean-cmd-set-get-option-name cmd)
          (lean-cmd-set-get-option-value cmd)))
(defun lean-cmd-eval-to-string (cmd)
  "Convert Eval command to string"
  (format "EVAL\n%s" (lean-cmd-eval-get-lean-cmd cmd)))
(defun lean-cmd-options-to-string (cmd)
  "Convert Options command to string"
  (format "OPTIONS"))
(defun lean-cmd-clear-cache-to-string (cmd)
  "Convert clear-cache command to string"
  (format "CLEAR_CACHE"))
(defun lean-cmd-show-to-string (cmd)
  "Convert show command to string"
  (format "SHOW"))
(defun lean-cmd-valid-to-string (cmd)
  "Convert valid command to string"
  (format "VALID"))
(defun lean-cmd-findp-to-string (cmd)
  "Convert valid command to string"
  (format "FINDP %d\n%s"
          (lean-cmd-findp-get-line-number cmd)
          (lean-cmd-findp-get-prefix cmd)))

(defun lean-cmd-to-string (cmd)
  "Convert command to string"
  (cl-case (lean-cmd-type cmd)
    ('LOAD        (lean-cmd-load-to-string        cmd))
    ('VISIT       (lean-cmd-visit-to-string       cmd))
    ('REPLACE     (lean-cmd-replace-to-string     cmd))
    ('INSERT      (lean-cmd-insert-to-string      cmd))
    ('REMOVE      (lean-cmd-remove-to-string      cmd))
    ('INFO        (lean-cmd-info-to-string        cmd))
    ('CHECK       (lean-cmd-check-to-string       cmd))
    ('SET         (lean-cmd-set-to-string         cmd))
    ('EVAL        (lean-cmd-eval-to-string        cmd))
    ('OPTIONS     (lean-cmd-options-to-string     cmd))
    ('CLEAR-CACHE (lean-cmd-clear-cache-to-string cmd))
    ('SHOW        (lean-cmd-show-to-string        cmd))
    ('VALID       (lean-cmd-valid-to-string       cmd))
    ('FINDP       (lean-cmd-findp-to-string       cmd))))

;; -- Test
(cl-assert (string= (lean-cmd-to-string (lean-cmd-load "~/work/lean/basic.lean"))
                    (concat "LOAD " (expand-file-name "~/work/lean/basic.lean"))))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-visit "~/work/lean/basic.lean"))
                    (concat "VISIT " (expand-file-name "~/work/lean/basic.lean"))))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-replace 42 "∀ (n : nat), ne (succ n) zero"))
                    (concat "REPLACE 42" "\n" "∀ (n : nat), ne (succ n) zero")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-insert 42 "∀ (n : nat), ne (succ n) zero"))
                    (concat "INSERT 42" "\n" "∀ (n : nat), ne (succ n) zero")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-remove 42))
                    (concat "REMOVE 42")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-info 42))
                    (concat "INFO 42")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-info 42 11))
                    (concat "INFO 42 11")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-check 42 "∀ (n : nat), ne (succ n) zero"))
                    (concat "CHECK 42" "\n" "∀ (n : nat), ne (succ n) zero")))
(cl-assert (string= (lean-cmd-to-string (lean-cmd-findp 42 "iff_"))
                    (concat "FINDP 42" "\n" "iff_")))
;; ----------------
(provide 'lean-cmd)
