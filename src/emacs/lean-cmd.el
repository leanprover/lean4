;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'lean-util)

;; Load
;; ----
(defun lean-cmd-load (file-name)
  "Load the Lean file named [file-name].

Lean will create a \"snapshot\" (aka backtracking point) after
each command. Lean uses the “snapshots” to process incremental
updates efficiently."
  `(LOAD ,file-name))

(defun lean-cmd-load-get-file-name (load-cmd)
  (cl-second load-cmd))

(defun lean-cmd-load-to-string (cmd)
  "Convert LOAD command to string"
  (format "LOAD %s" (expand-file-name (lean-cmd-load-get-file-name cmd))))

;; Visit
;; -----
(defun lean-cmd-visit (&optional file-name)
  "sets [file-name] as the \"current\" file.

Lean can keep information about multiple files. This command The
remaining commands are all with respect to the current file. If
[file-name] has not been loaded yet, then this command will load
it. Some of the remaining commands apply  'changes'  to the current
file. The LOAD command can be used to discard all these changes,
and enforce the content of the file stored in file system."
(let ((file-name (or file-name (buffer-file-name))))
  (cl-assert file-name)
  `(VISIT ,file-name)))

(defun lean-cmd-visit-get-file-name (visit-cmd)
  (cl-second visit-cmd))

(defun lean-cmd-visit-to-string (cmd)
  "Convert VISIT command to string"
  (format "VISIT %s" (expand-file-name (lean-cmd-load-get-file-name cmd))))


;; Replace
;; -------
(defun lean-cmd-replace (line-number new-line)
  "Replace the line [line-number] (in the current file) with [new-line].

 Lean uses the snapshots to process the request efficiently. If
 [line-number] is greater than the total number of lines in the
 lean buffer, then empty lines are introduced. The lines are
 indexed from 1."
  `(REPLACE ,line-number ,new-line))

(defun lean-cmd-replace-get-line-number (replace-cmd)
  (cl-second replace-cmd))

(defun lean-cmd-replace-get-line (replace-cmd)
  (cl-third replace-cmd))

(defun lean-cmd-replace-to-string (cmd)
  "Convert Replace command to string"
  (format "REPLACE %d\n%s" (lean-cmd-replace-get-line-number cmd)
          (lean-cmd-replace-get-line cmd)))

;; Insert
;; ------
(defun lean-cmd-insert (line-number new-line)
  "Insert [new-line] (in the current file) before line [line-number].

If [line-number] is greater than the total number of lines in the
lean buffer, then empty lines are introduced. The lines are
indexed from 1."
  `(INSERT ,line-number ,new-line))

(defun lean-cmd-insert-get-line-number (insert-cmd)
  (cl-second insert-cmd))

(defun lean-cmd-insert-get-line (insert-cmd)
  (cl-third insert-cmd))

(defun lean-cmd-insert-to-string (cmd)
  "Convert Insert command to string"
  (format "INSERT %d\n%s" (lean-cmd-insert-get-line-number cmd)
          (lean-cmd-insert-get-line cmd)))

;; Remove
;; ------
(defun lean-cmd-remove (line-number)
  "Remove line [line-number] (in the current file).

The lines are indexed from 1. If [line-number] is greater than
the total number of lines in the lean buffer, then the command is
ignored."
  `(REMOVE ,line-number))

(defun lean-cmd-remove-get-line-number (remove-cmd)
  (cl-second remove-cmd))

(defun lean-cmd-remove-to-string (cmd)
  "Convert Remove command to string"
  (format "REMOVE %d" (lean-cmd-remove-get-line-number cmd)))

;; Info
;; ----
(defun lean-cmd-info (line-number &optional column-number)
  "Extracts typing information associated with line [line-number].

Lean produces a possible empty sequence of entries terminated with '--ENDINFO'"
  `(INFO ,line-number ,column-number))

(defun lean-cmd-info-get-line-number (info-cmd)
  (cl-second info-cmd))

(defun lean-cmd-info-get-column-number (info-cmd)
  (cl-third info-cmd))

(defun lean-cmd-info-to-string (cmd)
  "Convert Info command to string"
  (let ((col (lean-cmd-info-get-column-number cmd)))
    (if col
        (format "INFO %d %d" (lean-cmd-info-get-line-number cmd) col)
      (format "INFO %d" (lean-cmd-info-get-line-number cmd)))))

;; Check
;; -----
(defun lean-cmd-check (line-number line)
  "Check whether the text editor and Lean have the 'same view' of the current file + modifications"
  `(CHECK ,line-number ,line))

(defun lean-cmd-check-get-line-number (check-cmd)
  (cl-second check-cmd))

(defun lean-cmd-check-get-line (check-cmd)
  (cl-third check-cmd))

(defun lean-cmd-check-to-string (cmd)
  "Convert Check command to string"
  (format "CHECK %d\n%s" (lean-cmd-check-get-line-number cmd)
          (lean-cmd-check-get-line cmd)))

;; Set
;; ---
(defun lean-cmd-set (option-name option-value)
  "Set a Lean option [option-name] with [option-value].

 [option-name] must be a valid Lean option. Any option that can be
set using the command set_option in a ‘.lean’ file is supported."
  `(SET ,option-name ,option-value))

(defun lean-cmd-set-get-option-name (set-cmd)
  (cl-second set-cmd))

(defun lean-cmd-set-get-option-value (set-cmd)
  (cl-third set-cmd))

(defun lean-cmd-set-to-string (cmd)
  "Convert Set command to string"
  (format "SET\n%s %s" (lean-cmd-set-get-option-name cmd)
          (lean-cmd-set-get-option-value cmd)))

;; Eval
;; ----
(defun lean-cmd-eval (lean-cmd)
  "Evaluates a Lean command [lean-cmd].

It has the effect of evaluating a command in the end of the current file"
  `(EVAL ,lean-cmd))

(defun lean-cmd-eval-get-lean-cmd (eval-cmd)
  (cl-second eval-cmd))

(defun lean-cmd-eval-to-string (cmd)
  "Convert Eval command to string"
  (format "EVAL\n%s" (lean-cmd-eval-get-lean-cmd cmd)))

;; Options
;; -------
(defun lean-cmd-options ()
  "Display all configuration options available in Lean."
  `(OPTIONS))

(defun lean-cmd-options-to-string (cmd)
  "Convert Options command to string"
  (format "OPTIONS"))

;; Clear Cache
;; -----------
(defun lean-cmd-clear-cache ()
  "Clear Cache"
  `(CLEAR-CACHE))

(defun lean-cmd-clear-cache-to-string (cmd)
  "Convert clear-cache command to string"
  (format "CLEAR_CACHE"))

;; Show
;; ----
(defun lean-cmd-show ()
  "Display the \"lines\" associated with the current buffer, or at least"
  `(SHOW))

(defun lean-cmd-show-to-string (cmd)
  "Convert show command to string"
  (format "SHOW"))

;; Valid
;; -----
(defun lean-cmd-valid ()
  "Display valid/invalid lines. Invalid lines are the one we need to refresh type information"
  `(VALID))

(defun lean-cmd-valid-to-string (cmd)
  "Convert valid command to string"
  (format "VALID"))

;; Findp
;; -----
(defun lean-cmd-findp (line-number prefix)
  "Find All auto-complete candidates matched with prefix at line-number"
  `(FINDP ,line-number ,prefix))

(defun lean-cmd-findp-get-line-number (findp-cmd)
  (cl-second findp-cmd))

(defun lean-cmd-findp-get-prefix (findp-cmd)
  (cl-third findp-cmd))

(defun lean-cmd-findp-to-string (cmd)
  "Convert findp command to string"
  (format "FINDP %d\n%s"
          (lean-cmd-findp-get-line-number cmd)
          (lean-cmd-findp-get-prefix cmd)))

;; Findg
;; -----
(defun lean-cmd-findg (line-number column-number patterns)
  "FINDG generates a sequence of declarations that may be used to “fill” a particular placeholder"
  `(FINDG ,line-number ,column-number ,patterns))

(defun lean-cmd-findg-get-line-number (findg-cmd)
  (cl-second findg-cmd))

(defun lean-cmd-findg-get-column-number (findg-cmd)
  (cl-third findg-cmd))

(defun lean-cmd-findg-get-patterns (findg-cmd)
  (cl-fourth findg-cmd))

(defun lean-cmd-findg-to-string (cmd)
  "Convert findg command to string"
  (format "FINDG %d %d\n%s"
          (lean-cmd-findg-get-line-number cmd)
          (lean-cmd-findg-get-column-number cmd)
          (lean-cmd-findg-get-patterns cmd)))

;; Wait
;; ----
(defun lean-cmd-wait ()
  "Block server until all pending information has been computed."
  `(WAIT))

(defun lean-cmd-wait-to-string (cmd)
  "Convert wait command to string"
  (format "WAIT"))

;; SYNC
;; -----
(defun lean-cmd-sync (&optional lines)
  "Force lean-server to synchonize with emacs buffer. SYNC command provides a number of lines in a buffer, and the contents of the buffer"
  (unless lines
    (let* ((buffer-contents (buffer-substring-no-properties
                             (point-min)
                             (point-max))))
      (setq lines (s-lines buffer-contents))))
  `(SYNC ,lines))

(defun lean-cmd-sync-get-num-lines (sync-cmd)
  (length (cl-second sync-cmd)))

(defun lean-cmd-sync-get-lines (sync-cmd)
  (cl-second sync-cmd))

(defun lean-cmd-sync-to-string (cmd)
  "Convert sync command to string"
  (format "SYNC %d\n%s"
          (lean-cmd-sync-get-num-lines cmd)
          (s-join "\n" (lean-cmd-sync-get-lines cmd))))

;; Type
;; ====
(defun lean-cmd-type (cmd)
  (cl-first cmd))

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
    ('FINDP       (lean-cmd-findp-to-string       cmd))
    ('FINDG       (lean-cmd-findg-to-string       cmd))
    ('WAIT        (lean-cmd-wait-to-string        cmd))
    ('SYNC        (lean-cmd-sync-to-string        cmd))))

;; ----------------
(provide 'lean-cmd)
