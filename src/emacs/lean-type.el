;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'dash)
(require 'dash-functional)
(require 'lean-variable)
(require 'lean-util)
(require 'lean-cmd)
(require 'lean-server)
(require 'lean-changes)
(require 'lean-debug)
(require 'flymake)

(defun lean-fill-placeholder-cont (info-record)
  "Continuation for lean-fill-placeholder"
  (let ((synth (and info-record (cl-first (lean-info-record-synth info-record)))))
    (when synth
      (let ((synth-str
             (replace-regexp-in-string "?M_[0-9]+" "_" (lean-info-synth-body-str synth))))
        (when (search " " synth-str)
          (setq synth-str (concat "(" synth-str ")")))
        (when (looking-at "_")
          (delete-forward-char 1)
          (insert synth-str))))))

(defun lean-fill-placeholder ()
  "Fill the placeholder with a synthesized expression by Lean."
  (interactive)
  (lean-get-info-record-at-point 'lean-fill-placeholder-cont))

(defun lean-eldoc-documentation-function-cont (info-record)
  "Continuation for lean-eldoc-documentation-function"
  (let ((info-string (lean-info-record-to-string info-record)))
    (when info-string
      (message "%s" info-string))))

(defun lean-eldoc-documentation-function ()
  "Show information of lean expression at point if any"
  (interactive)
  (lean-get-info-record-at-point 'lean-eldoc-documentation-function-cont))

;; =======================================================
;; eval
;; =======================================================

(defun lean-eval-parse-string (str)
  "Parse the output of eval command."
  (let ((str-list (split-string str "\n")))
    ;; Drop the first line "-- BEGINEVAL" and
    ;; the last line "-- ENDEVAL"
    (setq str-list
          (-take (- (length str-list) 2)
                 (-drop 1 str-list)))
    (string-join str-list "\n")))

(defun lean-eval-cmd (lean-cmd)
  "Evaluate lean command."
  (interactive "sLean CMD: ")
  (lean-server-send-cmd-async (lean-cmd-eval lean-cmd)
                              'message))

;; Clear Cache
(defun lean-clear-cache ()
  "Send CLEAR_CACHE command to lean-server"
  (interactive)
  (call-process (lean-get-executable "linja") nil 0 nil "clear-cache")
  (lean-server-send-cmd-async (lean-cmd-clear-cache)))

(provide 'lean-type)
