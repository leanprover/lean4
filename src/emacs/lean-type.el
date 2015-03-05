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

(defun lean-toggle-eldoc-mode ()
  "Toggle eldoc-mode"
  (interactive)
  (cond
   (eldoc-mode (eldoc-mode -1))
   (t          (eldoc-mode  1))))

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

(defconst lean-info-buffer-name "*lean-info*")
(defconst lean-info-buffer-delimiter "-------------------------------\n")

(defun lean-setup-info-buffer ()
  (unless (get-buffer lean-info-buffer-name)
    (with-current-buffer (get-buffer-create lean-info-buffer-name)
      (lean-info-mode))))

(defvar-local lean-info-prev-message nil
  "A variable storing the previous message written to *lean-info*
buffer. It's used to avoid outputting the same message")

(defun lean-output-to-lean-info-buffer (fmt args)
  (lean-setup-info-buffer)
  (let ((output (apply 'format fmt args)))
    (when (and (> (length output) 0)
               (or (not lean-info-prev-message)
                   (not (string= lean-info-prev-message output))))
      (setq lean-info-prev-message output)
      (lean-output-to-buffer lean-info-buffer-name lean-info-buffer-delimiter nil)
      (lean-output-to-buffer lean-info-buffer-name "%s\n" (list output)))))

(defun lean-eldoc-documentation-function-cont (info-record &optional add-to-kill-ring)
  "Continuation for lean-eldoc-documentation-function"
  (let* ((info-strings (lean-info-record-to-strings info-record))
         (info-string-mini-buffer (and info-strings (string-join info-strings " ")))
         (info-string-info-buffer (and info-strings (-last-item info-strings)))
         (proofstate (lean-info-record-proofstate info-record)))
    (when info-strings
      (when add-to-kill-ring
        (kill-new
         (substring-no-properties info-string-mini-buffer)))
      ;; Display on Mini-buffer
      (when (or lean-show-proofstate-in-minibuffer
                (not proofstate))
        (message "%s" info-string-mini-buffer))
      ;; Display on Info Buffer
      (when info-string-info-buffer
        (lean-output-to-lean-info-buffer "%s" (list info-string-info-buffer))))))

(defun lean-eldoc-documentation-function (&optional add-to-kill-ring)
  "Show information of lean expression at point if any"
  (interactive)
  (cond ((and lean-flycheck-use
              (or (get-char-property (point) 'flycheck-error)
                  (get-char-property (point) 'flycheck-warning)))
         nil)
        ((or (and (not (looking-at (rx white)))
                  (not (eolp)))
             (and (looking-back (rx (not white)))
                  (not (bolp))))
         (lean-get-info-record-at-point
          (lambda (info-record)
            (lean-eldoc-documentation-function-cont info-record add-to-kill-ring))))))

(defun lean-show-type ()
  "Show information of lean-expression at point if any."
  (interactive)
  (lean-eldoc-documentation-function lean-show-type-add-to-kill-ring))

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
