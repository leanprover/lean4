;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)

(defvar lean-debug-buffer-name "*lean-debug*")

(defun lean-turn-on-debug-mode (&optional print-msg)
  (interactive)
  (when (eq major-mode 'lean-mode)
    (when (or (called-interactively-p) print-msg)
      (message "lean: turn on debug mode"))
    (get-buffer-create lean-debug-buffer-name)
    (setq-local lean-debug-mode t)))

(defun lean-turn-off-debug-mode (&optional print-msg)
  (interactive)
  (when (eq major-mode 'lean-mode)
    (when (or (called-interactively-p) print-msg)
      (message "lean: turn off debug mode"))
    (setq-local lean-debug-mode nil)))

(defun lean-toggle-debug-mode ()
  (interactive)
  (if lean-debug-mode
      (lean-turn-off-debug-mode (called-interactively-p))
    (lean-turn-on-debug-mode (called-interactively-p))))

(defun lean-output-to-buffer (buffer-name format-string args)
  (with-current-buffer
      (get-buffer-create buffer-name)
    (save-selected-window
      (ignore-errors
        (select-window (get-buffer-window buffer-name t)))
      (goto-char (point-max))
      (insert (apply 'format format-string args)))))

(defun lean-debug (format-string &rest args)
  "Display a message at the bottom of the *lean-debug* buffer."
  (when lean-debug-mode
    (let ((time-str (format-time-string "%H:%M:%S.%3N" (current-time))))
      (lean-output-to-buffer lean-debug-buffer-name
                             (concat "%s -- " format-string "\n")
                             (cons (propertize time-str 'face 'font-lock-keyword-face)
                                   args)))))

(defun lean-debug-mode-line-status-text ()
  "Get a text describing STATUS for use in the mode line."
  (let ((text
               ;; No Process : "X"
         (cond ((not (lean-server-process-exist-p))
                "X")
               ;; Number of Async Queue: *-n
               ((> (lean-server-async-task-queue-len) 0)
                (format "*-%d" (lean-server-async-task-queue-len)))
               ;; Async Queue = 0
               (t ""))))
    (concat " LeanDebug" text)))

(define-minor-mode lean-debug-mode
  "Minor mode for lean debugging."

  :init-value nil
  :lighter lean-debug-mode-line
  :group 'lean
  :require 'lean)

(provide 'lean-debug)
