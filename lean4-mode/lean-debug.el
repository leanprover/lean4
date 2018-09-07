;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)

(defvar lean4-debug-mode nil)

(defvar lean4-debug-buffer-name "*lean4-debug*")

(defun lean4-turn-on-debug-mode (&optional print-msg)
  (interactive)
  (when (or (called-interactively-p 'any) print-msg)
    (message "lean: turn on debug mode"))
  (get-buffer-create lean4-debug-buffer-name)
  (buffer-disable-undo lean4-debug-buffer-name)
  (display-buffer lean4-debug-buffer-name 'display-buffer-reuse-window
                  '((reusable-frames . t)))
  (setq lean4-debug-mode t))

(defun lean4-turn-off-debug-mode (&optional print-msg)
  (interactive)
  (when (eq major-mode 'lean4-mode)
    (when (or (called-interactively-p 'any) print-msg)
      (message "lean: turn off debug mode"))
    (setq lean4-debug-mode nil)))

(defun lean4-output-to-buffer (buffer-name format-string args)
  (with-current-buffer
      (get-buffer-create buffer-name)
    (save-selected-window
      (ignore-errors
        (select-window (get-buffer-window buffer-name t)))
      (goto-char (point-max))
      (insert (apply 'format format-string args)))))

(defun lean4-debug (format-string &rest args)
  "Display a message at the bottom of the *lean4-debug* buffer."
  (when lean4-debug-mode
    (let ((time-str (format-time-string "%H:%M:%S.%3N" (current-time))))
      (lean4-output-to-buffer lean4-debug-buffer-name
                             (concat "%s -- " format-string "\n")
                             (cons (propertize time-str 'face 'font-lock-keyword-face)
                                   args)))))

(provide 'lean4-debug)
