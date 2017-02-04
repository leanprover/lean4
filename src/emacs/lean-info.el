;; -*- lexical-binding: t -*-
;;
;;; lean-info.el --- Emacs mode for Lean theorem prover
;;
;; Copyright (c) 2016 Gabriel Ebner. All rights reserved.
;;
;; Author: Gabriel Ebner <gebner@gebner.org>
;; Maintainer: Gabriel Ebner <gebner@gebner.org>
;; Created: Oct 29, 2016
;; Keywords: languages
;; Version: 0.1
;; URL: https://github.com/leanprover/lean/blob/master/src/emacs
;;
;; Released under Apache 2.0 license as described in the file LICENSE.
;;

;; Lean Info Mode (for "*lean-info*" buffer)
;; Automode List
;;;###autoload
(define-derived-mode lean-info-mode prog-mode "Lean-Info"
  "Major mode for Lean Info Buffer"
  :syntax-table lean-syntax-table
  :group 'lean
  (set (make-local-variable 'font-lock-defaults) lean-info-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set 'compilation-mode-font-lock-keywords '())
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function))

(defmacro lean-with-info-output-to-buffer (buffer &rest body)
  `(let ((buf (get-buffer ,buffer)))
     (with-current-buffer buf
       (setq buffer-read-only nil)
       (erase-buffer)
       (setq standard-output buf)
       . ,body)))

(defun lean-toggle-info-buffer (buffer)
  (-if-let (window (get-buffer-window buffer))
      (quit-window nil window)
    (unless (get-buffer buffer)
      (with-current-buffer (get-buffer-create buffer)
        (buffer-disable-undo)
        (lean-info-mode)))
    (display-buffer buffer)))

(defun lean-info-buffer-active (buffer)
  "Checks whether the given info buffer should show info for the current buffer"
  (and
   ;; info buffer visible
   (get-buffer-window buffer)
   ;; current window of current buffer is selected (i.e., in focus)
   (eq (current-buffer) (window-buffer))))

(defun lean-get-info-record-at-point (cont)
  "Get info-record at the current point"
  (lean-server-send-command
   'info (list :file_name (buffer-file-name)
               :line (line-number-at-pos)
               :column (lean-line-offset))
   (cl-function
    (lambda (&key record)
      (funcall cont record)))))

(cl-defun lean-find-definition-cont (&key file line column)
  (when (fboundp 'xref-push-marker-stack) (xref-push-marker-stack))
  (when file
    (find-file file))
  (goto-char (point-min))
  (forward-line (1- line))
  (forward-char column))


(defun lean-find-definition ()
  "Jump to definition of thing at point"
  (interactive)
  (lean-get-info-record-at-point
   (lambda (info-record)
     (-if-let (source-record (plist-get info-record :source))
         (apply #'lean-find-definition-cont source-record)
       (-if-let (id (plist-get info-record :full-id))
           (message "no source location available for %s" id)
         (message "unknown thing at point"))))))

(provide 'lean-info)
