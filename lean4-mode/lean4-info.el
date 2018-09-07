;; -*- lexical-binding: t -*-
;;
;;; lean4-info.el --- Emacs mode for Lean theorem prover
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

(require 'lean4-syntax)

;; Lean Info Mode (for "*lean4-info*" buffer)
;; Automode List
;;;###autoload
(define-derived-mode lean4-info-mode prog-mode "Lean-Info"
  "Major mode for Lean Info Buffer"
  :syntax-table lean4-syntax-table
  :group 'lean
  (set (make-local-variable 'font-lock-defaults) lean4-info-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set 'compilation-mode-font-lock-keywords '())
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function))

(defmacro lean4-with-info-output-to-buffer (buffer &rest body)
  `(let ((buf (get-buffer ,buffer)))
     (with-current-buffer buf
       (setq buffer-read-only nil)
       (erase-buffer)
       (setq standard-output buf)
       . ,body)))

(defun lean4-ensure-info-buffer (buffer)
  (unless (get-buffer buffer)
    (with-current-buffer (get-buffer-create buffer)
      (buffer-disable-undo)
      (lean4-info-mode))))

(defun lean4-toggle-info-buffer (buffer)
  (-if-let (window (get-buffer-window buffer))
      (quit-window nil window)
    (lean4-ensure-info-buffer buffer)
    (display-buffer buffer)))

(defun lean4-info-buffer-active (buffer)
  "Checks whether the given info buffer should show info for the current buffer"
  (and
   ;; info buffer visible
   (get-buffer-window buffer)
   ;; current window of current buffer is selected (i.e., in focus)
   (eq (current-buffer) (window-buffer))))

(defun lean4-get-info-record-at-point (cont)
  "Get info-record at the current point"
  (with-demoted-errors "lean get info: %s"
    (lean4-server-send-command
     'info (list :file_name (buffer-file-name)
                 :line (line-number-at-pos)
                 :column (lean4-line-offset))
     (cl-function
      (lambda (&key record)
        (funcall cont record))))))

(defun lean4-info-right-click-find-definition ()
  "Offer to jump to definition of right-click target."
  (interactive)
  (list 'info
        (list :file_name (buffer-file-name)
              :line (line-number-at-pos)
              :column (lean4-line-offset))
        (cl-function
         (lambda (&key record)
           (let ((source-record (plist-get record :source)))
             (if source-record
                 (let ((full-name (plist-get record :full-id)))
                   (list
                    (list :name (if full-name
                                    (concat "Find definition of " full-name)
                                  "Find definition")
                          :action (lambda ()
                                    (apply #'lean4-find-definition-cont source-record)))))
               (list)))))))

(cl-defun lean4-find-definition-cont (&key file line column)
  (when (fboundp 'xref-push-marker-stack) (xref-push-marker-stack))
  (when file
    (find-file file))
  (goto-char (point-min))
  (forward-line (1- line))
  (forward-char column))


(defun lean4-find-definition ()
  "Jump to definition of thing at point"
  (interactive)
  (setq lean4-show-goal--handler-mask t) ; avoid the current request to the Lean server to by
                                        ; interrupted by requests made for `lean4-show-goal`
  (lean4-get-info-record-at-point
   (lambda (info-record)
     (-if-let (source-record (plist-get info-record :source))
         (apply #'lean4-find-definition-cont source-record)
       (-if-let (id (plist-get info-record :full-id))
           (message "no source location available for %s" id)
         (message "unknown thing at point"))))))

(provide 'lean4-info)
