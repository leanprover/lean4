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
(require 'lsp-protocol)

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

(lsp-interface
 (lean:PlainGoal (:rendered) nil))

(defconst lean4-show-goal-buffer-name "*Lean Goal*")

(defun lean4-show-goal--handler ()
  (let ((deactivate-mark)) ; keep transient mark
    (when (lean4-info-buffer-active lean4-show-goal-buffer-name)
      (lsp-request-async
       "$/lean/plainGoal"
       (lsp--text-document-position-params)
       (-lambda ((goal &as &lean:PlainGoal? :rendered))
         (when goal
           (let ((rerendered (lsp--render-string rendered "markdown")))
             (lean4-with-info-output-to-buffer
              lean4-show-goal-buffer-name
              (insert rerendered)
              (when lean4-highlight-inaccessible-names
                (goto-char 0)
                (while (re-search-forward "\\(\\sw+\\)✝\\([¹²³⁴-⁹⁰]*\\)" nil t)
                  (replace-match
                   (propertize (s-concat (match-string-no-properties 1) (match-string-no-properties 2))
                               'font-lock-face 'font-lock-comment-face)
                   'fixedcase 'literal)))))))
       :error-handler #'ignore
       :mode 'tick
       :cancel-token :plain-goal))))

(defun lean4-toggle-show-goal ()
  "Show goal at the current point."
  (interactive)
  (lean4-toggle-info-buffer lean4-show-goal-buffer-name)
  (lean4-show-goal--handler))

(provide 'lean4-info)
