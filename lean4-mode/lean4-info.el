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

(require 'dash)
(require 'lean4-syntax)
(require 'lean4-settings)
(require 'lsp-mode)
(require 'lsp-protocol)
(require 'magit-section)

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
      (magit-section-mode)
      (set-syntax-table lean4-syntax-table))))

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

(eval-when-compile
  (lsp-interface
    (lean:PlainGoal (:goals) nil)
    (lean:PlainTermGoal (:goal) nil)
    (lean:Diagnostic (:range :fullRange :message) (:code :relatedInformation :severity :source :tags))))

(defconst lean4-info-buffer-name "*Lean Goal*")

(defvar lean4-goals nil)
(defvar lean4-term-goal nil)

(lsp-defun lean4-diagnostic-full-start-line ((&lean:Diagnostic :full-range (&Range :start (&Position :line))))
  line)
(lsp-defun lean4-diagnostic-full-end-line ((&lean:Diagnostic :full-range (&Range :end (&Position :line))))
  line)

(defun lean4-mk-message-section (caption errors)
  (when errors
    (magit-insert-section (magit-section)
      (magit-insert-heading caption)
      (magit-insert-section-body
        (dolist (e errors)
          (-let (((&Diagnostic :message :range (&Range :start (&Position :line :character))) e))
            (magit-insert-section (magit-section)
              (magit-insert-heading (format "%d:%d: " (1+ (lsp-translate-line line)) (lsp-translate-column character)))
              (magit-insert-section-body
                (insert message "\n")))))))))

(defun lean4-info-buffer-redisplay ()
  (when (lean4-info-buffer-active lean4-info-buffer-name)
    (-let* ((deactivate-mark) ; keep transient mark
            (pos (apply #'lsp-make-position (lsp--cur-position)))
            (line (lsp--cur-line))
            (errors (lsp--get-buffer-diagnostics))
            (errors (-sort (-on #'< #'lean4-diagnostic-full-end-line) errors))
            ((errors-above errors)
             (--split-with (< (lean4-diagnostic-full-end-line it) line) errors))
            ((errors-here errors-below)
             (--split-with (<= (lean4-diagnostic-full-start-line it) line) errors)))
      (lean4-with-info-output-to-buffer
       lean4-info-buffer-name
       (when lean4-goals
         (magit-insert-section (magit-section)
           (magit-insert-heading "Goals:")
           (magit-insert-section-body
             (if (> (length lean4-goals) 0)
                 (seq-doseq (g lean4-goals)
                   (magit-insert-section (magit-section)
                     (insert (lsp--fontlock-with-mode g 'lean4-info-mode) "\n\n")))
               (insert "goals accomplished\n\n")))))
       (when lean4-term-goal
         (magit-insert-section (magit-section)
           (magit-insert-heading "Expected type:")
           (magit-insert-section-body
             (insert (lsp--fontlock-with-mode lean4-term-goal 'lean4-info-mode) "\n"))))
       (lean4-mk-message-section "Messages here:" errors-here)
       (lean4-mk-message-section "Messages below:" errors-below)
       (lean4-mk-message-section "Messages above:" errors-above)
       (when lean4-highlight-inaccessible-names
         (goto-char 0)
         (while (re-search-forward "\\(\\sw+\\)✝\\([¹²³⁴-⁹⁰]*\\)" nil t)
           (replace-match
            (propertize (s-concat (match-string-no-properties 1) (match-string-no-properties 2))
                        'font-lock-face 'font-lock-comment-face)
            'fixedcase 'literal)))))))

(defun lean4-info-buffer-refresh ()
  (when (lean4-info-buffer-active lean4-info-buffer-name)
    (lsp-request-async
     "$/lean/plainGoal"
     (lsp--text-document-position-params)
     (-lambda ((_ &as &lean:PlainGoal? :goals))
       (setq lean4-goals goals)
       (lean4-info-buffer-redisplay))
     :error-handler #'ignore
     :mode 'tick
     :cancel-token :plain-goal)
    (lsp-request-async
     "$/lean/plainTermGoal"
     (lsp--text-document-position-params)
     (-lambda ((_ &as &lean:PlainTermGoal? :goal))
       (setq lean4-term-goal goal)
       (lean4-info-buffer-redisplay))
     :error-handler #'ignore
     :mode 'tick
     :cancel-token :plain-term-goal)
    ;; may lead to flickering
    ;(lean4-info-buffer-redisplay)
    ))

(defun lean4-toggle-info ()
  "Show infos at the current point."
  (interactive)
  (lean4-toggle-info-buffer lean4-info-buffer-name)
  (lean4-info-buffer-refresh))

(provide 'lean4-info)
