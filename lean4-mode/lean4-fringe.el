;;; lean4-fringe.el -*- lexical-binding: t; -*-
;;
;; Copyright (c) 2016 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Authors: Gabriel Ebner, Sebastian Ullrich
;;
;;; Commentary:
;;
;; Show Lean processing progress in the editor fringe
;;
;;; Code:

(require 'lean4-settings)
(require 'lsp-mode)
(require 'lsp-protocol)

(eval-when-compile
  (lsp-interface
    (lean:LeanFileProgressProcessingInfo (:range) nil)
    (lean:LeanFileProgressParams (:textDocument :processing) nil)))

(defvar-local lean4-fringe-delay-timer nil)

(defvar-local lean4-fringe-overlays nil)

(lsp-defun lean4-fringe-region ((&lean:LeanFileProgressProcessingInfo :range))
  (lsp--range-to-region range))

(defface lean4-fringe-face
  nil
  "Face to highlight Lean file progress."
  :group 'lean4)

(if (fboundp 'define-fringe-bitmap)
  (define-fringe-bitmap 'lean4-fringe-fringe-bitmap
    (vector) 16 8))

(defface lean4-fringe-fringe-face
  '((((class color) (background light))
     :background "chocolate1")
    (((class color) (background dark))
     :background "navajo white")
    (t :inverse-video t))
  "Face to highlight the fringe of Lean file progress."
  :group 'lean)

(defvar-local lean4-fringe-data nil)

(defun lean4-fringe-update-progress-overlays ()
  (dolist (ov lean4-fringe-overlays) (delete-overlay ov))
  (setq lean4-fringe-overlays nil)
  (when lean4-show-file-progress
    (seq-doseq (item lean4-fringe-data)
      (let* ((reg (lean4-fringe-region item))
             (ov (make-overlay (car reg) (cdr reg))))
        (setq lean4-fringe-overlays (cons ov lean4-fringe-overlays))
        (overlay-put ov 'face 'lean4-fringe-face)
        (overlay-put ov 'line-prefix
                     (propertize " " 'display
                                 '(left-fringe lean4-fringe-fringe-bitmap lean4-fringe-fringe-face)))
        (overlay-put ov 'help-echo (format "processing..."))))))

(defvar-local lean4-fringe-delay-timer nil)

(lsp-defun lean4-fringe-update (workspace (&lean:LeanFileProgressParams :processing :text-document (&VersionedTextDocumentIdentifier :uri)))
  (dolist (buf (lsp--workspace-buffers workspace))
    (lsp-with-current-buffer buf
      (when (equal (lsp--buffer-uri) uri)
        (setq lean4-fringe-data processing)
        (save-match-data
          (when (not (memq lean4-fringe-delay-timer timer-list))
            (setq lean4-fringe-delay-timer
                  (run-at-time "300 milliseconds" nil
                               (lambda (buf)
                                 (with-current-buffer buf
                                   (lean4-fringe-update-progress-overlays)))
                               (current-buffer)))))))))

(provide 'lean4-fringe)
;;; lean4-fringe.el ends here
