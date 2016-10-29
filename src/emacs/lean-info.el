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

(defconst lean-info-buffer-name "*lean-info*")

(defmacro with-output-to-lean-info (&rest body)
  `(let ((lean-info-buffer (get-buffer lean-info-buffer-name)))
     (if (and lean-info-buffer (get-buffer-window lean-info-buffer))
         (with-current-buffer lean-info-buffer
           (setq buffer-read-only nil)
           (erase-buffer)
           (setq standard-output lean-info-buffer)
           . ,body)
       (let ((temp-buffer-setup-hook #'lean-info-mode))
         (with-output-to-temp-buffer lean-info-buffer-name . ,body)))))

(provide 'lean-info)
