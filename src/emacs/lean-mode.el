;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Leonardo de Moura
;;         Soonho Kong
;;
(require 'cl-lib)
(require 'generic-x)
(require 'compile)
(require 'flymake)
(require 'lean-variable)
(require 'lean-util)
(require 'lean-settings)
(require 'lean-flycheck)
(require 'lean-input)
(require 'lean-type)
(require 'lean-tags)
(require 'lean-syntax)

(defun lean-compile-string (exe-name args file-name)
  "Concatenate exe-name, args, and file-name"
  (format "%s %s %s" exe-name args file-name))

(defun lean-create-temp-in-system-tempdir (file-name prefix)
  "Create a temp lean file and return its name"
  (make-temp-file (or prefix "flymake") nil ".lean"))

(defun lean-execute (&optional arg)
  "Execute Lean in the current buffer"
  (interactive "sarg: ")
  (let ((target-file-name
         (or
          (buffer-file-name)
          (flymake-init-create-temp-buffer-copy 'lean-create-temp-in-system-tempdir))))
    (compile (lean-compile-string
              (lean-get-executable lean-executable-name)
              (or arg "")
              target-file-name))))

(defun lean-std-exe ()
  (interactive)
  (lean-execute))

(defun lean-hott-exe ()
  (interactive)
  (lean-execute "--hott"))

(defun lean-set-keys ()
  (local-set-key "\C-c\C-x" 'lean-std-exe)
  (local-set-key "\C-c\C-l" 'lean-std-exe)
  (local-set-key "\C-c\C-k" 'lean-hott-exe)
  (local-set-key "\C-c\C-t" 'lean-eldoc-documentation-function)
  (local-set-key "\C-c\C-f" 'lean-fill-placeholder)
  (local-set-key "\M-."     'lean-find-tag)
  (local-set-key [tab]      'completion-at-point))

(define-abbrev-table 'lean-abbrev-table
  '(("var"    "variable")
    ("vars"   "variables")
    ("def"    "definition")
    ("th"     "theorem")))

;; Automode List
;;;###autoload
(define-derived-mode lean-mode prog-mode "Lean"
  "Major mode for Lean"
  :syntax-table lean-syntax-table
  :abbrev-table lean-abbrev-table
  :group 'lean
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'font-lock-defaults) lean-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (lean-set-keys)
  (abbrev-mode 1)
  (add-hook 'before-change-functions 'lean-before-change-function nil t)
  (add-hook 'after-change-functions 'lean-after-change-function nil t)
  ;; Draw a vertical line for rule-column
  (when (and lean-rule-column
             lean-show-rule-column-method)
    (cl-case lean-show-rule-column-method
      ('vline (require 'fill-column-indicator)
              (setq fci-rule-column lean-rule-column)
              (setq fci-rule-color lean-rule-color)
              (add-hook 'lean-mode-hook 'fci-mode nil t))))
  ;; Delete Trailing Whitespace
  (if lean-delete-trailing-whitespace
      (progn (require 'whitespace-cleanup-mode)
             (add-hook 'lean-mode-hook 'whitespace-cleanup-mode nil t))
    (remove-hook 'lean-mode-hook 'whitespace-cleanup-mode))
  ;; eldoc
  (set (make-local-variable 'eldoc-documentation-function)
       'lean-eldoc-documentation-function)
  ;; company-mode
  (when lean-company-use
    (require 'company)
    (company-mode t)
    (set (make-local-variable 'company-backends) '(company-etags))))

;; Automatically use lean-mode for .lean files.
;;;###autoload
(push '("\\.lean$" . lean-mode) auto-mode-alist)
;; Use utf-8 encoding
;;;### autoload
(modify-coding-system-alist 'file "\\.lean\\'" 'utf-8)

(provide 'lean-mode)
