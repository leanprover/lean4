;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'dash)
(require 'f)
(require 'lean-util)

(defalias 'lean-global-search 'tags-apropos)

(defun lean-tags-table-list ()
  (-filter 'f-exists?
           (--map (f-join it "TAGS") (lean-path-list))))

(defun lean-generate-tags ()
  "Run linja TAGS and let emacs use the generated TAGS file."
  (interactive)
  (let* ((leantags-file-name (lean-get-executable "linja"))
         leantags-command)
    (setq leantags-command
          (cond ((string= system-type "windows-nt")

                 (append '("python" nil "*lean-tags*" nil)
                         `(,leantags-file-name)
                         lean-flycheck-checker-options
                         '("tags")))
                (t
                 (append `(,leantags-file-name nil "*lean-tags*" nil)
                         lean-flycheck-checker-options
                         '("tags")))))
    (message "Generating TAGS...")
    (apply 'call-process leantags-command)
    (message "TAGS generated.")
    (setq tags-table-list (lean-tags-table-list))))

(defmacro lean-tags-make-advice-to-call-leantags (f)
  (let* ((f-name (symbol-name f))
         (advice-name (concat "lean-tags-advice-"
                              (symbol-name f))))
    `(defadvice ,f
       (before ,(intern advice-name)  first activate)
       ,(concat "Before call " f-name ", run 'linja TAGS'")
       (when (derived-mode-p 'lean-mode)
         (lean-generate-tags)))))

(defvar-local functions-to-call-leantags-before-it
  '(find-tag-noselect
    tags-search
    tags-query-replace
    list-tags
    tags-apropos
    select-tags-table))

(-each functions-to-call-leantags-before-it
  (lambda (f) (eval `(lean-tags-make-advice-to-call-leantags ,f))))

(defun lean-find-tag ()
  "lean-find-tag"
  (interactive)
  (lean-get-full-name-at-point
   (lambda (full-name)
     (lean-debug "lean-find-tag: %s" full-name)
     (when full-name
       (condition-case err
           (find-tag full-name)
         (user-error (message "lean-find-tag error: %s" (cdr err))))))))

(defun lean-complete-tag ()
  "complete with tag"
  (interactive)
  (lean-generate-tags)
  (complete-tag))
(provide 'lean-tags)
