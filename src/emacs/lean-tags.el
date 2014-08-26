;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'dash)

(defun lean-generate-tags ()
  "Run lmake TAGS and let emacs use the generated TAGS file."
  (interactive)
  (let ((ltags-file-name (lean-get-executable "lmake"))
        tags-file-name)
    (call-process ltags-file-name nil nil nil "TAGS" "--jobs" "--keep-going" "--permissive"))
  (unless tags-table-list
    (setq tags-file-name (lean-find-file-upward "TAGS"))
    (when tags-file-name
      (visit-tags-table tags-file-name))))

(defmacro lean-tags-make-advice-to-call-ltags (f)
  (let* ((f-name (symbol-name f))
         (advice-name (concat "lean-tags-advice-"
                              (symbol-name f))))
    `(defadvice ,f
       (before ,(intern advice-name)  first activate)
       ,(concat "Before call " f-name ", run 'lmake TAGS'")
       (when (derived-mode-p 'lean-mode)
         (lean-generate-tags)))))

(defvar-local functions-to-call-ltags-before-it
  '(find-tag-noselect
    tags-search
    tags-query-replace
    list-tags
    tags-apropos
    select-tags-table))

(-each functions-to-call-ltags-before-it
  (lambda (f) (eval `(lean-tags-make-advice-to-call-ltags ,f))))

(defun lean-find-tag ()
  "lean-find-tag"
  (interactive)
  (let ((full-name (lean-get-full-name-at-point)))
    (when full-name
      (find-tag full-name))))

(defun lean-complete-tag ()
  "complete with tag"
  (interactive)
  (lean-generate-tags)
  (complete-tag))
(provide 'lean-tags)
