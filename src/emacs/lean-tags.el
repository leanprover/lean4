;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'dash)
(defun lean-tags-table-list ()
  (let* ((lean-path-env-list
          (parse-colon-path (getenv "LEAN_PATH")))
         (lean--path-list
          (parse-colon-path
           (ignore-errors
             (car (process-lines (lean-get-executable lean-executable-name)
                                 "--path")))))
         (lean-path-list
          (-uniq (append lean-path-env-list lean--path-list)))
         (tags-file-list
          (-non-nil
           (--map (let ((tags-file (concat (file-name-as-directory it)
                                           "TAGS")))
                    (if (file-exists-p tags-file)
                        tags-file
                      nil))
                  lean-path-list))))
    tags-file-list))

(defun lean-generate-tags ()
  "Run linja TAGS and let emacs use the generated TAGS file."
  (interactive)
  (let ((ltags-file-name (lean-get-executable "linja"))
        tags-file)
    (message "Generating TAGS...")
    (apply 'call-process
           (append `(,ltags-file-name nil "*lean-tags*" nil)
                   lean-flycheck-checker-options
                   '("TAGS")))
    (message "TAGS generated.")
    (setq tags-table-list (lean-tags-table-list))
    (setq tags-file (lean-find-file-upward "TAGS"))
    (when tags-file
      (add-to-list 'tags-table-list tags-file))))

(defmacro lean-tags-make-advice-to-call-ltags (f)
  (let* ((f-name (symbol-name f))
         (advice-name (concat "lean-tags-advice-"
                              (symbol-name f))))
    `(defadvice ,f
       (before ,(intern advice-name)  first activate)
       ,(concat "Before call " f-name ", run 'linja TAGS'")
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
  (lean-get-full-name-at-point
   (lambda (full-name)
     (lean-server-debug "lean-find-tag: %s" full-name)
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
