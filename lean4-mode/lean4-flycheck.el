;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'flycheck)
(require 'lean4-settings)
(require 'lean4-info)
(require 'lean4-debug)

(defun lean4-toggle-flycheck-mode ()
  "Toggle flycheck-mode"
  (interactive)
  (cond
   (flycheck-mode (flycheck-mode -1))
   (t             (flycheck-mode  1))))

(defun lean4-flycheck-command ()
  (let ((command
         (-concat `(,(lean4-get-executable lean4-executable-name))
                  '((eval lean4-extra-arguments))
                  '("--json" "--stdin"))))
    command))

(defun lean4-bootstrapped-flycheck-command ()
  `(,(s-concat (lean4-get-executable lean4-executable-name) "-bootstrapped") source-inplace))

(cl-defun lean4-flycheck-parse-task (checker buffer cur-file-name
                                            &key pos_line pos_col desc file_name &allow-other-keys)
  (if (equal cur-file-name file_name)
      (flycheck-error-new-at pos_line (1+ pos_col)
                             'info
                             (format "still running: %s" desc)
                             :filename file_name
                             :checker checker :buffer buffer)
    (flycheck-error-new-at 1 1
                           'info
                           (format "still running: %s" desc)
                           :filename cur-file-name
                           :checker checker :buffer buffer)))

(defun lean4-flycheck-mk-task-msgs (checker buffer sess)
  (if (and sess (lean4-server-session-tasks sess)
           (plist-get (lean4-server-session-tasks sess) :is_running))
      (let* ((cur-fn (buffer-file-name))
             (tasks (lean4-server-session-tasks sess))
             (cur-task (plist-get tasks :cur_task))
             (tasks-for-cur-file (cl-remove-if-not (lambda (task) (equal cur-fn (plist-get task :file_name)))
                                                   (plist-get tasks :tasks)))
             (display-tasks))
        ;; do not display tasks for current file when highlighting is enabled
        (when (not lean4-server-show-pending-tasks)
          (setq display-tasks tasks-for-cur-file))
        ;; show current task when not in current file
        (when (and cur-task
                   (not (equal cur-fn (plist-get cur-task :file_name))))
          (setq display-tasks (cons cur-task display-tasks)))
        (mapcar (lambda (task) (apply #'lean4-flycheck-parse-task checker buffer cur-fn task))
                display-tasks))))

(defun lean4-info-fontify-string (str)
  (lean4-ensure-info-buffer "*lean4-fontify*")
  (with-current-buffer "*lean4-fontify*"
    (erase-buffer)
    (insert str)
    (font-lock-fontify-region (point-min) (point-max) nil)
    (buffer-string)))

(cl-defun lean4-flycheck-parse-error (checker buffer &key pos_line pos_col severity text file_name &allow-other-keys)
  (flycheck-error-new-at pos_line (1+ pos_col)
                         (pcase severity
                           ("error" 'error)
                           ("warning" 'warning)
                           ("information" 'info)
                           (_ 'info))
                         (lean4-info-fontify-string text)
                         :filename (if (equal file_name "<stdin>") nil file_name)
                         :checker checker :buffer buffer))

(defun lean4-flycheck-parse-errors (output checker buffer)
  (mapcar (lambda (line)
            (lean4-debug "server=> %s" line)
            (let* ((json-array-type 'list)
                   (json-object-type 'plist)
                   (json-false nil))
              (apply #'lean4-flycheck-parse-error checker buffer (json-read-from-string line))))
   (split-string output "\n" t)))

(defun lean4-flycheck-start (checker callback)
  (let ((cur-fn (buffer-file-name))
        (buffer (current-buffer)))
    (funcall callback 'finished
             (if lean4-server-session
                 (append
                  (lean4-flycheck-mk-task-msgs checker buffer lean4-server-session)
                  (mapcar (lambda (msg) (apply #'lean4-flycheck-parse-error checker buffer msg))
                          (cl-remove-if-not (lambda (msg) (equal cur-fn (plist-get msg :file_name)))
                                            (lean4-server-session-messages lean4-server-session))))))))

(defun lean4-flycheck-init ()
  "Initialize lean4-flycheck checker"
  (flycheck-define-command-checker 'lean4-checker
    "A Lean syntax checker."
    :command (lean4-flycheck-command)
    :standard-input t
    :error-parser #'lean4-flycheck-parse-errors
    :modes '(lean4-mode))
  (flycheck-define-command-checker 'lean4-bootstrapped-checker
    "Bootstrapped Lean syntax checker."
    :command (lean4-bootstrapped-flycheck-command)
    :error-parser #'lean4-flycheck-parse-errors
    :modes '(lean4-mode))
  (add-to-list 'flycheck-checkers 'lean4-checker))

(defun lean4-flycheck-turn-on ()
  (flycheck-mode t))

(defconst lean4-next-error-buffer-name "*Lean Next Error*")

(defun lean4-next-error--handler ()
  (when (lean4-info-buffer-active lean4-next-error-buffer-name)
    (let ((deactivate-mark) ; keep transient mark
          (errors (or
                   ;; prefer error of current position, if any
                   (flycheck-overlay-errors-at (point))
                   ;; try errors in current line next
                   (sort (flycheck-overlay-errors-in (line-beginning-position) (line-end-position))
                         #'flycheck-error-<)
                   ;; fall back to next error position
                   (-if-let* ((pos (flycheck-next-error-pos 1)))
                       (flycheck-overlay-errors-at pos)))))
      (lean4-with-info-output-to-buffer lean4-next-error-buffer-name
       (dolist (e errors)
         (princ (format "%d:%d: " (flycheck-error-line e) (flycheck-error-column e)))
         (princ (flycheck-error-message e))
         (princ "\n\n"))
       (when flycheck-current-errors
         (princ (format "(%d more messages above...)" (length flycheck-current-errors))))))))

(defun lean4-toggle-next-error ()
  (interactive)
  (lean4-toggle-info-buffer lean4-next-error-buffer-name)
  (lean4-next-error--handler))

(provide 'lean4-flycheck)
