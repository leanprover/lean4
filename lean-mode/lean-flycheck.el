;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'flycheck)
(require 'lean-settings)
(require 'lean-server)
(require 'lean-info)

(defun lean-toggle-flycheck-mode ()
  "Toggle flycheck-mode"
  (interactive)
  (cond
   (flycheck-mode (flycheck-mode -1))
   (t             (flycheck-mode  1))))

(cl-defun lean-flycheck-parse-task (checker buffer cur-file-name
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

(defun lean-flycheck-mk-task-msgs (checker buffer sess)
  (if (and sess (lean-server-session-tasks sess)
           (plist-get (lean-server-session-tasks sess) :is_running))
      (let* ((cur-fn (buffer-file-name))
             (tasks (lean-server-session-tasks sess))
             (cur-task (plist-get tasks :cur_task))
             (tasks-for-cur-file (cl-remove-if-not (lambda (task) (equal cur-fn (plist-get task :file_name)))
                                                   (plist-get tasks :tasks)))
             (display-tasks))
        ;; do not display tasks for current file when highlighting is enabled
        (when (not lean-server-show-pending-tasks)
          (setq display-tasks tasks-for-cur-file))
        ;; show current task when not in current file
        (when (and cur-task
                   (not (equal cur-fn (plist-get cur-task :file_name))))
          (setq display-tasks (cons cur-task display-tasks)))
        (mapcar (lambda (task) (apply #'lean-flycheck-parse-task checker buffer cur-fn task))
                display-tasks))))

(defun lean-info-fontify-string (str)
  (lean-ensure-info-buffer "*lean-fontify*")
  (with-current-buffer "*lean-fontify*"
    (erase-buffer)
    (insert str)
    (font-lock-fontify-region (point-min) (point-max) nil)
    (buffer-string)))

(cl-defun lean-flycheck-parse-error (checker buffer &key pos_line pos_col severity text file_name &allow-other-keys)
  (flycheck-error-new-at pos_line (1+ pos_col)
                         (pcase severity
                           ("error" 'error)
                           ("warning" 'warning)
                           ("information" 'info)
                           (_ 'info))
                         (lean-info-fontify-string text)
                         :filename file_name
                         :checker checker :buffer buffer))

(defun lean-flycheck-start (checker callback)
  (let ((cur-fn (buffer-file-name))
        (buffer (current-buffer)))
    (funcall callback 'finished
             (if lean-server-session
                 (append
                  (lean-flycheck-mk-task-msgs checker buffer lean-server-session)
                  (mapcar (lambda (msg) (apply #'lean-flycheck-parse-error checker buffer msg))
                          (cl-remove-if-not (lambda (msg) (equal cur-fn (plist-get msg :file_name)))
                                            (lean-server-session-messages lean-server-session))))))))

(defun lean-flycheck-init ()
  "Initialize lean-flychek checker"
  (flycheck-define-generic-checker 'lean-checker
    "A Lean syntax checker."
    :start #'lean-flycheck-start
    :modes '(lean-mode))
  (add-to-list 'flycheck-checkers 'lean-checker))

(defun lean-flycheck-turn-on ()
  (flycheck-mode t))

(defconst lean-next-error-buffer-name "*Lean Next Error*")

(defun lean-next-error--handler ()
  (when (lean-info-buffer-active lean-next-error-buffer-name)
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
      (lean-with-info-output-to-buffer lean-next-error-buffer-name
       (dolist (e errors)
         (princ (format "%d:%d: " (flycheck-error-line e) (flycheck-error-column e)))
         (princ (flycheck-error-message e))
         (princ "\n\n"))
       (when flycheck-current-errors
         (princ (format "(%d more messages above...)" (length flycheck-current-errors))))))))

(defun lean-toggle-next-error ()
  (interactive)
  (lean-toggle-info-buffer lean-next-error-buffer-name)
  (lean-next-error--handler))

(provide 'lean-flycheck)
