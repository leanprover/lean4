;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
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
             (tasks-for-cur-file (remove-if-not (lambda (task) (equal cur-fn (plist-get task :file_name)))
                                                (plist-get tasks :tasks)))
             (display-tasks))
        ;; do not display tasks for current file when highlighting is enabled
        (when (not lean-server-show-pending-tasks)
          (setq display-tasks tasks-for-cur-file))
        ;; show current task when not in current file
        (when (and cur-task
                   (not (equal cur-fn (plist-get cur-task :file_name))))
          (setq display-tasks (cons cur-task display-task)))
        (mapcar (lambda (task) (apply #'lean-flycheck-parse-task checker buffer cur-fn task))
                display-tasks))))

(cl-defun lean-flycheck-parse-error (checker buffer &key pos_line pos_col severity text file_name &allow-other-keys)
  (flycheck-error-new-at pos_line (1+ pos_col)
                         (pcase severity
                           ("error" 'error)
                           ("warning" 'warning)
                           ("information" 'info)
                           (_ 'info))
                         text
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
                          (remove-if-not (lambda (msg) (equal cur-fn (plist-get msg :file_name)))
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

(defun lean-flycheck-error-list-buffer-width ()
  "Return the width of flycheck-error list buffer"
  (interactive)
  (let* ((flycheck-error-window (get-buffer-window "*Flycheck errors*" t))
         (window                (selected-window))
         (body-width            (window-body-width window)))
    (cond
     ;; If "*Flycheck errors" buffer is available, use its width
     (flycheck-error-window
      (window-body-width flycheck-error-window))
     ;; Can we split vertically?
     ((window-splittable-p window nil)
      body-width)
     ;; Can we split horizontally?
     ((window-splittable-p window t)
      (/ body-width 2))
     ;; In worst case, just use the same width of current window
     (t body-width))))

(defun lean-flycheck-error-list-message-width ()
  "Return the width of error messages in the flycheck-error list buffer"
  (let (;; assume 'Message' is last column and has size 0 (true for default config)
        (other-columns-width (apply '+ (mapcar (apply-partially 'nth 1) flycheck-error-list-format)))
        (margin (length flycheck-error-list-format)))
    (cond
     ;; If lean-flycheck-msg-width is set, use it
     (lean-flycheck-msg-width
      lean-flycheck-msg-width)
     (t (- (lean-flycheck-error-list-buffer-width) other-columns-width margin)))))

(defconst lean-next-error-buffer-name "*Lean Next Error*")

(defun lean-next-error--handler ()
  (when (lean-info-buffer-active lean-next-error-buffer-name)
    (let* ((errors (sort (flycheck-overlay-errors-in (line-beginning-position) (line-end-position))
                         #'flycheck-error-<)))

      ;; prefer error of current position, if any
      (-if-let (e (get-char-property (point) 'flycheck-error))
          (setq errors (list e)))

      ;; fall back to next error
      (if (null errors)
          (-if-let* ((pos (flycheck-next-error-pos 1))
                     (e (get-char-property pos 'flycheck-error)))
              (setq errors (list e))))

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
