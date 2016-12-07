;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2016 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Gabriel Ebner
;;

(require 'json)
(require 'lean-debug)
(require 'lean-project)

(defstruct lean-server-session
  project-dir      ; the project directory of this lean server
  process          ; process object of lean --server
  seq-num          ; sequence number
  callbacks        ; alist of (seq_num . (success_cb . error_cb))
  messages)        ; list of messages in deserialized json

(defun lean-server-session-proc-buffer (sess)
  (process-buffer (lean-server-session-process sess)))

(defun lean-server-session-pop-callback (sess seq-num)
  (let ((cbp (assoc seq-num (lean-server-session-callbacks sess))))
    (setf (lean-server-session-callbacks sess)
          (delete cbp (lean-server-session-callbacks sess)))
    (if cbp (cdr cbp) (cons nil nil))))

(defun lean-server-process-response (sess res)
  (pcase (plist-get res :response)
    ("additional_message"
     (setf (lean-server-session-messages sess)
           (cons (plist-get res :msg) (lean-server-session-messages sess)))
     (lean-server-notify-messages-changed sess))
    ("all_messages"
     (setf (lean-server-session-messages sess)
           (plist-get res :msgs))
     (lean-server-notify-messages-changed sess))
    ("error"
     (message "error: %s" (plist-get res :message))
     ; TODO(gabriel): maybe even add the error as a message
     (when (plist-get res :seq_num)
       (let ((cb (lean-server-session-pop-callback sess (plist-get res :seq_num))))
         (when (cdr cb) (funcall (cdr cb) res)))))
    ("ok"
     (let ((cb (lean-server-session-pop-callback sess (plist-get res :seq_num))))
       (when (car cb) (funcall (car cb) res))))))

(defun lean-server-process-line (sess line)
  (with-demoted-errors "error in lean-server command handler: %s"
    (let* ((json-array-type 'list)
           (json-object-type 'plist)
           (response (json-read-from-string line)))
        (lean-debug "server=> %s" line)
        (lean-server-process-response sess response))))

(defun lean-server-process-buffer (sess)
  (goto-char (point-min))
  (when (search-forward "\n" nil t)
    (let ((line (buffer-substring (point-min) (point))))
      (delete-region (point-min) (point))
      (lean-server-process-line sess line)
      (lean-server-process-buffer sess))))

(defun lean-server-filter (sess string)
  (when (buffer-live-p (lean-server-session-proc-buffer sess))
    (with-current-buffer (lean-server-session-proc-buffer sess)
      (goto-char (point-max))
      (insert string)
      (lean-server-process-buffer sess))))

(defun lean-server-handle-signal (process event)
  "Handle signals for lean-server-process"
  (let ((event-string (s-trim event)))
    (lean-debug "lean-server-handle-signal: %s"
                (propertize event-string 'face '(:foreground "red")))
    (if (s-contains? "abnormally" event)
        (message (concat "Lean server died. See lean-server stderr buffer for details; "
                         "use lean-server-restart to restart it")))))

(defun lean-server-session-create (project-dir)
  "Creates a new server session"
  (let* ((default-directory project-dir)
         ; Setting process-connection-type is necessary, otherwise
         ; emacs truncates lines with >4096 bytes:
         ; https://debbugs.gnu.org/cgi/bugreport.cgi?bug=24531
         (process-connection-type nil)
         (proc (if (fboundp 'make-process)
                   (make-process ;; emacs >= 25 lets us redirect stderr
                    :name "lean-server"
                    :buffer (format "*lean-server (%s)*" project-dir)
                    :command `(,(lean-get-executable lean-executable-name)
                               "--server"
                               ,(format "*%s*" project-dir))
                    :coding 'utf-8
                    :noquery t
                    :sentinel #'lean-server-handle-signal
                    :stderr (format "*lean-server stderr (%s)*" project-dir))
                 (start-file-process "lean-server"
                                     (format "*lean-server (%s)*" (buffer-name))
                                     (lean-get-executable lean-executable-name)
                                     "--server"
                                     (format "*%s*" (buffer-name)))))
         (sess (make-lean-server-session
                :project-dir project-dir
                :process proc
                :seq-num 0
                :callbacks nil
                :messages nil)))
    (set-process-filter proc (lambda (proc string) (lean-server-filter sess string)))
    (set-process-coding-system proc 'utf-8 'utf-8)
    (set-process-query-on-exit-flag proc nil)
    sess))

(defun lean-server-session-send-command (sess cmd-name params &optional cb error-cb)
  (let* ((seq-num (lean-server-session-seq-num sess))
         (req `(:seq_num ,seq-num :command ,cmd-name . ,params))
         (json-array-type 'list)
         (json-object-type 'plist)
         (json-req (json-encode req))
         (cur-buf (current-buffer))
         (wrapped-cb (lambda (res) (with-current-buffer cur-buf (apply cb :allow-other-keys t res))))
         (wrapped-err-cb (lambda (res) (with-current-buffer cur-buf (apply error-cb :allow-other-keys t res)))))
    (setf (lean-server-session-seq-num sess) (1+ seq-num))
    (if (or cb error-cb)
        (setf (lean-server-session-callbacks sess)
              (cons (cons seq-num (cons wrapped-cb wrapped-err-cb)) (lean-server-session-callbacks sess))))
    (lean-debug "server<= %s" json-req)
    (process-send-string (lean-server-session-process sess)
                         (concat json-req "\n"))))

(defvar lean-server-sessions nil
  "list of all running lean-server-sessions")

(defun lean-server-session-alive-p (sess)
  (and sess
       (lean-server-session-process sess)
       (equal 'run (process-status (lean-server-session-process sess)))))

(defun lean-server-session-kill (sess)
  (delete-process (lean-server-session-process sess))
  (kill-buffer (lean-server-session-proc-buffer sess))
  (setf (lean-server-session-process sess) nil)
  (setq lean-server-sessions (delete sess lean-server-sessions)))

(defun lean-server-session-get (project-dir)
  (setq lean-server-sessions
        (remove-if-not #'lean-server-session-alive-p
                       lean-server-sessions))
  (or (find project-dir lean-server-sessions
            :test (lambda (d s) (equal d (lean-server-session-project-dir s))))
      (let ((sess (lean-server-session-create project-dir)))
        (setq lean-server-sessions (cons sess lean-server-sessions))
        sess)))

(defvar-local lean-server-session nil
  "Lean server session for the current buffer")

(defun lean-server-notify-messages-changed (sess)
  (dolist (buf (buffer-list))
    (with-current-buffer buf
      (when (eq sess lean-server-session)
        (run-at-time nil nil
                     (lambda ()
                       (flycheck-mode -1)
                       (flycheck-mode)
                       (flycheck-buffer)))))))

(defun lean-server-stop ()
  "Stops the lean server associated with the current buffer"
  (interactive)
  (when lean-server-session
    (lean-server-session-kill lean-server-session)))

(defun lean-server-ensure-alive ()
  "Ensures that the current buffer has a lean server"
  (when (not (lean-server-session-alive-p lean-server-session))
    (setq lean-server-session (lean-server-session-get
                               (or (lean-project-find-root)
                                   (file-name-directory (buffer-file-name)))))
    (lean-server-sync)))

(defun lean-server-restart ()
  "Restarts the lean server for the current buffer"
  (interactive)
  (lean-server-stop)
  (lean-server-ensure-alive)
  (when lean-flycheck-use
    (flycheck-stop)
    (flycheck-buffer)))

(defun lean-server-send-command (cmd params &optional cb error-cb)
  "Sends a command to the lean server for the current buffer, with a callback to be called upon completion"
  (lean-server-ensure-alive)
  (lean-server-session-send-command lean-server-session cmd params cb error-cb))

(defun lean-server-sync ()
  "Synchronizes the current buffer state with the lean server"
  (lean-server-send-command
   'sync (list :file_name (buffer-file-name)
               :content (buffer-string))))

(defvar-local lean-server-sync-timer nil)

(defun lean-server-change-hook (begin end len)
  (when lean-server-sync-timer (cancel-timer lean-server-sync-timer))
  (setq lean-server-sync-timer
        (run-at-time "200 milliseconds" nil #'lean-server-sync)))

(provide 'lean-server)
