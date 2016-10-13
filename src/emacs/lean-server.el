;; Copyright (c) 2016 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Gabriel Ebner
;;

(require 'json)
(require 'tq)
(require 'lean-debug)
(require 'lean-project)

(defvar-local lean-server-process nil
  "Lean server process for the current buffer")

(defvar-local lean-server-handler-tq nil
  "Transaction queue for the currently queued commands to the server")

(defun lean-server-stop ()
  "Stops the lean server for the current buffer"
  (interactive)
  (when lean-server-process
    (tq-close lean-server-handler-tq)
    (kill-buffer (process-buffer lean-server-process))
    (setq lean-server-process nil
          lean-server-handler-tq nil)))

(defun lean-server-start ()
  "Starts the lean server for the current buffer"
  (when (or (not lean-server-process)
            (not (equal (process-status lean-server-process) 'run)))
    (lean-server-stop)
    (setq lean-server-process
          (let* ((default-directory (or (lean-project-find-root) default-directory)))
            (start-file-process "lean-server"
                                (format "*lean-server (%s)*" (buffer-name))
                                "lean" "--server" (format "*%s*" (buffer-name)))))
    (set-process-query-on-exit-flag lean-server-process nil)
    (setq lean-server-handler-tq (tq-create lean-server-process))))

(defun lean-server-restart ()
  "Restarts the lean server for the current buffer"
  (lean-server-stop)
  (lean-server-start))

(defun lean-server-send-command-handler (closure answer)
  "Callback for lean-server-send-command"
  (let ((buffer (elt closure 0))
        (cb (elt closure 1))
        (error-cb (elt closure 2))
        (json-array-type 'list))
    (with-current-buffer buffer
      (lean-debug "server=> %s" answer)
      (let ((response (json-read-from-string answer)))
        (if (equal (cdr (assq 'response response)) "error")
            (progn (message "error: %s" (cdr (assq 'message response)))
                   (if error-cb (funcall error-cb response)))
          (if cb (funcall cb response)))))))

(defun lean-server-send-command (cmd &optional cb error-cb)
  "Sends a command to the lean server, with a callback to be called upon completion"
  (lean-server-start)
  (lean-debug "server<= %s" (json-encode cmd))
  (tq-enqueue lean-server-handler-tq
              (concat (json-encode cmd) "\n") "\n"
              (list (current-buffer) cb error-cb) #'lean-server-send-command-handler))

(defun lean-server-sync ()
  "Synchronizes the current buffer state with the lean server"
  (lean-server-send-command
   (list :command 'sync
         :file_name (buffer-file-name)
         :content (buffer-string))))

(provide 'lean-server)
