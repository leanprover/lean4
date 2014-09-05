;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'dash)
(require 'lean-variable)
(require 'lean-cmd)
(require 'lean-info)
(require 'lean-util)
(require 'flycheck)

;; Parameters
;; ==========
(defvar-local lean-server-process-name      "lean-server")
(defvar-local lean-server-buffer-name       "*lean-server*")
(defvar-local lean-server-trace-buffer-name "*lean-server-trace*")
(defvar-local lean-server-debug-buffer-name "*lean-server-debug*")
(defvar-local lean-server-option            "--server")
(defvar-local lean-server-debug-mode        t)

;; Log Function
;; ============
(defun lean-server-log (format-string &rest args)
  "Display a message at the bottom of the *lean-server* buffer."
  (with-current-buffer (lean-server-get-buffer)
    (goto-char (point-max))
    (insert (apply 'format (concat format-string "\n") args))))

;; Trace Function
;; ============
(defun lean-server-trace (format-string &rest args)
  "Display a message at the bottom of the *lean-server* buffer."
  (with-current-buffer
      (get-buffer-create lean-server-trace-buffer-name)
    (goto-char (point-max))
    (when lean-global-server-last-time-sent
      (let ((time-diff (- (float-time) lean-global-server-last-time-sent)))
        (insert (format "SLEEP %i\n" (* 1000 time-diff)))))
    (setq lean-global-server-last-time-sent (float-time))
    (insert (apply 'format format-string args))))

(defun lean-server-debug (format-string &rest args)
  "Display a message at the bottom of the *lean-server-debug* buffer."
  (when lean-server-debug-mode
    (with-current-buffer
        (get-buffer-create lean-server-debug-buffer-name)
      (goto-char (point-max))
      (insert (format-time-string "%H:%M:%S:%3N -- " (current-time)))
      (insert (apply 'format (concat format-string "\n") args)))))

;; How to read data from an async process
;; ======================================
(defconst lean-server-syntax-pattern
  `((INFO    ,(rx line-start "-- BEGININFO" (* not-newline) line-end)
             ,(rx line-start (group "-- ENDINFO") line-end))
    (SET     ,(rx line-start "-- BEGINSET"  line-end)
             ,(rx line-start (group "-- ENDSET")  line-end))
    (EVAL    ,(rx line-start "-- BEGINEVAL"  line-end)
             ,(rx line-start (group "-- ENDEVAL") line-end))
    (OPTIONS ,(rx line-start "-- BEGINOPTIONS" line-end)
             ,(rx line-start (group "-- ENDOPTIONS") line-end))
    (SHOW    ,(rx line-start "-- BEGINSHOW" line-end)
             ,(rx line-start (group "-- ENDSHOW") line-end))
    (FINDP   ,(rx line-start "-- BEGINFINDP" (* not-newline) line-end)
             ,(rx line-start (group "-- ENDFINDP") line-end))
    (ERROR   ,(rx line-start "-- " (0+ not-newline) line-end)
             ,(rx line-start (group "-- ERROR" (0+ not-newline)) line-end)))
  "Regular expression pattern for lean-server message syntax")

(defun lean-server-split-buffer (buf-str beg-regex end-regex)
  ""
  (let ((beg (string-match beg-regex buf-str))
        (end (string-match end-regex buf-str))
        pre body post)
    (when (and beg end)
      (setq end (match-end 1))
      (setq pre  (substring-no-properties buf-str 0 beg))
      (setq body (substring-no-properties buf-str beg end))
      (setq post (substring-no-properties buf-str end))
      `(,pre ,body ,post))))

(defun lean-server-check-buffer-and-partition (buf-str)
  "Return the status of buffer."
  (let (result)
    (when buf-str
      (cl-loop for (type beg-regex end-regex) in lean-server-syntax-pattern
               do (setq partition-result (lean-server-split-buffer buf-str beg-regex end-regex))
               if partition-result
               return `(,type ,partition-result)))))

(defun lean-server-process-received-message (buf str)
  "Process received message from lean-server"
  (lean-server-log "Received String: %s" str)
  (setq lean-global-server-buffer (concat lean-global-server-buffer str)))

(defun lean-server-output-filter (process string)
  "Filter function attached to lean-server process"
  (lean-server-process-received-message (process-buffer process) string))

(defun lean-server-handle-signal (process event)
  "Handle signals for lean-server-process"
  (cond
   ((string-prefix-p "hangup" event)
    (lean-server-initialize-global-vars))
   ((string-prefix-p "killed" event)
    (lean-server-initialize-global-vars))))

;; How to create an async process
;; ==============================
(defun lean-server-initialize-global-vars ()
  "Initialize lean-server related global variables"
  (setq lean-global-server-buffer nil)
  (setq lean-global-server-current-file-name nil)
  (setq lean-global-server-message-to-process nil)
  (setq lean-global-server-last-time-sent nil)
  (setq lean-global-async-task-queue nil)
  (when (timerp lean-global-retry-timer)
    (cancel-timer lean-global-retry-timer))
  (setq lean-global-retry-timer nil))

(defun lean-server-create-process ()
  "Create lean-server process."
  ;; (when (buffer-modified-p)
  ;;   (error "Please save the buffer before start lean-server."))
  (let ((process-connection-type nil)
        (lean-server-process
         (start-process lean-server-process-name
                        lean-server-buffer-name
                        (lean-get-executable lean-executable-name)
                        lean-server-option)))
    (set-process-coding-system lean-server-process 'utf-8 'utf-8)
    (set-process-filter lean-server-process 'lean-server-output-filter)
    (set-process-sentinel lean-server-process 'lean-server-handle-signal)
    (lean-server-initialize-global-vars)
    (setq lean-global-server-process lean-server-process)
    lean-server-process))

(defun lean-server-kill-process ()
  "Kill lean-server process. Return t if killed, nil if nothing to kill"
  (interactive)
  (lean-server-initialize-global-vars)
  (cond
   ((and lean-global-server-process
         (not (= 0 (process-exit-status lean-global-server-process))))
    (setq lean-global-server-process nil) t)
   (lean-global-server-process
    (when (interactive-p)
      (message "lean-server-kill-process: %S killed" lean-global-server-process))
    (kill-process lean-global-server-process)
    (setq lean-global-server-process nil) t)
   (t
    (when (interactive-p)
      (message "lean-server-kill-process: no process to kill")) nil)))

(defun lean-server-restart-process ()
  "Restart lean-server process."
  (interactive)
  (and (lean-server-kill-process)
       (lean-server-create-process)))

(defun lean-server-get-process ()
  "Get lean-server process. If needed, create a one."
  (cond ((not lean-global-server-process)
         (lean-server-create-process))
        ((not (process-live-p lean-global-server-process))
         (when (interactive-p)
           (message "lean-server-get-process: %S is not live, kill it"
                    lean-global-server-process))
         (lean-server-restart-process))
        (t lean-global-server-process)))

(defun lean-server-get-buffer ()
  "Get lean-server buffer."
  (process-buffer (lean-server-get-process)))

;; How to send data to an async process
;; ====================================
(defun lean-flush-changed-lines ()
  "Flush lean-changed-lines.

Send REPLACE commands to lean-server, reset lean-changed-lines to nil."
  (cl-loop for n in lean-changed-lines
           do (lean-server-send-cmd-async (lean-cmd-replace n (lean-grab-line n)))
           finally (setq lean-changed-lines nil)))

(defun lean-server-check-current-file (&optional file-name)
  "Check lean-global-server-current-file-name.

If it's not the same with file-name (default: buffer-file-name), send VISIT cmd."
  (let ((current-file-name (or file-name (buffer-file-name))))
    (unless (string= lean-global-server-current-file-name
                     current-file-name)
      (lean-server-send-cmd-async (lean-cmd-visit current-file-name)))))

(defun lean-server-before-send-cmd (cmd)
  "Operations to perform before sending a command."
  (cl-case (lean-cmd-type cmd)
    ('LOAD    (setq lean-global-server-current-file-name
                    (lean-cmd-load-get-file-name cmd)))
    ('VISIT   (setq lean-global-server-current-file-name
                    (lean-cmd-visit-get-file-name cmd)))
    ('REPLACE (lean-server-check-current-file))
    ('INSERT  (lean-server-check-current-file))
    ('REMOVE  (lean-server-check-current-file))
    ('INFO    (lean-flush-changed-lines))
    ('CHECK   ())
    ('SET     ())
    ('EVAL    (lean-server-check-current-file))
    ('OPTIONS ())
    ('SHOW    (lean-server-check-current-file))
    ('VALID   (lean-server-check-current-file))
    ('FINDP   (lean-server-check-current-file))))

(defun lean-server-after-send-cmd (cmd)
  "Operations to perform after sending a command."
  (cl-case (lean-cmd-type cmd)
    ('LOAD    ())
    ('VISIT   ())
    ('REPLACE ())
    ('INSERT  ())
    ('REMOVE  ())
    ('INFO    ())
    ('CHECK   ())
    ('SET     ())
    ('EVAL    ())
    ('OPTIONS ())
    ('SHOW    ())
    ('VALID   ())
    ('FINDP   ())))

(defun lean-server-send-cmd (cmd)
  "Send cmd to lean-server"
  (let ((proc (lean-server-get-process))
        (string-to-send (concat (lean-cmd-to-string cmd) "\n")))
    (lean-server-before-send-cmd cmd)
    ;; Logging
    (lean-server-log
     (string-join
      '("Send"
        "================"
        "%s"
        "================") "\n") string-to-send)
    ;; Trace
    (lean-server-trace
     (format "%s" string-to-send))
    (process-send-string proc string-to-send)
    (lean-server-after-send-cmd cmd)))

(defun lean-server-process-message-with-cont (body type cont)
  "Process the message from lean-server and call continuation"
  (cl-case type
    (INFO
     (let ((info-record (lean-server-get-info-record-at-pos body)))
       (funcall cont info-record)))
    (SET
     ;; Call cont with string
     (funcall cont (lean-set-parse-string body)))
    (EVAL
     ;; Call cont with string
     (funcall cont (lean-eval-parse-string body)))
    (OPTIONS
     ;; Call cont with alist of lean-option-records
     (funcall cont (lean-options-parse-string body)))
    (SHOW
     ;; Call cont with string
     (funcall cont (lean-show-parse-string body)))
    (FINDP
     ;; Call cont with (name * type) list
     (funcall cont (lean-findp-parse-string body)))
    (ERROR
     (lean-server-log "Error detected:\n%s" body))))

(defun lean-server-check-and-process-buffer-with-cont (cont)
  "Check server-buffer and process the message with a continuation if it's ready."
  (let ((partition-result (lean-server-check-buffer-and-partition
                           lean-global-server-buffer))
        result)
    (pcase partition-result
      (`(,type (,pre ,body ,post))
       (lean-server-log "The following pre-message will be thrown away:")
       (lean-server-log "%s" pre)
       (setq lean-global-server-buffer post)
       (setq result (lean-server-process-message-with-cont body type cont))
       `(PROCESSED ,result)))))

(defun lean-server-send-cmd-async (cmd &optional cont)
  "Send cmd to lean-server and attach continuation to the queue."
  (lean-server-debug "send-cmd-async: %S" (lean-cmd-type cmd))
  (lean-server-debug "send-cmd-async: queue len = %d" (length lean-global-async-task-queue))
  (lean-server-send-cmd cmd)
  (when cont
    (setq lean-global-async-task-queue (-snoc lean-global-async-task-queue cont))
    (lean-server-cancel-retry-timer)
    (lean-server-debug "send-cmd-async: call handler")
    (lean-server-debug "send-cmd-async: queue len = %S" (length lean-global-async-task-queue))
    (lean-server-event-handler)))

(defun lean-server-cancel-retry-timer ()
  (when (timerp lean-global-retry-timer)
    (cancel-timer lean-global-retry-timer)
    (setq lean-global-retry-timer nil)))

(defun lean-server-consume-all-async-tasks ()
  (while lean-global-async-task-queue
    (accept-process-output (lean-server-get-process) 0 50 t)
    (let* ((cont  (car lean-global-async-task-queue))
           (result (lean-server-check-and-process-buffer-with-cont cont)))
      (pcase result
        (`(PROCESSED ,ret)
         (!cdr lean-global-async-task-queue))))))

(defun lean-server-send-cmd-sync (cmd &optional cont)
  "Send cmd to lean-server (sync)."
  (lean-server-debug "send-cmd-sync: %S" (lean-cmd-type cmd))
  (lean-server-cancel-retry-timer)
  (lean-server-consume-all-async-tasks)
  (lean-server-send-cmd cmd)
  (let ((result (lean-server-check-and-process-buffer-with-cont cont)))
    (while (not result)
      (accept-process-output (lean-server-get-process) 0 50 t)
      (setq result (lean-server-check-and-process-buffer-with-cont cont)))
    (pcase result
      (`(PROCESSED ,ret) ret))))

(defun lean-show-parse-string (str)
  "Parse the output of show command."
  (let ((str-list (split-string str "\n")))
    ;; Drop the first line "-- BEGINSHOW" and
    ;; the last line "-- ENDSHOW"
    (setq str-list
          (-take (- (length str-list) 2)
                 (-drop 1 str-list)))
    (string-join str-list "\n")))

(defun lean-findp-parse-string (str)
  "Parse the output of findp command."
  (let ((str-list (split-string str "\n")))
    ;; Drop the first line "-- BEGINFINDP" and
    ;; the last line "-- ENDFINDP"
    (setq str-list
          (-take (- (length str-list) 2)
                 (-drop 1 str-list)))
    (--map
     (let ((items (split-string it "|")))
       `(,(cl-first items) . ,(cl-second items))) str-list)))

(defun lean-server-show ()
  (interactive)
  (lean-server-send-cmd-async (lean-cmd-show) 'message))

(defun lean-server-valid ()
  (interactive)
  (lean-server-send-cmd-async (lean-cmd-valid) 'message))

(defun lean-server-set-timer-for-event-handler ()
  (unless lean-global-retry-timer
    (setq lean-global-retry-timer
          (run-with-idle-timer
           (if (current-idle-time)
               (time-add (seconds-to-time lean-server-retry-time) (current-idle-time))
             lean-server-retry-time)
           nil
           'lean-server-event-handler)))
  nil)

(defun lean-server-get-info-record-at-pos (body)
  (let* ((file-name (buffer-file-name))
         (column (current-column))
         (cur-char (char-after (point))))
    (when (and cur-char
               (--any? (char-equal cur-char it) '(?\s ?\t ?\, ?\) ?\} ?\]))
               (> column 1))
      (setq column (1- column)))
    (lean-info-record-parse body file-name column)))

(defun lean-server-event-handler ()
  "Process an item from async-task-queue.

If it's successful, take it out from the queue. Otherwise, set an
  idle-timer to call the handler again"
  (lean-server-debug "event-handler: start queue size = %d"
                     (length lean-global-async-task-queue))
  (setq lean-global-retry-timer nil)
  (let* ((cont  (car lean-global-async-task-queue))
         (result (lean-server-check-and-process-buffer-with-cont cont)))
    (pcase result
      (`(PROCESSED ,ret)
       (!cdr lean-global-async-task-queue)
       (lean-server-debug "event-handler: processed. queue size = %d"
                          (length lean-global-async-task-queue))
       ret)))
  (when lean-global-async-task-queue
    (lean-server-set-timer-for-event-handler)))

(provide 'lean-server)
