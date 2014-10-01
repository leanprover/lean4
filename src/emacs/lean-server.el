;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'dash)
(require 'dash-functional)
(require 'flycheck)
(require 's)
(require 'lean-debug)
(require 'lean-variable)
(require 'lean-cmd)
(require 'lean-info)
(require 'lean-util)

;; Parameters
;; ==========
(defvar lean-server-process-name      "lean-server")
(defvar lean-server-buffer-name       "*lean-server*")
(defvar lean-server-trace-buffer-name "*lean-server-trace*")
(defvar lean-server-option            "--server")

;; Log & Trace
;; ===========
(defun lean-server-log (format-string &rest args)
  "Display a message at the bottom of the *lean-server* buffer."
  (lean-output-to-buffer (lean-server-get-buffer)
                         (concat format-string)
                         args)
  (apply 'lean-debug (cons format-string args)))


(defun lean-server-trace (format-string &rest args)
  "Display a message at the bottom of the *lean-server* buffer."
  (when lean-debug-mode
    (when lean-global-server-last-time-sent
      (let ((time-diff (- (float-time) lean-global-server-last-time-sent)))
        (lean-output-to-buffer lean-server-trace-buffer-name
                                    "SLEEP %i\n"
                                    `(,(truncate (* 1000 time-diff))))))
    (setq lean-global-server-last-time-sent (float-time))
    (lean-output-to-buffer lean-server-trace-buffer-name
                                format-string args)))

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
    (FINDG   ,(rx line-start "-- BEGINFINDG" (* not-newline) line-end)
             ,(rx line-start (group "-- ENDFINDG") line-end))
    (WAIT    ,(rx line-start "-- BEGINWAIT" line-end)
             ,(rx line-start (group "-- ENDWAIT") line-end))
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
  (when buf-str
    (let (matches partition-result)
      (setq matches
            (cl-loop for (type beg-regex end-regex) in lean-server-syntax-pattern
                     do (setq partition-result (lean-server-split-buffer buf-str beg-regex end-regex))
                     if partition-result
                     collect `(,type ,partition-result)))
      (when matches
        (-min-by (-on '< (lambda (type-partition-result) (length (car (cdr type-partition-result)))))
                 matches)))))

(defun lean-server-process-received-message (buf str)
  "Process received message from lean-server"
  (lean-server-log "%s:\n%s\n"
                   (propertize "Received Message" 'face 'font-lock-variable-name-face)
                   str)
  (setq lean-global-server-buffer (concat lean-global-server-buffer str)))

(defun lean-server-output-filter (process string)
  "Filter function attached to lean-server process"
  (lean-server-process-received-message (process-buffer process) string))

(defun lean-server-handle-signal (process event)
  "Handle signals for lean-server-process"
  (let ((event-string (s-trim event)))
    (lean-server-initialize-global-vars)
    (lean-debug "lean-server-handle-signal: %s"
                       (propertize event-string 'face '(:foreground "red")))
    (lean-server-trace "lean-server-handle-signal: %s\n"
                       (propertize event-string 'face '(:foreground "red")))))

;; How to create an async process
;; ==============================

(defun lean-server-cancel-retry-timer ()
  (when (timerp lean-global-retry-timer)
    (cancel-timer lean-global-retry-timer))
  (setq lean-global-retry-timer nil))

(defun lean-server-initialize-global-vars ()
  "Initialize lean-server related global variables"
  (setq lean-global-server-buffer nil)
  (setq lean-global-server-current-file-name nil)
  (setq lean-global-server-message-to-process nil)
  (setq lean-global-server-last-time-sent nil)
  (setq lean-global-async-task-queue nil)
  (setq lean-global-nay-retry-counter 0)
  (setq lean-global-option-alist nil)
  (lean-server-cancel-retry-timer))

(defun lean-server-create-process ()
  "Create lean-server process."
  (let ((process-connection-type nil)
        (lean-server-process
         (start-process lean-server-process-name
                        lean-server-buffer-name
                        (lean-get-executable lean-executable-name)
                        lean-server-option)))
    (set-process-coding-system lean-server-process 'utf-8 'utf-8)
    (set-process-filter lean-server-process 'lean-server-output-filter)
    (set-process-sentinel lean-server-process 'lean-server-handle-signal)
    (set-process-query-on-exit-flag lean-server-process nil)
    (lean-server-initialize-global-vars)
    (setq lean-global-server-process lean-server-process)
    (lean-debug "lean-server process %S is created" lean-server-process)
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

(defun lean-server-process-exist-p ()
  "Return t if lean-server-process exists, otherwise return nil"
  (if lean-global-server-process
      t
    nil))

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
(defun lean-server-flush-changed-lines ()
  "Flush lean-changed-lines.

Send REPLACE commands to lean-server, reset lean-changed-lines to nil."
  (cl-loop for n in lean-changed-lines
           do (lean-server-send-cmd-async (lean-cmd-replace n (lean-grab-line n)))
           finally (setq lean-changed-lines nil)))

(defun lean-server-visit-current-buffer ()
  "Send VISIT for the current buffer"
  (cond ((and (buffer-modified-p)
              (not lean-global-server-current-file-name))
         (lean-server-handle-modified-buffer))
        (t (lean-server-send-cmd-async (lean-cmd-visit)))))

(defun lean-server-check-current-file (&optional file-name)
  "Check lean-global-server-current-file-name

If it's not the same with file-name (default: buffer-file-name), send VISIT cmd."
  (let ((current-file-name (or file-name (buffer-file-name))))
    (unless (string= lean-global-server-current-file-name
                     current-file-name)
      (lean-server-visit-current-buffer))))

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
    ('INFO    (lean-server-flush-changed-lines))
    ('CHECK   ())
    ('SET     ())
    ('EVAL    (lean-server-check-current-file))
    ('OPTIONS ())
    ('SHOW    (lean-server-check-current-file))
    ('VALID   (lean-server-check-current-file))
    ('FINDP   (lean-server-flush-changed-lines)
              (lean-server-check-current-file))
    ('FINDG   (lean-server-flush-changed-lines)
              (lean-server-check-current-file))
    ('WAIT    (lean-server-check-current-file))))

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
    ('FINDP   ())
    ('FINDG   ())
    ('WAIT    ())))

(defun lean-server-send-cmd (cmd)
  "Send cmd to lean-server"
  (let ((proc (lean-server-get-process))
        (string-to-send (concat (lean-cmd-to-string cmd) "\n")))
    (lean-server-before-send-cmd cmd)
    ;; Logging
    (lean-server-log "%s:\n%s"
                     (propertize "Sent Message" 'face 'font-lock-variable-name-face)
                     string-to-send)
    ;; Trace
    (lean-server-trace
     (format "%s" string-to-send))
    (process-send-string proc string-to-send)
    (lean-server-after-send-cmd cmd)))

(defun lean-server-process-message-with-cont (body type cont cmd-type)
  "Process the message from lean-server and call continuation"
  (lean-debug "process-message-with-cont: type = %S, cmd-type = %S"
                     type cmd-type)
  (lean-debug "process-message-with-cont: body\n-----\n%s\n-----\n" body)
  (cl-case type
    (INFO
     (lean-debug "Process: INFO")
     (let ((info-record (lean-server-get-info-record-at-pos body)))
       (funcall cont info-record)))
    (SET
     (lean-debug "Process: SET")
     ;; Call cont with string
     (funcall cont (lean-set-parse-string body)))
    (EVAL
     (lean-debug "Process: EVAL")
     ;; Call cont with string
     (funcall cont (lean-eval-parse-string body)))
    (OPTIONS
     (lean-debug "Process: OPTIONS")
     ;; Call cont with alist of lean-option-records
     (funcall cont (lean-options-parse-string body)))
    (SHOW
     (lean-debug "Process: SHOW")
     ;; Call cont with string
     (funcall cont (lean-show-parse-string body)))
    (FINDP
     (lean-debug "Process: FINDP")
     ;; Call cont with (name * type) list
     (funcall cont (lean-findp-parse-string body)))
    (FINDG
     (lean-debug "Process: FINDG")
     ;; Call cont with (name * type) list
     (funcall cont (lean-findg-parse-string body)))
    (WAIT
     (lean-debug "Process: WAIT")
     ;; Call cont
     (funcall cont))
    (ERROR
     (lean-server-log "Error detected:\n%s" body))))

(defun lean-server-check-and-process-buffer-with-cont (cont cmd-type)
  "Check server-buffer and process the message with a continuation if it's ready."
  (let ((partition-result (lean-server-check-buffer-and-partition
                           lean-global-server-buffer))
        result)
    (condition-case err
        (pcase partition-result
          (`(,type (,pre ,body ,post))
           (lean-server-log "The following pre-message will be thrown away:")
           (lean-server-log "%s" pre)
           (setq lean-global-server-buffer post)
           (setq result (lean-server-process-message-with-cont body type cont cmd-type))
           `(PROCESSED ,result))
          (`nil '(NOTREADY)))
      (error `(ERROR ,err))
      (quit  `(QUIT  ,err)))))

(defun lean-server-async-task-queue-len ()
  (length lean-global-async-task-queue))

(defun lean-server-async-task-queue-push-back (cont cmd-type)
  (setq lean-global-async-task-queue (-snoc lean-global-async-task-queue
                                            `(,cont . ,cmd-type))))

(defun lean-server-async-task-queue-peek-front ()
  (car lean-global-async-task-queue))

(defun lean-server-async-task-queue-pop-front ()
  (!cdr lean-global-async-task-queue))

(defun lean-server-send-cmd-async (cmd &optional cont)
  "Send cmd to lean-server and attach continuation to the queue."
  (lean-debug "send-cmd-async: %S %S" (lean-cmd-type cmd) (cl-second cmd))
  (lean-debug "send-cmd-async: queue len = %d" (lean-server-async-task-queue-len))
  (lean-server-send-cmd cmd)
  (when cont
    (lean-server-async-task-queue-push-back cont (lean-cmd-type cmd))
    (lean-debug "send-cmd-async: added to %s the queue, queue size = %d"
                       (lean-cmd-type cmd)
                       (lean-server-async-task-queue-len))
    (lean-debug "send-cmd-async: call handler")
    (lean-server-set-timer-for-event-handler)))

(defun lean-server-consume-all-async-tasks ()
  (lean-debug "lean-server-consume-all-async-tasks: queue size = %d"
                     (lean-server-async-task-queue-len))
  (while lean-global-async-task-queue
    (accept-process-output (lean-server-get-process) 0 50 t)
    (let* ((front-item (lean-server-async-task-queue-peek-front))
           (cont       (car front-item))
           (cmd-type   (cdr front-item))
           (result (lean-server-check-and-process-buffer-with-cont cont
                                                                   cmd-type)))
      (pcase result
        (`(PROCESSED ,ret)
         (lean-server-async-task-queue-pop-front)
                  (lean-debug "lean-server-consume-all-sync-tasks: processed. queue size = %d"
                            (lean-server-async-task-queue-len)))
        (`(NOTREADY)
         (lean-debug "lean-server-consume-all-sync-tasks: not ready. queue size = %d"
                            (lean-server-async-task-queue-len)))
        (t
         (lean-server-async-task-queue-pop-front)
         (lean-debug "lean-server-consume-all-sync-tasks: either error or quit happend. queue size = %d"
                            (lean-server-async-task-queue-len))))))
  (lean-debug "lean-server-consume-all-async-tasks: over. queue size = %d"
                     (lean-server-async-task-queue-len)))

(defun lean-server-send-cmd-sync (cmd &optional cont)
  "Send cmd to lean-server (sync)."
  (lean-debug "send-cmd-sync: %S" (lean-cmd-type cmd))
  (lean-server-cancel-retry-timer)
  (lean-server-consume-all-async-tasks)
  (lean-server-send-cmd cmd)
  (let ((result (lean-server-check-and-process-buffer-with-cont cont (lean-cmd-type cmd))))
    (while (equal result '(NOTREADY))
      (accept-process-output (lean-server-get-process) 0 50 t)
      (setq result (lean-server-check-and-process-buffer-with-cont cont (lean-cmd-type cmd))))
    (pcase result
      (`(PROCESSED ,ret)
       (lean-debug "lean-server-send-cmd-sync: %S, processed result = %S"
                          cmd
                          result)
       ret)
      (`(ERROR ,err)
       (lean-debug "lean-server-send-cmd-sync: %S, error = %S"
                          cmd
                          err))
      (`(QUIT ,err)
       (lean-debug "lean-server-send-cmd-sync: %S, quit = %S"
                          cmd
                          err))
      (t
       (lean-debug "lean-server-send-cmd-sync: %S, ??? = %S"
                          cmd
                          result)))))

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

(defun lean-findg-parse-string (str)
  "Parse the output of findg command."
  (let ((str-list (split-string str "\n")))
    ;; Drop the first line "-- BEGINFINDG" and
    ;; the last line "-- ENDFINDG"
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
  (lean-debug "set-timer-for-event-handler")
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
         (column (current-column)))
    (when (and (or (looking-at (rx (or white "," ")" "}" "]")))
                   (eolp))
               (> column 1))
      (setq column (1- column)))
    (lean-info-record-parse body file-name column)))

(defun lean-server-event-handler ()
  "Process an item from async-task-queue.

If it's successful, take it out from the queue.
Otherwise, set an idle-timer to call the handler again"
  (lean-server-cancel-retry-timer)
  (when (eq major-mode 'lean-mode)
    (let* ((front-item (lean-server-async-task-queue-peek-front))
           (cont       (car front-item))
           (cmd-type   (cdr front-item))
           (result     (lean-server-check-and-process-buffer-with-cont cont
                                                                       cmd-type)))
      (pcase result
        (`(PROCESSED ,ret)
         (lean-server-async-task-queue-pop-front)
         (lean-debug "event-handler: processed. now the queue size = %d\n"
                            (lean-server-async-task-queue-len))
         ret)
        (`(NOTREADY)
         (lean-debug "event-handler: not ready. queue size = %d"
                            (lean-server-async-task-queue-len)))
        (`(ERROR ,err)
         (lean-server-async-task-queue-pop-front)
         (lean-debug "event-handler: error %S. queue size = %d"
                            err
                            (lean-server-async-task-queue-len)))
        (`(QUIT ,err)
         (lean-server-async-task-queue-pop-front)
         (lean-debug "event-handler: quit %S. queue size = %d"
                            err
                            (lean-server-async-task-queue-len)))))
    (if lean-global-async-task-queue (lean-server-set-timer-for-event-handler))))

(defun lean-server-after-save ()
  (let ((current-file-name (buffer-file-name)))
    (when current-file-name
      (lean-debug "lean-server-handle-save: %s" current-file-name)
      (lean-server-send-cmd-async (lean-cmd-visit current-file-name)))))

(defun lean-server-save-buffer-to-temp-file (prefix)
  "Save the current buffer to a temp-file and return its path"
  (interactive)
  (let ((temp-file (make-temp-file prefix)))
    (with-current-buffer (flymake-copy-buffer-to-temp-buffer (current-buffer))
      (set-visited-file-name temp-file)
      (save-buffer 0)
      (kill-buffer))
    temp-file))

(defun lean-server-handle-modified-buffer ()
  "Handle modified buffer when lean-mode start"
  (interactive)
  (when (buffer-file-name)
    (let* ((current-file-name (buffer-file-name))
           (current-directory (file-name-directory current-file-name))
           (temp-prefix (concat (file-name-as-directory current-directory)
                                "lean-temp"))
           (temp-file (lean-server-save-buffer-to-temp-file temp-prefix)))
      (lean-debug "lean-server-handle-modified-buffer: %s => %s"
                         current-file-name
                         temp-file)
      (lean-server-send-cmd-async (lean-cmd-visit temp-file))
      (setq lean-global-server-current-file-name current-file-name)
      (lean-server-send-cmd-async (lean-cmd-wait)
                                  (lambda () (delete-file temp-file))))))

(provide 'lean-server)
