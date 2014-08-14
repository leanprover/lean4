;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'lean-variable)
(require 'lean-cmd)
(require 'lean-info)
(require 'lean-util)

;; Parameters
;; ==========
(defvar-local lean-server-process-name "lean-server")
(defvar-local lean-server-buffer-name  "*lean-server*")
(defvar-local lean-server-option       "--server")

;; How to read data from an async process
;; ======================================
(defun lean-server-has-error-p (buf-str)
  "Return true if a buffer-string has --ERROR"
  (lean-string-contains-line-p buf-str "-- ERROR"))

(defun lean-server-ready-to-process-p (buf-str)
  "Return true if a buffer-string is ready to process"
  (lean-string-contains-line-p buf-str "-- ENDINFO"))

(defun lean-server-cut-prefix (buf-str prefix)
  "Cut prefix from the string"
  (cond ((string-prefix-p prefix buf-str)
         (substring-no-properties buf-str (length prefix)))
        (t
         (let* ((new-prefix (concat "\n" prefix))
                (beg-pos    (search new-prefix buf-str))
                (len        (length new-prefix)))
           (when (not beg-pos)
             error (concat prefix " is not found in buf-str " buf-str))
           (substring-no-properties buf-str (+ beg-pos len))))))

;; -- Test
(cl-assert (string= (lean-server-cut-prefix "-- BEGININFO\nblablabla" "-- BEGININFO\n")
                    "blablabla"))
(cl-assert (string= (lean-server-cut-prefix "line1\nline2\n-- BEGININFO\nblablabla" "-- BEGININFO\n")
                    "blablabla"))


(defun lean-server-process-received-message (buf str)
  "Process received message from lean-server"
  (setq lean-global-info-buffer (concat lean-global-info-buffer str))
  (with-current-buffer buf
    (goto-char (point-max))
    (insert "Received String:\n")
    (insert str)
    (insert "\n------------------\n")
    (goto-char (point-max)))
  (cond ((lean-server-ready-to-process-p lean-global-info-buffer)
         (setq lean-global-info-buffer (lean-server-cut-prefix lean-global-info-buffer "-- BEGININFO\n"))
         (setq lean-global-info-list (lean-infolist-parse lean-global-info-buffer))
         (setq lean-global-info-processed t)
         ;; clear lean-global-info-buffer after processing
         (setq lean-global-info-buffer "")
         (with-current-buffer buf
           (goto-char (point-max))
           (prin1 lean-global-info-list buf)
           (insert "\n=============================\n")))
        ((lean-server-has-error-p lean-global-info-buffer)
         (setq lean-global-info-processed t)
         ;; clear lean-global-info-buffer after processing
         (setq lean-global-info-buffer "")
         (with-current-buffer buf
           (goto-char (point-max))
           (insert "Error Detected\n")
           (insert "=============================\n")))))

(defun lean-server-output-filter (process string)
  "Filter function attached to lean-server process"
  (lean-server-process-received-message (process-buffer process) string))

;; How to create an async process
;; ==============================
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
    (setq lean-global-info-buffer "")
    (setq lean-global-server-current-file-name "")
    (with-current-buffer (process-buffer lean-server-process)
      (goto-char (point-max))
      (insert "Server Created.\n")
      (insert lean-global-server-current-file-name))
    lean-server-process))

(defun lean-server-kill-process ()
  "Kill lean-server process."
  (interactive)
  (let ((proc (get-process lean-server-process-name)))
    (when proc
      (with-current-buffer (process-buffer proc)
        (goto-char (point-max))
        (insert "Server Killed.\n")
        (setq lean-global-server-current-file-name nil))
      (kill-process proc))))

(defun lean-server-restart-process ()
  "Restart lean-server process."
  (interactive)
  (lean-server-kill-process)
  (lean-server-create-process))

(defun lean-server-get-process ()
  "Get lean-server process. If needed, create a one."
  (let ((proc (get-process lean-server-process-name)))
    (cond ((not proc) (lean-server-create-process))
          ((not (process-live-p proc)) (error "TODO(soonhok): need to kill and recreate one"))
          (t proc))))

(defun lean-server-get-buffer ()
  "Get lean-server buffer."
  (process-buffer (lean-server-get-process)))

;; How to send data to an async process
;; ====================================
(defun lean-flush-changed-lines ()
  "Flush lean-changed-lines.

Send REPLACE commands to lean-server, reset lean-changed-lines to nil."
  (cl-loop for n in lean-changed-lines
           do (lean-server-send-cmd (lean-cmd-replace n (lean-grab-line n)))
           finally (setq lean-changed-lines nil)))

(defun lean-server-check-current-file ()
  "Check lean-global-server-current-file-name.

If it's not the same with (buffer-file-name), send VISIT cmd."
  (let ((current-file-name (buffer-file-name)))
    (unless (string= lean-global-server-current-file-name
                     current-file-name)
      (lean-server-send-cmd (lean-cmd-visit current-file-name)))))

(defun lean-server-before-send-cmd (cmd)
  "Operations to perform before sending a command."
  (cl-case (lean-cmd-type cmd)
    ('LOAD    ())
    ('VISIT   ())
    ('REPLACE (lean-server-check-current-file))
    ('INSERT  (lean-server-check-current-file))
    ('REMOVE  (lean-server-check-current-file))
    ('INFO    (lean-server-check-current-file)
              (lean-flush-changed-lines)
              (setq lean-global-info-processed nil)
              (setq lean-global-info-buffer ""))
    ('CHECK   (lean-server-check-current-file))))

(defun lean-server-after-send-cmd (cmd)
  "Operations to perform after sending a command."
  (cl-case (lean-cmd-type cmd)
    ('LOAD    (setq lean-global-server-current-file-name
                    (lean-cmd-load-get-file-name cmd)))
    ('VISIT   (setq lean-global-server-current-file-name
                    (lean-cmd-visit-get-file-name cmd)))
    ('REPLACE ())
    ('INSERT  ())
    ('REMOVE  ())
    ('INFO    ())
    ('CHECK   ())))

(defun lean-server-send-cmd (cmd)
  "Send string to lean-server."
  (let ((proc (lean-server-get-process))
        (string-to-send (concat (lean-cmd-to-string cmd) "\n")))
    (lean-server-before-send-cmd cmd)
    ;; Logging
    (with-current-buffer (lean-server-get-buffer)
      (goto-char (point-max))
      (insert "Send\n===========\n")
      (insert string-to-send)
      (insert "==========\n"))
    (process-send-string proc string-to-send))
  (lean-server-after-send-cmd cmd))

(provide 'lean-server)
