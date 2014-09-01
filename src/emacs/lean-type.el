;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'dash)
(require 'dash-functional)
(require 'lean-variable)
(require 'lean-util)
(require 'lean-cmd)
(require 'lean-server)
(require 'lean-debug)
(require 'flymake)

(defun lean-fill-placeholder ()
  "Fill the placeholder with a synthesized expression by Lean."
  (interactive)
  (let* ((info-record (lean-get-info-record-at-point))
         (synth (and info-record (cl-first (lean-info-record-synth info-record)))))
    (when synth
      (let ((synth-str
             (replace-regexp-in-string "?M_[0-9]+" "_" (lean-info-synth-body-str synth))))
        (when (search " " synth-str)
          (setq synth-str (concat "(" synth-str ")")))
        (delete-forward-char 1)
        (insert synth-str)))))

(defun lean-eldoc-documentation-function ()
  "Show information of lean expression at point if any"
  (interactive)
  (when (timerp lean-global-nay-retry-timer)
    (cancel-timer lean-global-nay-retry-timer)
    (setq lean-global-nay-retry-timer nil))
  (let ((info-record (lean-get-info-record-at-point))
        info-string)
    (cond
     ((and info-record (lean-info-record-nay info-record))
      (setq lean-global-nay-retry-timer
            (run-with-idle-timer
             (if (current-idle-time)
                 (time-add (seconds-to-time lean-eldoc-nay-retry-time) (current-idle-time))
               lean-eldoc-nay-retry-time)
             nil
             'lean-eldoc-documentation-function))
      nil)
     (info-record
      (setq info-string (lean-info-record-to-string info-record))
      (when info-string
        (message "%s" info-string))))))

;; =======================================================
;; eval
;; =======================================================

(defun lean-eval-parse-string (str)
  "Parse the output of eval command."
  (let ((str-list (split-string str "\n")))
    ;; Drop the first line "-- BEGINEVAL" and
    ;; the last line "-- ENDEVAL"
    (setq str-list
          (-take (- (length str-list) 2)
                 (-drop 1 str-list)))
    (string-join str-list "\n")))

(defun lean-eval-cmd (lean-cmd)
  "Evaluate lean command."
  (interactive "sLean CMD: ")
  (lean-server-send-cmd (lean-cmd-eval lean-cmd))
  (while (not lean-global-server-message-to-process)
    (accept-process-output (lean-server-get-process) 0 50 t))
  (pcase lean-global-server-message-to-process
    (`(EVAL ,pre ,body)
     (lean-server-log "The following pre-message will be thrown away:")
     (lean-server-log "%s" pre)
     (setq lean-global-server-message-to-process nil)
     (message "%s" (lean-eval-parse-string body)))
    (`(,type ,pre , body)
     (lean-server-log "The following pre-message will be thrown away:")
     (lean-server-log "%s" pre)
     (lean-server-log "Something other than EVAL detected: %S" type)
     (setq lean-global-server-message-to-process nil))))

;; =======================================================
;; Change Handling
;; =======================================================

(defun lean-before-change-function (beg end)
  "Function attached to before-change-functions hook.

It saves the following information to the global variable:

 - lean-global-before-change-beg             : beg
 - lean-global-before-change-end             : end
 - lean-global-before-change-beg-line-number : line-number of beg
 - lean-global-before-change-end-line-number : line-number of end
 - lean-global-before-change-text            : text between beg and end

These information will be used by lean-after-changed-function."
  (lean-server-get-process)
  (setq lean-global-before-change-beg beg)
  (setq lean-global-before-change-end end)
  (setq lean-global-before-change-beg-line-number (line-number-at-pos beg))
  (setq lean-global-before-change-end-line-number (line-number-at-pos end))
  (setq lean-global-before-change-text (buffer-substring-no-properties beg end)))

(defun lean-after-change-diff-lines (before-beg-line-number
                                     before-end-line-number
                                     after-beg-line-number
                                     after-end-line-number)
  "Given before and after (beg-line-number, end-line-number)
pairs, compute changed-lines, inserted-lines, and removed-lines."
  (let* ((old-lines (cl-loop for n from before-beg-line-number to before-end-line-number
                             collect n))
         (new-lines (cl-loop for n from after-beg-line-number to after-end-line-number
                             collect n))
         (old-lines-len (length old-lines))
         (new-lines-len (length new-lines))
         changed-lines removed-lines inserted-lines)
    (cond ((= old-lines-len new-lines-len)
           (setq changed-lines old-lines)
           `(CHANGE-ONLY ,changed-lines))
          ;; Case "REMOVE"
          ((> old-lines-len new-lines-len)
           (setq removed-lines (-take (- old-lines-len new-lines-len) old-lines))
           ;; Make sure that we return it in reverse order
           (setq removed-lines (cl-sort removed-lines '>))
           (setq changed-lines new-lines)
           `(REMOVE ,removed-lines ,changed-lines))
          ;; Case "INSERT"
          ((< old-lines-len new-lines-len)
           (setq inserted-lines (-drop old-lines-len new-lines))
           ;; Make sure that we return it in sorted order
           (setq inserted-lines (cl-sort inserted-lines '<))
           (setq changed-lines old-lines)
           `(INSERT ,inserted-lines ,changed-lines)))))

(defun lean-after-changed-p (before-beg before-end after-beg after-end
                                        before-text after-text)
  "Return true if there is a really change"
  (or (/= before-beg after-beg)
      (/= before-end after-end)
      (not (string= before-text after-text))))

(defun lean-after-change-handle-changes-only (changed-lines)
  (cl-loop for n in changed-lines
           do (add-to-list 'lean-changed-lines n)))

(defun lean-after-change-handle-inserted (inserted-lines changed-lines)
  (lean-flush-changed-lines)
  (cl-loop for n in inserted-lines
           do (lean-server-send-cmd (lean-cmd-insert n (lean-grab-line n))))
  (setq lean-changed-lines changed-lines)
  (lean-flush-changed-lines))

(defun lean-after-change-handle-removed (removed-lines changed-lines)
  (lean-flush-changed-lines)
  (cl-loop for n in removed-lines
           do (lean-server-send-cmd (lean-cmd-remove n)))
  (setq lean-changed-lines changed-lines)
  (lean-flush-changed-lines))

(defun lean-after-change-function (beg end leng-before)
  "Function attached to after-change-functions hook"
  (let* ((before-beg lean-global-before-change-beg)
         (before-end lean-global-before-change-end)
         (before-beg-line-number lean-global-before-change-beg-line-number)
         (before-end-line-number lean-global-before-change-end-line-number)
         (after-beg-line-number (line-number-at-pos beg))
         (after-end-line-number (line-number-at-pos end))
         (before-text lean-global-before-change-text)
         (after-text (buffer-substring-no-properties beg end)))
    (when (lean-after-changed-p before-beg before-end beg end before-text after-text)
      (pcase (lean-after-change-diff-lines before-beg-line-number before-end-line-number
                                           after-beg-line-number after-end-line-number)
        (`(CHANGE-ONLY ,changed-lines)
         (lean-after-change-handle-changes-only changed-lines))
        (`(INSERT ,inserted-lines ,changed-lines)
         (lean-after-change-handle-inserted inserted-lines changed-lines))
        (`(REMOVE ,removed-lines ,changed-lines)
         (lean-after-change-handle-removed removed-lines changed-lines))))))

(provide 'lean-type)
