;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'cl-lib)
(require 'dash)
(require 'lean-server)
(require 'lean-debug)

(defvar-local lean-changed-lines nil
  "Changed lines")
(defvar-local lean-removed-lines nil
  "Removed lines")
(defvar-local lean-inserted-lines nil
  "Inserted lines")

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
  (lean-server-check-current-file)
  (setq lean-global-before-change-beg beg)
  (setq lean-global-before-change-end end)
  (setq lean-global-before-change-beg-line-number (line-number-at-pos beg))
  (setq lean-global-before-change-end-line-number (line-number-at-pos end))
  (setq lean-global-before-change-text (buffer-substring-no-properties beg end)))

(defun lean-after-change-diff-lines (before-beg-line-number
                                     before-end-line-number
                                     after-beg-line-number
                                     after-end-line-number)
  "Given before and after (beg-line-number, end-line-number) pairs,
compute changed-lines, inserted-lines, and removed-lines."
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

(defun lean-after-changed-p (before-beg before-end before-text
                             after-beg after-end after-text)
  "Return true if there is a really change"
  (or (/= before-beg after-beg)
      (/= before-end after-end)
      (not (string= before-text after-text))))

(defun lean-after-change-handle-changes-only (changed-lines)
  (cl-loop for n in changed-lines
           do (add-to-list 'lean-changed-lines n)))

(defun lean-after-change-handle-inserted (inserted-lines changed-lines)
  (lean-server-flush-changed-lines)
  (cl-loop for n in inserted-lines
           do (lean-server-send-cmd-async (lean-cmd-insert n (lean-grab-line n))))
  (setq lean-changed-lines changed-lines)
  (lean-server-flush-changed-lines))

(defun lean-after-change-handle-removed (removed-lines changed-lines)
  (lean-server-flush-changed-lines)
  (cl-loop for n in removed-lines
           do (lean-server-send-cmd-async (lean-cmd-remove n)))
  (setq lean-changed-lines changed-lines)
  (lean-server-flush-changed-lines))

(defun lean-after-change-function (beg end leng-before)
  "Function attached to after-change-functions hook"
  (let* ((before-beg lean-global-before-change-beg)
         (before-end lean-global-before-change-end)
         (before-beg-line-number lean-global-before-change-beg-line-number)
         (before-end-line-number lean-global-before-change-end-line-number)
         (after-beg-line-number (line-number-at-pos beg))
         (after-end-line-number (line-number-at-pos end))
         (before-text lean-global-before-change-text)
         (text (buffer-substring-no-properties beg end)))
    (lean-debug "after-change-function")
    (lean-debug "before-text: %s" before-text)
    (lean-debug "after-text: %s"  text)
    (when (lean-after-changed-p before-beg before-end before-text
                                beg end text)
      (pcase (lean-after-change-diff-lines before-beg-line-number before-end-line-number
                                           after-beg-line-number after-end-line-number)
        (`(CHANGE-ONLY ,changed-lines)
         (lean-after-change-handle-changes-only changed-lines))
        (`(INSERT ,inserted-lines ,changed-lines)
         (lean-after-change-handle-inserted inserted-lines changed-lines))
        (`(REMOVE ,removed-lines ,changed-lines)
         (lean-after-change-handle-removed removed-lines changed-lines))))))

(defconst lean-changes-hooks-alist
  '((after-change-functions              . lean-after-change-function)
    (before-change-functions             . lean-before-change-function)))

(defun lean-before-revert ()
  "Remove changes hooks"
  (pcase-dolist (`(,hook . ,fn) lean-changes-hooks-alist)
    (remove-hook hook fn 'local)))

(defun lean-after-revert ()
  "Reset changes variables, add back changes-hooks, load file"
  (setq lean-changed-lines nil)
  (setq lean-removed-lines nil)
  (setq lean-inserted-lines nil)
  (pcase-dolist (`(,hook . ,fn) lean-changes-hooks-alist)
    (add-hook hook fn nil 'local))
  (lean-server-send-cmd-async (lean-cmd-load (buffer-file-name))))

(provide 'lean-changes)
