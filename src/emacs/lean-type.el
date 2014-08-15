;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'lean-variable)
(require 'lean-util)
(require 'lean-cmd)
(require 'lean-server)
(require 'lean-debug)

(defun lean-get-info-list (file-name line-number column)
  "Get info list from lean server using file-name, line-number, and column.

TODO(soonhok): for now, it ignores file-name and column."
  (lean-server-send-cmd (lean-cmd-info line-number))
  (while (not lean-global-info-processed)
    (accept-process-output (lean-server-get-process) 0 50 t))
  lean-global-info-list)

(defun lean-filter-info-list (info-list when-pred)
  "Filter info-list by given when-pred"
  (cl-loop for info in info-list
           when (funcall when-pred info)
           collect info))

(defun lean-get-current-sym-info ()
  "Return the information of current symbol at point.

The return valus has the form of '([symbol-string] [start-pos])"
  (interactive)
  (let ((bound (bounds-of-thing-at-point 'symbol))
        start-pos end-pos sym)
    (cond (bound
           (setq start-pos (car bound))
           (setq end-pos   (cdr bound))
           (setq sym       (buffer-substring-no-properties start-pos end-pos)))
          ((= (point) (point-max))
           (setq start-pos (point))
           (setq sym       ""))
          (t
           (setq start-pos (point))
           (setq sym       (buffer-substring-no-properties start-pos (1+ start-pos)))))
    (list sym start-pos)))

(defun lean-eldoc-argument-list (string)
  "Upcase and fontify STRING for use with `eldoc-mode'."
  (propertize string 'face 'font-lock-variable-name-face))

(defun lean-extract-info-at-pos (file-name line-number column start-pos)

  (let*  ((info-list (lean-get-info-list file-name line-number column))
          (info-list-at-pos (lean-filter-info-list
                             info-list
                             '(lambda (info) (= start-column (lean-info-column info)))))
          (typeinfo
           (cl-first (lean-filter-info-list info-list-at-pos
                                            'lean-typeinfo-p)))
          (overload
           (cl-first (lean-filter-info-list info-list-at-pos
                                            'lean-overload-p)))
          (synth
           (cl-first (lean-filter-info-list info-list-at-pos
                                            'lean-synth-p))))
    (list typeinfo overload synth)))

(defun lean-print-info (typeinfo overload synth sym-name)
  "Given typeinfo, overload, and sym-name, print out information."
  (when typeinfo
    (let* ((overload-names  (lean-overload-names overload))
           (overload-name   (cl-first overload-names))
           (synth-value     (when synth (lean-synth-body-str synth)))
           (name            (or synth-value overload-name sym-name))
           (type-str        (lean-typeinfo-body-str typeinfo))
           (type-output-str
            (format "%s : %s"
                    (propertize name 'face 'font-lock-variable-name-face)
                    type-str))
           (overload-output-str
            (when overload-names
              (format "\n%s with %s"
                      (propertize "overloaded" 'face 'font-lock-keyword-face)
                      (lean-string-join (cdr overload-names) ", "))))
           (output-str (concat type-output-str overload-output-str)))
      (message "%s" output-str))))

(defun lean-fill-placeholder ()
  "Fill the placeholder with a synthesized expression by Lean."
  (interactive)
  (let ((cur_char (buffer-substring-no-properties (point) (1+ (point)))))
    (when (string= cur_char "_")
      (let* ((file-name (buffer-file-name))
             (line-number (line-number-at-pos))
             (column (current-column))
             (sym-info (lean-get-current-sym-info))
             (sym-name (cl-first sym-info))
             (start-pos (cl-second sym-info))
             (start-column (- column (- (point) start-pos)))
             typeinfo overload)
        (cl-multiple-value-setq (typeinfo overload synth)
          (lean-extract-info-at-pos file-name line-number column start-pos))
        (when synth
          (let ((synth-str
                 (replace-regexp-in-string "?M_[0-9]+" "_" (lean-synth-body-str synth))))
            (when (search " " synth-str)
              (setq synth-str (concat "(" synth-str ")")))
            (delete-forward-char 1)
            (insert synth-str)))))))

(defun lean-eldoc-documentation-function ()
  "Show information of lean expression at point if any"
  (interactive)
  (let* ((file-name (buffer-file-name))
         (line-number (line-number-at-pos))
         (column (current-column))
         (sym-info (lean-get-current-sym-info))
         (sym-name (cl-first sym-info))
         (start-pos (cl-second sym-info))
         (start-column (- column (- (point) start-pos)))
         typeinfo overload)
    (cl-multiple-value-setq (typeinfo overload synth)
      (lean-extract-info-at-pos file-name line-number column start-pos))
    (lean-print-info typeinfo overload synth sym-name)))

(defun lean-before-change-function (beg end)
  "Function attached to before-change-functions hook.

It saves the following information to the global variable:

 - lean-global-before-change-beg             : beg
 - lean-global-before-change-end             : end
 - lean-global-before-change-beg-line-number : line-number of beg
 - lean-global-before-change-end-line-number : line-number of end
 - lean-global-before-change-text            : text between beg and end

These information will be used by lean-after-changed-function."
  ;; (message "lean-before-change %d %d" beg end)
  (setq lean-global-before-change-beg beg)
  (setq lean-global-before-change-end end)
  (setq lean-global-before-change-beg-line-number (line-number-at-pos beg))
  (setq lean-global-before-change-end-line-number (line-number-at-pos end))
  (setq lean-global-before-change-text (buffer-substring-no-properties beg end)))

(defun lean-after-change-log (beg end after-beg-line-number after-end-line-number)
  (message "before-change: beg=%d (%d) end=%d (%d)"
           beg lean-global-before-change-beg-line-number
           end lean-global-before-change-end-line-number)
  (message "before-text:||%s||" lean-global-before-change-text)
  (message "before-text # of lines = %d" (count-lines beg end))
  (message "after-change: beg=%d (%d) end=%d (%d) leng-before=%d"
           beg after-beg-line-number end after-end-line-number leng-before)
  (message "after-text:||%s||" (buffer-substring-no-properties beg end))
  (message "after-text # of lines = %d" (count-lines beg end))
  (message "changed  lines = %s" (prin1-to-string changed-lines))
  (message "inserted lines = %s" (prin1-to-string inserted-lines))
  (message "removed lines  = %s" (prin1-to-string removed-lines))
  (message "===================================="))

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
    ;; (lean-debug-print "old-lines" old-lines)
    ;; (lean-debug-print "new-lines" new-lines)
    (cond ((= old-lines-len new-lines-len)
           (setq changed-lines old-lines)
           ;; (lean-debug-print "changed" changed-lines)
           `(CHANGE-ONLY ,changed-lines))
          ;; Case "REMOVE"
          ((> old-lines-len new-lines-len)
           (setq removed-lines (lean-take-first-n old-lines (- old-lines-len new-lines-len)))
           ;; Make sure that we return it in reverse order
           (setq removed-lines (cl-sort removed-lines '>))
           (setq changed-lines new-lines)
           `(REMOVE ,removed-lines ,changed-lines))
          ;; Case "INSERT"
          ((< old-lines-len new-lines-len)
           (setq inserted-lines (lean-take-last-n new-lines (- new-lines-len old-lines-len)))
           ;; Make sure that we return it in sorted order
           (setq inserted-lines (cl-sort inserted-lines '<))
           (setq changed-lines old-lines)
           ;; (lean-debug-print "inserted-lines" inserted-lines)
           ;; (lean-debug-print "changed-lines" changed-lines)
           `(INSERT ,inserted-lines ,changed-lines)))))

(defun lean-after-changed-p (before-beg
                             before-end
                             after-beg
                             after-end
                             before-text
                             after-text)
  "Return true if there is a really change"
  (or (/= before-beg after-beg)
      (/= before-end after-end)
      (not (string= before-text after-text))))

(defun lean-after-change-handle-changes-only (changed-lines)
  (cl-loop for n in changed-lines
           do (add-to-list 'lean-changed-lines n))
  ;; (lean-debug-print "changes-only" lean-changed-lines)
  )

(defun lean-after-change-handle-inserted (inserted-lines changed-lines)
  ;; (lean-debug-print "inserted lines" (cons inserted-lines changed-lines))
  (lean-flush-changed-lines)
  (cl-loop for n in inserted-lines
           do (lean-server-send-cmd (lean-cmd-insert n (lean-grab-line n))))
  (setq lean-changed-lines changed-lines)
  (lean-flush-changed-lines))

(defun lean-after-change-handle-removed (removed-lines changed-lines)
  ;; (lean-debug-print "removed lines" (cons removed-lines changed-lines))
  (lean-flush-changed-lines)
  (cl-loop for n in removed-lines
           do (lean-server-send-cmd (lean-cmd-remove n)))
  (setq lean-changed-lines changed-lines)
  (lean-flush-changed-lines))

(defun lean-after-change-function (beg end leng-before)
  "Function attached to after-change-functions hook"
  ;; (message "lean-after-change-function: %d %d %d" beg end leng-before)
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
