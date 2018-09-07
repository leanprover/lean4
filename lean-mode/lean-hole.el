;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2017 David Christiansen.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: David Christiansen
;;
;;; Commentary:
;; This is an interface to Lean's support for holes.
;;
;; The interface consists of two components: the hole command, which
;; collects the list of completions and the message, and a handler,
;; which selects a completion.
;;
;; For now, the only handler uses completing-read, but handlers using
;; helm or company's interface would be a good addition.
;;
;;; Code:
(require 'lean-server)

(defun lean-hole-handler-completing-read (alternatives)
  "Pick a hole replacement from ALTERNATIVES with `completing-read'."
  (let* ((choices (cl-loop for alt in alternatives
                           collect (cons (concat (plist-get alt :code)
                                                 " — "
                                                 (plist-get alt :description))
                                         (plist-get alt :code))))
         (selection (let ((this-command 'lean-hole))
                      (completing-read
                       "Response: "
                       choices
                       nil t nil nil nil t)))
         (code (assoc selection choices)))
    (if code
        (cdr code)
      (error "Didn't select a hole completion"))))

(defvar lean-hole-handler-function 'lean-hole-handler-completing-read)

(defun lean-hole--line-col->pos (line col)
  "Compute the position corresponding to LINE and COL."
  (save-restriction
    (widen)
    (save-excursion
      (goto-char (point-min))
      (forward-line (1- line))
      (forward-char col)
      (point))))

(defun lean-hole ()
  "Ask Lean for a list of holes, then ask the user which to use."
  (interactive)
  (with-demoted-errors "lean hole: %s"
    (lean-server-send-command
     'hole_commands (list :file_name (buffer-file-name)
                          :line (line-number-at-pos)
                          :column (lean-line-offset))
     (cl-function
      (lambda (&key start end results)
        (let ((start-pos (lean-hole--line-col->pos (plist-get start :line)
                                                   (plist-get start :column)))
              (end-pos (lean-hole--line-col->pos (plist-get end :line)
                                                 (plist-get end :column))))
          (let ((start-marker (make-marker))
                (end-marker (make-marker)))
            (set-marker start-marker start-pos (current-buffer))
            (set-marker end-marker end-pos (current-buffer))
            (let* ((choices
                    (cl-loop for res in results
                             collect (cons (concat (plist-get res :name)
                                                   " — "
                                                   (plist-get res :description))
                                           (plist-get res :name))))
                   (selection (let ((this-command 'lean-hole))
                                (completing-read
                                 "Hole command: "
                                 choices
                                 nil t nil nil nil t)))
                   (code (assoc selection choices)))
              (if code
                  (lean-hole--command (cdr code) start-marker end-marker)
                (error "Didn't select a hole completion"))))))))))

;; This uses markers to ensure that if the hole moves while the
;; command is running, it is still updated.
(defun lean-hole--command (command start-marker end-marker)
  "Execute COMMAND in the hole between START-MARKER and END-MARKER."
  (interactive)
  (with-demoted-errors "lean hole: %s"
    (lean-server-send-command
     'hole (list :action command
                 :file_name (buffer-file-name)
                 :line (line-number-at-pos start-marker)
                 :column (lean-line-offset start-marker))
     (cl-function
      (lambda (&key message replacements)
        (let ((replacement-count (length (plist-get replacements :alternatives))))
          (let ((selected-code
                 (cond ((= replacement-count 0)
                        nil)
                       ((= replacement-count 1)
                        (plist-get (car (plist-get replacements :alternatives)) :code))
                       (t
                        (lean-hole-handler-completing-read
                         (plist-get replacements :alternatives))))))
            (when selected-code
              (save-excursion
                (goto-char start-marker)
                (delete-region start-marker end-marker)
                (insert selected-code)))))
        (when message
          (message "%s" (s-trim message)))
        (set-marker start-marker nil)
        (set-marker end-marker nil))))))

(defun lean-hole-right-click ()
  "Ask Lean for a list of hole commands, then ask the user which to use."
  (interactive)
  (let ((buf (current-buffer)))
    (ignore-errors
      (list
       'hole_commands
       (list :file_name (buffer-file-name)
             :line (line-number-at-pos)
             :column (lean-line-offset))
       (cl-function
        (lambda (&key start end results)
          (when (and start end)
            (with-current-buffer buf
              (let ((start-pos (lean-hole--line-col->pos (plist-get start :line)
                                                         (plist-get start :column)))
                    (end-pos (lean-hole--line-col->pos (plist-get end :line)
                                                       (plist-get end :column))))
                (let ((start-marker (make-marker))
                      (end-marker (make-marker)))
                  (set-marker start-marker start-pos (current-buffer))
                  (set-marker end-marker (1+ end-pos) (current-buffer))
                  (mapcar (lambda (res)
                            (let ((item-name (plist-get res :name))
                                  (item-desc (plist-get res :description)))
                              (list :name
                                    (concat item-name " — " item-desc)
                                    :action
                                    (lambda ()
                                      (lean-hole--command
                                       item-name
                                       start-marker end-marker)))))
                          results)))))))))))

(provide 'lean-hole)
;;; lean-hole.el ends here
