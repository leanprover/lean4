;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'company)
(require 'company-etags)
(require 'dash)
(require 'dash-functional)
(require 'lean-tags)
(require 'lean-server)

(defun company-lean-hook ()
  (set (make-local-variable 'company-backends) '(company-lean))
  (setq-local company-tooltip-limit 20)                      ; bigger popup window
  (setq-local company-idle-delay .3)                         ; decrease delay before autocompletion popup shows
  (setq-local company-echo-delay 0)                          ; remove annoying blinking
  (setq-local company-begin-commands '(self-insert-command)) ; start autocompletion only after typing
  (company-mode t))

(defun company-lean--prefix ()
  "Returns the symbol to complete. Also, if point is on a dot,
triggers a completion immediately."
  (let ((prefix (company-grab-symbol)))
    (when (or
           (> (length prefix) 3)
           (string-match "[_.]" prefix))
      prefix)))

(defun company-lean--make-candidate (arg)
  (propertize (car arg) 'type (cdr arg)))

(defun company-lean--candidates (prefix)
  (let ((line-number (line-number-at-pos)))
    (lean-server-send-cmd-sync (lean-cmd-findp line-number prefix)
                               (lambda (candidates)
                                 (-map 'company-lean--make-candidate candidates)))))

(defun company-lean--location (arg)
  (lean-generate-tags)
  (let ((tags-table-list (company-etags-buffer-table)))
    (when (fboundp 'find-tag-noselect)
      (save-excursion
        (let ((buffer (find-tag-noselect arg)))
          (cons buffer (with-current-buffer buffer (point))))))))

(defun company-lean--annotation (candidate)
  (let ((type (get-text-property 0 'type candidate)))
    (when type
      (format " : %s" type))))

;;;###autoload
(defun company-lean (command &optional arg &rest ignored)
  (case command
    (prefix (company-lean--prefix))
    (candidates (company-lean--candidates arg))
    (annotation (company-lean--annotation arg))
    (location (company-lean--location arg))
    (sorted t)))

(provide 'lean-company)
