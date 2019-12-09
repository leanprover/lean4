;; -*- lexical-binding: t; -*-
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Authors: Soonho Kong, Sebastian Ullrich
;;

(require 'cl-lib)
(require 'dash)
(require 'dash-functional)
(require 's)
(require 'lean4-util)
;(require 'lean4-server)
(require 'lean4-debug)
(require 'flymake)

(defun lean4-fill-placeholder-cont (info-record)
  "Continuation for lean4-fill-placeholder"
  (let ((synth (and info-record (plist-get info-record :synth))))
    (when synth
      (let ((synth-str
             (replace-regexp-in-string "?M_[0-9]+" "_" synth)))
        (when (cl-search " " synth-str)
          (setq synth-str (concat "(" synth-str ")")))
        (when (looking-at "_")
          (delete-char 1)
          (insert synth-str))))))

(defun lean4-fill-placeholder ()
  "Fill the placeholder with a synthesized expression by Lean."
  (interactive)
  (lean4-get-info-record-at-point 'lean4-fill-placeholder-cont))

(cl-defun lean4-info-record-to-string (info-record)
  "Given typeinfo, overload, and sym-name, compose information as a string."
  (destructuring-bind (&key type tactic_params tactic_param_idx text doc full-id &allow-other-keys) info-record
    (let ((name-str (or full-id text))
          (type-str type)
          str)
      (when tactic_params
        (setq tactic_params (-map-indexed (lambda (i param)
                                            (if (eq i tactic_param_idx)
                                                (propertize param 'face 'eldoc-highlight-function-argument)
                                              param)) tactic_params))
        (setq type-str (mapconcat 'identity tactic_params " ")))

      (when (and name-str type-str)
        (setq str (format (if tactic_params "%s %s" "%s : %s")
                          (propertize name-str 'face 'font-lock-variable-name-face)
                          type-str)))
      (when doc
        (let* ((lines (split-string doc "\n"))
               (doc (if (cdr lines)
                        (concat (car lines) " ⋯")
                      (car lines))))
          (setq str (concat str
                            (format "\n%s"
                                    (propertize doc 'face 'font-lock-comment-face))))))
      str)))

(defvar-local lean4-eldoc-documentation-cache nil)

(defun lean4-eldoc-documentation-function-cont (info-record &optional add-to-kill-ring)
  "Continuation for lean4-eldoc-documentation-function"
  (let ((info-string (and info-record (lean4-info-record-to-string info-record))))
    (when info-string
      (when add-to-kill-ring
        (kill-new
         (substring-no-properties info-string))))
    (setq lean4-eldoc-documentation-cache (and info-string (format "%s" info-string)))
    (eldoc-message lean4-eldoc-documentation-cache)))

(defun lean4-eldoc-documentation-function (&optional add-to-kill-ring)
  "Show information of lean expression at point if any"
  (interactive)
  (when (not (eq lean4-server-check-mode 'nothing)) ; TODO(gabriel): revisit once info no longer reparses the file
    (lean4-get-info-record-at-point
     (lambda (info-record)
       (lean4-eldoc-documentation-function-cont info-record add-to-kill-ring)))
    lean4-eldoc-documentation-cache))

(defun lean4-show-type ()
  "Show information of lean4-expression at point if any."
  (interactive)
  (lean4-eldoc-documentation-function lean4-show-type-add-to-kill-ring))

(defconst lean4-show-goal-buffer-name "*Lean Goal*")

(setq lean4-show-goal--handler-mask nil)

(defun lean4-show-goal--handler ()
  (if lean4-show-goal--handler-mask
      (setq lean4-show-goal--handler-mask nil)
    (let ((deactivate-mark)) ; keep transient mark
      (when (and (not (eq lean4-server-check-mode 'nothing))
					; TODO(gabriel): revisit ^^ once info no longer reparses the file
		 (lean4-info-buffer-active lean4-show-goal-buffer-name))
	(lean4-get-info-record-at-point
	 (lambda (info-record)
	   (let ((state (plist-get info-record :state)))
	     (unless (or (s-blank? state) (s-blank? (s-trim state)))
	       (lean4-with-info-output-to-buffer lean4-show-goal-buffer-name (princ state))))))))))

(defun lean4-toggle-show-goal ()
  "Show goal at the current point."
  (interactive)
  (lean4-toggle-info-buffer lean4-show-goal-buffer-name)
  (lean4-show-goal--handler))

(provide 'lean4-type)
