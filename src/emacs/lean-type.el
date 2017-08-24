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
(require 'lean-util)
(require 'lean-server)
(require 'lean-debug)
(require 'flymake)

(defun lean-toggle-eldoc-mode ()
  "Toggle eldoc-mode"
  (interactive)
  (cond
   (eldoc-mode (eldoc-mode -1))
   (t          (eldoc-mode  1))))

(defun lean-fill-placeholder-cont (info-record)
  "Continuation for lean-fill-placeholder"
  (let ((synth (and info-record (plist-get info-record :synth))))
    (when synth
      (let ((synth-str
             (replace-regexp-in-string "?M_[0-9]+" "_" synth)))
        (when (cl-search " " synth-str)
          (setq synth-str (concat "(" synth-str ")")))
        (when (looking-at "_")
          (delete-forward-char 1)
          (insert synth-str))))))

(defun lean-fill-placeholder ()
  "Fill the placeholder with a synthesized expression by Lean."
  (interactive)
  (lean-get-info-record-at-point 'lean-fill-placeholder-cont))

(cl-defun lean-info-record-to-string (info-record)
  "Given typeinfo, overload, and sym-name, compose information as a string."
  (destructuring-bind (&key type tactic_params tactic_param_idx text doc overloads synth coercion proofstate full-id symbol extra &allow-other-keys) info-record
    (let (name-str type-str coercion-str extra-str proofstate-str overload-str stale-str str)
      (setq name-str
            (cond
             (synth synth)
             ((and full-id symbol)
              (format "[%s] %s" symbol full-id))
             (t (or full-id text symbol))))
      (when coercion
        (destructuring-bind (&key expr type) coercion
          (setq coercion-str
                (format "%s : %s"
                        (propertize expr 'face 'font-lock-variable-name-face)
                        type))))
      (when type
        (setq type-str type))
      (when tactic_params
        (setq tactic_params (-map-indexed (lambda (i param)
                                            (if (eq i tactic_param_idx)
                                                (propertize param 'face 'eldoc-highlight-function-argument)
                                              param)) tactic_params))
        (setq type-str (mapconcat 'identity tactic_params " ")))

      (when overloads
        (setq overload-str (s-join ", " overloads)))
      (when extra
        (destructuring-bind (&key expr type) extra
          (setq str
                (cond (lean-show-only-type-in-parens (format ": %s" type))
                      (t (format "(%s) : %s"
                                 (propertize expr 'face 'font-lock-variable-name-face)
                                 type))))))
      (when (and name-str type-str)
        (setq str (format (if tactic_params "%s %s" "%s : %s")
                          (propertize name-str 'face 'font-lock-variable-name-face)
                          type-str)))
      (when (and str coercion-str)
        (setq str (format "%s\n%s %s"
                          str
                          (propertize "coercion applied" 'face 'font-lock-keyword-face)
                          coercion-str)))
      (when overload-str
        (setq str (concat str
                          (format "\n%s with %s"
                                  (propertize "overloaded" 'face 'font-lock-keyword-face)
                                  overload-str))))
      (when proofstate
        (setq str proofstate))
      (when doc
        (let* ((lines (split-string doc "\n"))
               (doc (if (cdr lines)
                        (concat (car lines) " ⋯")
                      (car lines))))
          (setq str (concat str
                            (format "\n%s"
                                    (propertize doc 'face 'font-lock-comment-face))))))
      str)))

(defvar-local lean-eldoc-documentation-cache nil)

(defun lean-eldoc-documentation-function-cont (info-record &optional add-to-kill-ring)
  "Continuation for lean-eldoc-documentation-function"
  (let ((info-string (and info-record (lean-info-record-to-string info-record))))
    (when info-string
      (when add-to-kill-ring
        (kill-new
         (substring-no-properties info-string))))
    (setq lean-eldoc-documentation-cache (and info-string (format "%s" info-string)))
    (eldoc-message lean-eldoc-documentation-cache)))

(defun lean-eldoc-documentation-function (&optional add-to-kill-ring)
  "Show information of lean expression at point if any"
  (interactive)
  (when (not (eq lean-server-check-mode 'nothing)) ; TODO(gabriel): revisit once info no longer reparses the file
    (lean-get-info-record-at-point
     (lambda (info-record)
       (lean-eldoc-documentation-function-cont info-record add-to-kill-ring)))
    lean-eldoc-documentation-cache))

(defun lean-show-type ()
  "Show information of lean-expression at point if any."
  (interactive)
  (lean-eldoc-documentation-function lean-show-type-add-to-kill-ring))

(defconst lean-show-goal-buffer-name "*Lean Goal*")

(defun lean-show-goal--handler ()
  (let ((deactivate-mark)) ; keep transient mark
    (when (and (not (eq lean-server-check-mode 'nothing))
               ; TODO(gabriel): revisit ^^ once info no longer reparses the file
               (lean-info-buffer-active lean-show-goal-buffer-name))
      (lean-get-info-record-at-point
       (lambda (info-record)
         (let ((state (plist-get info-record :state)))
           (unless (or (s-blank? state) (s-blank? (s-trim state)))
             (lean-with-info-output-to-buffer lean-show-goal-buffer-name (princ state)))))))))

(defun lean-toggle-show-goal ()
  "Show goal at the current point."
  (interactive)
  (lean-toggle-info-buffer lean-show-goal-buffer-name)
  (lean-show-goal--handler))

(defun lean-helm-definitions-format-candidate (c)
  `(,(format "%s : %s %s"
             (propertize (plist-get c :text) 'face font-lock-variable-name-face)
             (plist-get c :type)
             (propertize (plist-get (plist-get c :source) :file) 'face font-lock-comment-face))
    . ,c))

(defun lean-helm-definitions-candidates ()
  (with-helm-current-buffer
    (let* ((response (lean-server-send-synchronous-command 'search (list :query helm-pattern)))
           (results (plist-get response :results))
           (results (-filter (lambda (c) (plist-get c :source)) results))
           (candidates (-map 'lean-helm-definitions-format-candidate results)))
      candidates)))

(defun lean-helm-definitions ()
  "Open a 'helm' interface for searching Lean definitions."
  (interactive)
  (require 'helm)
  (helm :sources (helm-build-sync-source "helm-source-lean-definitions"
                   :requires-pattern t
                   :candidates 'lean-helm-definitions-candidates
                   :volatile t
                   :match 'identity
                   :action '(("Go to" . (lambda (c) (with-helm-current-buffer
                                                      (apply 'lean-find-definition-cont (plist-get c :source)))))))
        :buffer "*helm Lean definitions*"))

(provide 'lean-type)
