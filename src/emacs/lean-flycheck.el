;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;
(require 'flycheck)
(require 'lean-settings)
(require 'lean-server)

(defun lean-toggle-flycheck-mode ()
  "Toggle flycheck-mode"
  (interactive)
  (cond
   (flycheck-mode (flycheck-mode -1))
   (t             (flycheck-mode  1))))

(cl-defun lean-flycheck-parse-error (checker buffer &key pos_line pos_col severity text file_name &allow-other-keys)
  (flycheck-error-new-at pos_line (1+ pos_col)
                         (pcase severity
                           ("error" 'error)
                           ("warning" 'warning)
                           ("information" 'info)
                           (_ 'info))
                         text
                         :filename file_name
                         :checker checker :buffer buffer))

(defun lean-flycheck-start (checker callback)
  (lean-server-sync)
  (lean-server-send-command
   '(:command check)
   (cl-function (lambda (&key messages)
     (let* ((buffer (current-buffer))
            (errors (mapcar (lambda (j) (apply 'lean-flycheck-parse-error checker buffer j))
                            messages)))
       (funcall callback 'finished errors))))
   (cl-function (lambda (&key message)
     (funcall callback 'errored message)))))

(defun lean-flycheck-init ()
  "Initialize lean-flychek checker"
  (flycheck-define-generic-checker 'lean-checker
    "A Lean syntax checker."
    :start #'lean-flycheck-start
    :modes '(lean-mode))
  (add-to-list 'flycheck-checkers 'lean-checker))

(defun lean-flycheck-turn-on ()
  (interactive)
  (unless lean-flycheck-use
    (when (called-interactively-p 'any)
      (message "use flycheck in lean-mode"))
    (setq lean-flycheck-use t))
  (flycheck-mode t))

(defun lean-flycheck-turn-off ()
  (interactive)
  (when lean-flycheck-use
    (when (called-interactively-p 'any)
      (message "no flycheck in lean-mode")))
  (flycheck-mode 0)
  (setq lean-flycheck-use nil))

(defun lean-flycheck-toggle-use ()
  (interactive)
  (if lean-flycheck-use
      (lean-flycheck-turn-off)
    (lean-flycheck-turn-on)))

(defun lean-flycheck-error-list-buffer-width ()
  "Return the width of flycheck-error list buffer"
  (interactive)
  (let* ((flycheck-error-window (get-buffer-window "*Flycheck errors*" t))
         (window                (selected-window))
         (body-width            (window-body-width window)))
    (cond
     ;; If "*Flycheck errors" buffer is available, use its width
     (flycheck-error-window
      (window-body-width flycheck-error-window))
     ;; If lean-flycheck-msg-width is set, use it
     (lean-flycheck-msg-width
      lean-flycheck-msg-width)
     ;; Can we split vertically?
     ((window-splittable-p window nil)
      body-width)
     ;; Can we split horizontally?
     ((window-splittable-p window t)
      (/ body-width 2))
     ;; In worst case, just use the same width of current window
     (t body-width))))

(defun lean-flycheck-error-list-message-width ()
  "Return the width of error messages in the flycheck-error list buffer"
  (let (;; assume 'Message' is last column and has size 0 (true for default config)
        (other-columns-width (apply '+ (mapcar (apply-partially 'nth 1) flycheck-error-list-format)))
        (margin (length flycheck-error-list-format)))
    (cond
     ;; If lean-flycheck-msg-width is set, use it
     (lean-flycheck-msg-width
      lean-flycheck-msg-width)
     (t (- (lean-flycheck-error-list-buffer-width) other-columns-width margin)))))

(defconst lean-next-error-buffer-name "*Lean Next Error*")

(defun lean-next-error-copy ()
  (when (and (equal major-mode 'lean-mode)
             ;; HACK -- princ-ing to another buffer seems to remove the marker
             (not mark-active))

    (let* ((errors (sort (flycheck-overlay-errors-in (line-beginning-position) (line-end-position)) #'flycheck-error-<))
           (buffer (get-buffer lean-next-error-buffer-name))
           ;; output logic taken from with-temp-buffer-window, but don't reset major mode
           (standard-output buffer))

      ;; prefer error of current position, if any
      (-if-let (e (get-char-property (point) 'flycheck-error))
          (setq errors (list e)))

      ;; fall back to next error
      (if (null errors)
          (-if-let* ((pos (flycheck-next-error-pos 1))
                     (e (get-char-property pos 'flycheck-error)))
              (setq errors (list e))))

      (with-current-buffer buffer
        (setq buffer-read-only nil)
        (erase-buffer))

      (if errors
          (dolist (e errors)
            (princ (format "%d:%d: " (flycheck-error-line e) (flycheck-error-column e)))
            (princ (flycheck-error-message e))
            (princ "\n\n"))
        (if flycheck-current-errors
            (princ (format "(%d more messages above...)" (length flycheck-current-errors)))))

      (temp-buffer-window-show buffer))))

(define-minor-mode lean-next-error-mode
  "Toggle lean-next-error-mode on and off.
lean-next-error-mode takes the next error (or all errors of the current line, if any) from
flycheck and shows them in a dedicated buffer set to `lean-info-mode'."
  :group 'lean
  :global t
  (let ((hooks '(flycheck-after-syntax-check-hook post-command-hook)))
    (if lean-next-error-mode
        (progn

          (unless (get-buffer lean-next-error-buffer-name)
            (with-current-buffer (get-buffer-create lean-next-error-buffer-name)
              (lean-info-mode)))

          (dolist (hook hooks)
            (add-hook hook 'lean-next-error-copy))

          (setq lean-next-error-old-display-function flycheck-display-errors-function
                flycheck-display-errors-function nil))

      (setq flycheck-display-errors-function lean-next-error-old-display-function)
      (dolist (hook hooks)
        (remove-hook hook 'lean-next-error-copy)))))

(provide 'lean-flycheck)
