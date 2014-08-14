;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'lean-settings)

(defvar lean-flycheck-initialized nil
  "Return true if lean-flycheck has been initialized")

(defun lean-flycheck-command ()
  (cl-concatenate 'list
                  `(,(lean-get-executable lean-flycheck-checker-name))
                  lean-flycheck-checker-options
                  '("--")
                  '(source-inplace)))

(defun lean-flycheck-init ()
  "Initialize lean-flychek checker"
  (unless lean-flycheck-initialized
    (require 'flycheck)
    (eval
     `(flycheck-define-checker lean-checker-file
        "A Lean syntax checker (file)."
        :command ,(lean-flycheck-command)
        :error-patterns
        ((error line-start "FLYCHECK_BEGIN ERROR\n"
                (file-name) ":" line ":" column  ": error: "
                (minimal-match
                 (message (one-or-more (one-or-more not-newline) "\n") ))
                "FLYCHECK_END" line-end)
         (warning line-start "FLYCHECK_BEGIN WARNING\n"
                  (file-name) ":" line ":" column  ": warning "
                  (minimal-match
                   (message (one-or-more (one-or-more not-newline) "\n") ))
                  "FLYCHECK_END" line-end))
        :modes (lean-mode)
        :predicate
        (lambda () (and buffer-file-name
                   (string= "lean" (file-name-extension buffer-file-name))))))
    (add-to-list 'flycheck-checkers 'lean-checker-file)
    (setq lean-flycheck-initialized t)))

(defun lean-flycheck-turn-on ()
  (interactive)
  (unless lean-flycheck-use
    (when (interactive-p)
      (message "use flycheck in lean-mode"))
    (setq lean-flycheck-use t))
  (lean-flycheck-init)
  (flycheck-mode t))

(defun lean-flycheck-turn-off ()
  (interactive)
  (when lean-flycheck-use
    (when (interactive-p)
      (message "no flycheck in lean-mode")))
  (flycheck-mode 0)
  (setq lean-flycheck-use nil))

(defun lean-flycheck-toggle-use ()
  (interactive)
  (if lean-flycheck-use
      (lean-flycheck-turn-off)
    (lean-flycheck-turn-on)))

(add-hook 'lean-mode-hook '(lambda ()
             (when lean-flycheck-use (lean-flycheck-turn-on))))

(defun lean-flycheck-try-parse-error-with-pattern (err pattern)
    "Try to parse a single ERR with a PATTERN.

Return the parsed error if PATTERN matched ERR, or nil
otherwise."
    (let ((regexp (car pattern))
          (level (cdr pattern)))
      (when (string-match regexp err)
        (let ((filename (match-string 1 err))
              (line (match-string 2 err))
              (column (match-string 3 err))
              (message (match-string 4 err)))
          (flycheck-error-new
           :filename (unless (string-empty-p filename) filename)
           :line (flycheck-string-to-number-safe line)
           :column (let ((col (flycheck-string-to-number-safe column)))
                     (if (= col 0) 1 col))
           :message (unless (string-empty-p message) message)
           :level level)))))

(eval-after-load "flycheck.el"
  '(defadvice flycheck-try-parse-error-with-pattern
     (after lean-flycheck-try-parse-error-with-pattern activate)
     "Add 1 to error-column."
     (let* ((err ad-return-value)
            (col (flycheck-error-column err)))
       (when (and (string= major-mode "lean-mode") col)
         (setf (flycheck-error-column ad-return-value) (1+ col))))))

(provide 'lean-flycheck)
