;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

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

(provide 'lean-flycheck)
