;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(setq-local lean-lmake-name "lmake")
(setq-local lean-lmake-options "--flycheck")
(eval
 `(flycheck-define-checker lean-checker-file
    "A Lean syntax checker (file)."
    :command (,(lean-get-executable lean-lmake-name) ,lean-lmake-options source-inplace)
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
(add-hook 'lean-mode-hook '(lambda () (flycheck-mode t)))
(provide 'lean-flycheck)
