;; Copyright (c) 2013, 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'mmm-mode)
(require 'mmm-auto)
(require 'lua-mode)
(setq mmm-global-mode 'maybe)
(setq mmm-submode-decoration-level 0)
(eval-after-load 'mmm-vars
  '(progn
     (mmm-add-group
      'lean-lua
      '((lua-inline
         :submode lua-mode
         :face mmm-code-submode-face
         :insert ((?l lean-tag nil @ "(*\n" @ " " _ "" @ "\n*)" @))
         :front "[(][*]"
         :back "[*][)]")))
     (mmm-add-mode-ext-class 'lean-mode "\\.lean" 'lean-lua)))
(defun lean-mmm-lua-hook ()
  (setq-local mmm-parse-when-idle t)
  (setq-local mmm-idle-timer-delay 0.5))

(provide 'lean-mmm-lua)
