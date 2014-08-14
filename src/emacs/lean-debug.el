;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)

(defun lean-debug-print (name obj)
  "Display debugging output"
  (message "[LEAN-DEBUG-PRINT] (%s):\n%s" name (prin1-to-string obj)))

(provide 'lean-debug)
