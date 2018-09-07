;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2017 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Sebastian Ullrich
;;

(require 'f)
(require 'lean-util)

(defun lean-diff-test-file ()
  "Use interactive ./test_input.sh on file of current buffer"
  (interactive)
  (message (shell-command-to-string (format "yes | ./test_single.sh \"%s\" \"%s\" yes"
                                            (lean-get-executable "lean")
                                            (f-filename (buffer-file-name))))))

(provide 'lean-dev)
