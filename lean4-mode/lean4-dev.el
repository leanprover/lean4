;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2017 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Sebastian Ullrich
;;

(require 'f)
(require 'lean4-util)

(defun lean4-diff-test-file ()
  "Use interactive ./test_input.sh on file of current buffer"
  (interactive)
  ; yes: auto-agree to copying missing files
  (message (shell-command-to-string (format "yes | PATH=%s/bin:$PATH ./test_single.sh -i \"%s\"" (lean4-get-rootdir) (f-filename (buffer-file-name))))))

(provide 'lean4-dev)
