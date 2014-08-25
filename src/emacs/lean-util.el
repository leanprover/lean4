;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)

(defun lean-concat-paths (&rest seq)
  "Concatenate paths"
  (cl-reduce (lambda (p1 p2) (concat (file-name-as-directory p1) p2))
             seq))

(defun lean-grab-line (n)
  "Return the contents of n-th line at the current buffer"
  (let* ((cur-line-number (line-number-at-pos))
         (rel-line-number (1+ (- n cur-line-number)))
         (p1 (line-beginning-position rel-line-number))
         (p2 (line-end-position rel-line-number)))
    (buffer-substring-no-properties p1 p2)))

(defun lean-get-rootdir ()
  (or
   lean-rootdir
   (error
    (concat "'lean-rootdir' is not defined."
            "Please have (customize-set-variable 'lean-rootdir \"~/work/lean\") "
            "in your emacs configuration. "
            "Also make sure that your (custom-set-variable ...) "
            " comes before (require 'lean-mode)"))))

(defun lean-get-executable (exe-name)
  "Return fullpath of lean executable"
  (let ((lean-bin-dir-name "bin"))
    (lean-concat-paths (lean-get-rootdir) lean-bin-dir-name exe-name)))

(provide 'lean-util)
