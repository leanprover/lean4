;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defmacro lean-get-this-if-true-or-that (this that)
  `(cond (,this ,this)
         (t ,that)))

(defun lean-get-rootdir ()
  (lean-get-this-if-true-or-that
   lean-rootdir
   (error "'lean-rootdir' is not defined. Please have\
(customize-set-variable 'lean-rootdir \"~/work/lean\")\
in your emacs configuration.\
Also make sure that your (custom-set-variable ...) comes before\
(require 'lean-mode).")))

(defun lean-get-executable (exe-name)
  "Return fullpath of lean executable"
  (let ((lean-binary-dir-name "bin"))
    (when lean-rootdir
      (concat (file-name-as-directory (lean-get-rootdir))
              (file-name-as-directory "bin")
              exe-name))))

(provide 'lean-util)
