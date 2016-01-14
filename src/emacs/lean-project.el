;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 's)
(require 'lean-util)

(defconst lean-project-file-name ".project"
  "Project file name")

(defun lean-project-find-root ()
  (lean-find-file-upward lean-project-file-name))

(defun lean-project-inside-p ()
  (if (lean-project-find-root) t nil))

(defun lean-project-create (directory)
  (interactive
   (list (read-directory-name "Specify the project root directory: ")))
  (let ((project-file (concat (file-name-as-directory directory)
                               lean-project-file-name)))
    (if (file-exists-p project-file)
        (user-error "project-file %s already exists" project-file))
    (find-file project-file)
    (insert (s-join "\n"
                    '("# Lean project file"
                      ""
                      "# Include all .lean files under this directory"
                      "+ *.lean"
                      ""
                      "# Exclude flycheck generated temp files"
                      "- flycheck*.lean"
                      ""
                      "# Exclude emacs temp files"
                      "- .#*.lean")))
    (save-buffer)))

(provide 'lean-project)
