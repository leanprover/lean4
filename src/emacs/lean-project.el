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
  (let ((p (f--traverse-upwards (f-exists? (f-expand lean-project-file-name it))
                                (f-dirname (buffer-file-name)))))
    (if p (file-name-as-directory p)
          nil)))

(defun lean-project-inside-p ()
  (if (lean-project-find-root) t nil))

(defun lean-project-create (directory type)
  (interactive
   (list (read-directory-name "Specify the project root directory: ")))
  (let ((project-file (concat (file-name-as-directory directory)
                              lean-project-file-name))
        (ext "lean")
        (default-contents
          (s-join "\n"
                  ;;  EXT is a placeholder.
                  '("# Lean project file"
                    ""
                    "# Include all .EXT files under this directory"
                    "+ *.EXT"
                    ""
                    "# Exclude flycheck generated temp files"
                    "- flycheck*.EXT"
                    ""
                    "# Exclude emacs temp files"
                    "- .#*.EXT"))))
    (if (file-exists-p project-file)
        (user-error "project-file %s already exists" project-file))
    (find-file project-file)
    (insert (s-replace "EXT" ext default-contents))
    (save-buffer)))

(provide 'lean-project)
