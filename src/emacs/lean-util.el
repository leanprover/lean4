;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'f)
(require 's)
(require 'dash)
(require 'dash-functional)

(defun lean-concat-paths (&rest seq)
  "Concatenate paths"
  (cl-reduce (lambda (p1 p2) (concat (file-name-as-directory p1) p2))
             seq))

(defun lean-find-file-upward (file-name &optional dir-name)
  "Try to find a file in a (current) directory or its parent directories."
  (let* ((dir-name (or dir-name (file-name-directory (buffer-file-name))))
         (parent-dir-name (file-name-directory (directory-file-name dir-name)))
         (full-name (lean-concat-paths dir-name file-name)))
    (cond ((file-exists-p full-name) full-name)
          ((string= dir-name parent-dir-name) nil)
          (t (lean-find-file-upward file-name parent-dir-name)))))

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

(defun lean-path-list ()
  (interactive)
  (let* ((lean-path-env-list
          (parse-colon-path (getenv "LEAN_PATH")))
         (lean--path-list
          (parse-colon-path
           (ignore-errors
             (car (process-lines (lean-get-executable lean-executable-name)
                                 "--path")))))
         (project-dir (f--traverse-upwards (f-exists? (f-expand ".project" it))
                                           (f-dirname (buffer-file-name))))
         (path-list (append lean-path-env-list lean--path-list)))
    (when project-dir
      (setq path-list
            (--map-when (f-relative? it)
                        (f-canonical (f-join project-dir it))
                        path-list)))
    (-uniq (-map (-compose 'f-slash 'f-canonical)
                 path-list))))

(provide 'lean-util)
