;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)
(require 'f)
(require 's)
(require 'dash)

(defun lean4-setup-rootdir ()
  (let ((root (executable-find lean4-executable-name)))
    (when root
      (setq lean4-rootdir (f-dirname (f-dirname root))))
    lean4-rootdir))

(defun lean4-get-rootdir ()
  (if lean4-rootdir
      (let ((lean4-path (f-full (f-join lean4-rootdir "bin" lean4-executable-name))))
        (unless (f-exists? lean4-path)
          (error "Incorrect 'lean4-rootdir' value, path '%s' does not exist." lean4-path))
        lean4-rootdir)
    (or
     (lean4-setup-rootdir)
     (error
      (concat "Lean was not found in the 'exec-path' and 'lean4-rootdir' is not defined. "
              "Please set it via M-x customize-variable RET lean4-rootdir RET.")))))

(defun lean4-get-executable (exe-name)
  "Return fullpath of lean executable"
  (let ((lean4-bin-dir-name "bin"))
    (f-full (f-join (lean4-get-rootdir) lean4-bin-dir-name exe-name))))

(defun lean4-line-offset (&optional pos)
  "Return the byte-offset of `pos` or current position, counting from the
  beginning of the line"
  (interactive)
  (let* ((pos (or pos (point)))
         (bol-pos
          (save-excursion
            (goto-char pos)
            (beginning-of-line)
            (point))))
    (- pos bol-pos)))

(defun lean4-pos-at-line-col (l c)
  "Return the point of the given line and column."
  ;; http://emacs.stackexchange.com/a/8083
  (save-excursion
    (goto-char (point-min))
    (forward-line (- l 1))
    (move-to-column c)
    (point)))

(defun lean4-whitespace-cleanup ()
    (when lean4-delete-trailing-whitespace
      (delete-trailing-whitespace)))

(defun lean4-in-comment-p ()
  "t if a current point is inside of comment block
   nil otherwise"
  (nth 4 (syntax-ppss)))

;; The following function is a slightly modified version of
;; f--collect-entries written by Johan Andersson
;; The URL is at https://github.com/rejeep/f.el/blob/master/f.el#L416-L435
(defun lean4--collect-entries (path recursive)
  (let (result
        (entries
         (-reject
          (lambda (file)
            (or
             (equal (f-filename file) ".")
             (equal (f-filename file) "..")))
          (directory-files path t))))
    ;; The following line is the only modification that I made
    ;; It waits 0.0001 second for an event. This wait allows
    ;; wait-timeout function to check the timer and kill the execution
    ;; of this function.
    (sit-for 0.0001)
    (cond (recursive
           (-map
            (lambda (entry)
              (if (f-file? entry)
                  (setq result (cons entry result))
                (when (f-directory? entry)
                  (setq result (cons entry result))
                  (setq result (append result (lean4--collect-entries entry recursive))))))
            entries))
          (t (setq result entries)))
    result))

;; The following function is a slightly modified version of
;; f-files function written by Johan Andersson The URL is at
;; https://github.com/rejeep/f.el/blob/master/f.el#L478-L481
(defun lean4-find-files (path &optional fn recursive)
  "Find all files in PATH."
  ;; It calls lean4--collect-entries instead of f--collect-entries
  (let ((files (-select 'f-file? (lean4--collect-entries path recursive))))
    (if fn (-select fn files) files)))

(provide 'lean4-util)
