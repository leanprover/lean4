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

(defun lean-setup-rootdir ()
  (let ((root (executable-find lean-executable-name)))
    (when root
      (setq lean-rootdir (f-dirname (f-dirname root))))
    root))

(defun lean-get-rootdir ()
  (if lean-rootdir
      (let ((lean-path (f-full (f-join lean-rootdir "bin" lean-executable-name))))
        (unless (f-exists? lean-path)
          (error "Incorrect 'lean-rootdir' value, path '%s' does not exist." lean-path))
        lean-rootdir)
    (or
     (lean-setup-rootdir)
     (error
      (concat "Lean was not found in the 'exec-path' and 'lean-rootdir' is not defined. "
              "Please set it via M-x customize-variable RET lean-rootdir RET.")))))

(defun lean-get-executable (exe-name)
  "Return fullpath of lean executable"
  (let ((lean-bin-dir-name "bin"))
    (f-full (f-join (lean-get-rootdir) lean-bin-dir-name exe-name))))

(defun lean-line-offset (&optional pos)
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

(defun lean-pos-at-line-col (l c)
  "Return the point of the given line and column."
  ;; http://emacs.stackexchange.com/a/8083
  (save-excursion
    (goto-char (point-min))
    (forward-line (- l 1))
    (move-to-column c)
    (point)))

(defun lean-whitespace-cleanup ()
    (when lean-delete-trailing-whitespace
      (delete-trailing-whitespace)))

(defun lean-in-comment-p ()
  "t if a current point is inside of comment block
   nil otherwise"
  (nth 4 (syntax-ppss)))

;; The following function is a slightly modified version of
;; f--collect-entries written by Johan Andersson
;; The URL is at https://github.com/rejeep/f.el/blob/master/f.el#L416-L435
(defun lean--collect-entries (path recursive)
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
                  (setq result (append result (lean--collect-entries entry recursive))))))
            entries))
          (t (setq result entries)))
    result))

;; The following function is a slightly modified version of
;; f-files function written by Johan Andersson The URL is at
;; https://github.com/rejeep/f.el/blob/master/f.el#L478-L481
(defun lean-find-files (path &optional fn recursive)
  "Find all files in PATH."
  ;; It calls lean--collect-entries instead of f--collect-entries
  (let ((files (-select 'f-file? (lean--collect-entries path recursive))))
    (if fn (-select fn files) files)))

(provide 'lean-util)
