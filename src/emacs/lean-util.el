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

(defun lean-letter-like-unicode-p (u)
  (when u
    (cond ((and (<= #x3b1 u)  (<= u #x3c9)   (not (= u #x3bb))) t)
          ((and (<= #x3ca u)  (<= u #x3fb))                     t)
          ((and (<= #x1f00 u) (<= u #x1ffe))                    t)
          ((and (<= #x2100 u) (<= u #x214f))                    t))))

(defun lean-super-sub-script-alnum-unicode-p (u)
  (when u
    (cond ((and (<= #x2070 u) (<= u #x2078)) t)
          ((and (<= #x207f u) (<= u #x2089)) t)
          ((and (<= #x2090 u) (<= u #x209c)) t))))

(defun lean-isalpha (c)
  (when c
    (cond ((and (<= ?a c) (<= c ?z)) t)
          ((and (<= ?A c) (<= c ?Z)) t))))

(defun lean-isnum (c)
  (when c
    (if (and (<= ?0 c) (<= c ?9)) t)))

(defun lean-isalnum (c)
  (when c
    (or (lean-isalpha c)
        (lean-isnum   c))))

(defun lean-id-rest-p (c)
  (when c
    (or (lean-isalnum c)
        (= c ?_)
        (= c ?\')
        (lean-letter-like-unicode-p c)
        (lean-super-sub-script-alnum-unicode-p c))))

(defun lean-id-first-p (c)
  (when c
    (or (lean-isalnum c)
      (= c ?_)
      (lean-letter-like-unicode-p c))))

(defun lean-find-id-beg ()
  (save-excursion
    (let ((initial-pos (point))
          (mode 'backward)
          stop char-at-pos success)
      (while (not stop)
        (setq char-at-pos (char-after))
        (cl-case mode
          ('backward
           (cond
            ((lean-id-rest-p char-at-pos) (backward-char 1))
            (t                            (forward-char  1)
                                          (setq mode 'forward))))
          ('forward
           (cond
            ((lean-id-first-p char-at-pos) (setq stop t)
             (setq success t))
            ((< (point) initial-pos)       (forward-char 1))
            (t                             (setq stop t))))))
      (when success
        (point)))))

(defun lean-find-hname-beg ()
  (save-excursion
    (let* ((new-id-beg (lean-find-id-beg))
           old-id-beg)
      (while new-id-beg
        (setq old-id-beg new-id-beg)
        (goto-char old-id-beg)
        (cond ((looking-back ".[.]")
               (backward-char 2)
               (setq new-id-beg (lean-find-id-beg)))
              (t
               (setq new-id-beg nil))))
      old-id-beg)))

(defun lean-grab-id ()
  (interactive)
  (when (not (bolp))
    (save-excursion
      (let ((cur-pos (point))
            id-beg)
        (backward-char 1)
        (setq id-beg (lean-find-id-beg))
        (when id-beg
          (buffer-substring id-beg cur-pos))))))

(defun lean-grab-hname ()
  (interactive)
  (when (not (bolp))
    (save-excursion
      (let ((cur-pos (point))
            id-beg)
        (backward-char 1)
        (setq id-beg (lean-find-hname-beg))
        (when id-beg
          (buffer-substring id-beg cur-pos))))))

(defun lean-line-offset ()
  "Return the byte-offset of current position, counting from the
  beginning of the line"
  (interactive)
  (let ((bol-pos
         (save-excursion
           (beginning-of-line)
           (point)))
        (pos (point)))
    (- pos bol-pos)))

(provide 'lean-util)
