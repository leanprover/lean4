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

(defun lean-string-contains-line-p (str line)
  "return true if str contains line"
  (or (string-prefix-p line str)
      (search (concat "\n" line) str)))

(defun lean-string-join (strings &optional separator)
  "Join all STRINGS using SEPARATOR."
  (mapconcat 'identity strings separator))

(defun lean-grab-line (n)
  "Return the contents of line n"
  (let* ((cur-line-number (line-number-at-pos))
         (rel-line-number (1+ (- n cur-line-number)))
         (p1 (line-beginning-position rel-line-number))
         (p2 (line-end-position rel-line-number)))
    (buffer-substring-no-properties p1 p2)))

(defun lean-split-seq-if (seq delim-pred &optional while-pred)
  (let ((result ())
        (cell ()))
    (cl-loop for item in seq
             while (if while-pred (funcall while-pred item) t)
             do (cond ((funcall delim-pred item)
                       (when cell
                         (setq result (cons (nreverse cell) result))
                         (setq cell nil)))
                      (t (setq cell (cons item cell))))
             finally
             (return (cond (cell (nreverse (cons (nreverse cell) result)))
                           (t (nreverse result)))))))

(defun lean-split-seq (seq delim)
  (lean-split-seq-if seq (lambda (x) (equal delim x))))

(defun lean-take-first-n (seq n)
  "Take first n elements from seq"
  (cond ((< (length seq) n) seq)
        (t                  (subseq seq 0 n))))

;; -- Test
(cl-assert (equal (lean-take-first-n '(1 2 3 4 5 6 7 8 9 10) 3)
                  '(1 2 3)))
(cl-assert (equal (lean-take-first-n '(1 2 3 4 5 6 7 8 9 10) 10)
                  '(1 2 3 4 5 6 7 8 9 10)))
(cl-assert (equal (lean-take-first-n '(1 2 3 4 5 6 7 8 9 10) 11)
                  '(1 2 3 4 5 6 7 8 9 10)))
(cl-assert (equal (lean-take-first-n '(1 2 3 4 5 6 7 8 9 10) 0)
                  nil))
(cl-assert (equal (lean-take-first-n '() 0)
                  nil))
(cl-assert (equal (lean-take-first-n '() 2)
                  nil))

(defun lean-take-last-n (seq n)
  "Take first n elements from seq"
  (let ((l (length seq)))
    (cond ((< l n) seq)
          (t       (subseq seq (- l n) l)))))
;; -- Test
(cl-assert (equal (lean-take-last-n '(1 2 3 4 5 6 7 8 9 10) 3)
                  '(8 9 10)))
(cl-assert (equal (lean-take-last-n '(1 2 3 4 5 6 7 8 9 10) 10)
                  '(1 2 3 4 5 6 7 8 9 10)))
(cl-assert (equal (lean-take-last-n '(1 2 3 4 5 6 7 8 9 10) 11)
                  '(1 2 3 4 5 6 7 8 9 10)))
(cl-assert (equal (lean-take-last-n '(1 2 3 4 5 6 7 8 9 10) 0)
                  nil))
(cl-assert (equal (lean-take-last-n '() 0)
                  nil))
(cl-assert (equal (lean-take-last-n '() 2)
                  nil))

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
