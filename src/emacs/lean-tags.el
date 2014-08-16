;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defun lean-run-lmake-tag ()
  (let ((ltags-file-name (lean-get-executable "lmake")))
    (call-process ltags-file-name nil nil nil "TAGS" "--jobs" "--keep-going" "--permissive")))

(defun lean-find-tag ()
  "lean-find-tag"
  (interactive)
  (let ((bounds (bounds-of-thing-at-point 'symbol))
        symbol-name)
    (when bounds
      (setq symbol-name (buffer-substring-no-properties (car bounds) (cdr bounds)))
      (lean-run-lmake-tag)
      (find-tag symbol-name))))

(defun lean-complete-tag ()
  "complete with tag"
  (interactive)
  (lean-run-lmake-tag)
  (complete-tag))
(setq tags-revert-without-query t)

(provide 'lean-tags)
