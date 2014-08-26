;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'dash)

(defun lean-generate-tags ()
  "Run lmake TAGS."
  (interactive)
  (let ((ltags-file-name (lean-get-executable "lmake")))
    (call-process ltags-file-name nil nil nil "TAGS" "--jobs" "--keep-going" "--permissive")))

(defun lean-find-tag ()
  "lean-find-tag"
  (interactive)
  (let ((full-name (lean-get-full-name-at-point)))
    (when full-name
      (find-tag full-name))))

(defun lean-complete-tag ()
  "complete with tag"
  (interactive)
  (lean-generate-tags)
  (complete-tag))
(provide 'lean-tags)
