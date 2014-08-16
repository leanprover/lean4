;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defun lean-find-tag ()
  "lean-find-tag"
  (interactive)
  (let ((ltags-file-name (lean-get-executable "lmake"))
        (bounds (bounds-of-thing-at-point 'symbol))
        symbol-name)
    (when bounds
      (setq symbol-name (buffer-substring-no-properties (car bounds) (cdr bounds)))
      ;; run ltags
      (message ltags-file-name)
      (call-process ltags-file-name nil nil nil "TAGS" "--jobs" "--keep-going" "--permissive")
      (find-tag symbol-name))))
(setq tags-revert-without-query t)
(provide 'lean-tags)
