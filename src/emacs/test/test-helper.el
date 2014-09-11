;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defconst lean-test/test-path
  (f-parent (f-this-file)))

(defconst lean-test/root-path
  (f-parent lean-test/test-path))

(add-to-list 'load-path lean-test/root-path)

;; Avoid Emacs 23 interupting the tests with:
;;   File bar-autoloads.el changed on disk.  Reread from disk? (yes or no)
(fset 'y-or-n-p (lambda (_) t))
(fset 'yes-or-no-p (lambda (_) t))
