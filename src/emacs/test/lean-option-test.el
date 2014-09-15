;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'ert)
(require 'lean-option)

(ert-deftest lean-test-update-string-alist ()
  (lean-update-option-alist "pp::implicit" 'true)
  (should
   (equal (assoc-string "pp::implicit" lean-global-option-alist)
          '("pp::implicit" . true)))
  (lean-update-option-alist "pp::implicit" 'false)
  (should
   (equal (assoc-string "pp::implicit" lean-global-option-alist)
          '("pp::implicit" . false))))
