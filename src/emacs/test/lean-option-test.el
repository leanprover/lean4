;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'ert)
(require 'lean-variable)
(require 'lean-settings)
(require 'lean-option)

(ert-deftest lean-test-update-string-alist ()
  (setq lean-global-option-alist
        (lean-update-option-alist lean-global-option-alist "pp.implicit" 'true))
  (should
   (equal (assoc-string "pp.implicit" lean-global-option-alist)
          '("pp.implicit" . true)))
  (setq lean-global-option-alist
        (lean-update-option-alist lean-global-option-alist "pp.implicit" 'false))
  (should
   (equal (assoc-string "pp.implicit" lean-global-option-alist)
          '("pp.implicit" . false))))

(ert-deftest lean-test-update-string-alist-default ()
  (setq lean-global-option-alist nil)
  (should (string= (lean-option-string)
                   (format "-D%s=%d"
                           "pp.width"
                           lean-default-pp-width)))
  (setq lean-global-option-alist
        (lean-update-option-alist lean-global-option-alist "pp.width" 80))
  (should (string= (lean-option-string)
                   (format "-D%s=%d"
                           "pp.width"
                           80))))
