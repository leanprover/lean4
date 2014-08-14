;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defvar lean-global-info-list nil
  "A placeholder we save the info-list that we get from lean server")

(defvar lean-global-info-processed nil
  "A shared variable to indicate the finished processing of lean-info")

(defvar lean-global-info-buffer ""
  "local buffer used to store messages sent by lean server")

(defvar lean-global-server-current-file-name ""
  "Current filename that lean server is processing")

(defvar-local lean-changed-lines nil
  "Changed lines")
(defvar-local lean-removed-lines nil
  "Removed lines")
(defvar-local lean-inserted-lines nil
  "Inserted lines")

(defvar lean-global-before-change-beg nil
  "Before-change BEG")
(defvar lean-global-before-change-end nil
  "Before-change END")
(defvar lean-global-before-change-beg-line-number nil
  "Before-change BEG line-number")
(defvar lean-global-before-change-end-line-number nil
  "Before-change END line-number")
(defvar lean-global-before-change-text ""
  "Before-change text")

(provide 'lean-variable)
