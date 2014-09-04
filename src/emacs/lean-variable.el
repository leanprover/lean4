;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(defvar lean-global-info-record nil
  "A placeholder we save the info-record that we get from lean server")

(defvar lean-global-server-message-to-process nil
  "A shared variable contains a received message to process.

A message is in the form of (TYPE PRE BODY)
where TYPE := INFO | SET | EVAL | OPTIONS | SHOW | FINDP | ERROR,
      PRE is a server message comes before the message
      BODY is a body of the received message.")

(defvar lean-global-server-process nil
  "lean server process")

(defvar lean-global-server-buffer nil
  "Global buffer used to store messages sent by lean server")

(defvar lean-global-server-current-file-name nil
  "Current filename that lean server is processing")

(defvar lean-global-server-last-time-sent nil
  "Last time lean-mode sent a command to lean-server")

(defvar lean-global-retry-timer nil
  "Timer used to re-try event-handler-function.")

(defvar lean-global-async-task-queue nil
  "Tasks (continuations) to be executed.")

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
