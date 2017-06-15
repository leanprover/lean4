;; -*- lexical-binding: t -*-
;;
;;; lean-right-click.el
;;
;; Copyright (c) 2017 David Christiansen. All rights reserved.
;;
;; Author: David Christiansen
;; Released under Apache 2.0 license as described in the file LICENSE.
;;

;;; Code:

(defvar lean-right-click-item-functions nil
  "A list of functions to compute menu items from source locations.

The functions take no arguments.  They will be run in a context
where `current-buffer' gives the buffer in which the click
occurred.  The function should return a three-element list, where
the first is a Lean server command, the second is its parameter
list, and the third is a continuation that will compute a list of
menu items.

 Each menu item is a plist that maps the key :name to the string
to show in the menu and the key :action to a zero-argument
function that implements the action.")
(make-variable-buffer-local 'lean-right-click-item-functions)

(defvar lean-right-click--unique-val-counter 0
  "A global counter for unique values for lean-right-click.")

(defun lean-right-click--unique-val ()
  "Get a unique value for internal tagging."
  (cl-incf lean-right-click--unique-val-counter))

(defun lean-right-click--items-for-location ()
  "Return the menu items for point in the current buffer."
  (let ((commands (cl-loop for fun in lean-right-click-item-functions
                           collecting (funcall fun))))
    (let ((timeout 0.15)
          (items '())
          (start-time (time-to-seconds))
          (command-count (length commands))
          (commands-returned 0))
      (cl-loop for (cmd args cont) in commands
               do (progn (lean-server-send-command
                          cmd args
                          (lambda (&rest result)
                            (setq items (append items (apply cont result)))
                            (cl-incf commands-returned))
                          (lambda (&rest _whatever)
                            (cl-incf commands-returned)))
                         ;; This is necessary to ensure that async IO happens.
                         (sit-for 0.02)))
      (while (and (< (time-to-seconds) (+ timeout start-time))
                  (< commands-returned command-count))
        (sit-for 0.02))
      items)))

(defun lean-right-click-show-menu (click)
  "Show a menu based on the location of CLICK, computed from the `lean-right-click-functions'."
  (interactive "e")
  (let* ((window (posn-window (event-end click)))
         (buffer (window-buffer window))
         (where (posn-point (event-end click)))
         (menu-items (with-current-buffer buffer
                       (save-excursion
                         (goto-char where)
                         (lean-right-click--items-for-location)))))
    (when menu-items
      (let* ((menu (make-sparse-keymap))
             (todo (cl-loop for item in menu-items
                            collecting (let ((sym (lean-right-click--unique-val)))
                                         (define-key-after menu `[,sym]
                                           `(menu-item ,(plist-get item :name)
                                                       (lambda () (interactive)))
                                           t)
                                         (cons sym (plist-get item :action)))))
             (selection (x-popup-menu click menu)))
        (when selection
          (funcall (cdr (assoc (car selection) todo))))))))


(provide 'lean-right-click)
;;; lean-right-click.el ends here
