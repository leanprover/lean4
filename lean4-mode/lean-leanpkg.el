;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2017 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Gabriel Ebner
;;

(require 's)
(require 'json)
(require 'lean-util)

(defun lean-leanpkg-find-dir-in (dir)
  (when dir
    (or (lean-leanpkg-find-dir-in (f-parent dir))
        (when (f-exists? (f-join dir "leanpkg.toml")) dir))))

(defun lean-leanpkg-find-dir ()
  (and (buffer-file-name)
       (lean-leanpkg-find-dir-in (f-dirname (buffer-file-name)))))

(defun lean-leanpkg-find-dir-safe ()
  (or (lean-leanpkg-find-dir)
      (error (format "cannot find leanpkg.toml for %s" (buffer-file-name)))))

(defun lean-leanpkg-executable ()
  (lean-get-executable "leanpkg"))

(defvar lean-leanpkg-running nil)
(defvar-local lean-leanpkg-configure-prompt-shown nil)

(defun lean-leanpkg-run (cmd &optional restart-lean-server)
  "Call `leanpkg $cmd`"
  (let ((dir (file-name-as-directory (lean-leanpkg-find-dir-safe)))
        (orig-buf (current-buffer)))
    (with-current-buffer (get-buffer-create "*leanpkg*")
      (let ((inhibit-read-only t)) (erase-buffer))
      (switch-to-buffer-other-window (current-buffer))
      (redisplay)
      (insert (format "> leanpkg %s\n" cmd))
      (setq lean-leanpkg-running t)
      (let* ((default-directory dir)
             (out-buf (current-buffer))
             (proc (start-process "leanpkg" (current-buffer)
                                  (lean-leanpkg-executable) cmd)))
        (comint-mode)
        (set-process-filter proc #'comint-output-filter)
        (set-process-sentinel
         proc (lambda (_p _e)
                (setq lean-leanpkg-running nil)
                (when restart-lean-server
                  (with-current-buffer out-buf
                    (insert "; restarting lean server\n"))
                  (with-current-buffer orig-buf
                    (lean-server-restart)))
                (with-current-buffer out-buf
                  (insert "; done"))))))))

(defun lean-leanpkg-configure ()
  "Call leanpkg configure"
  (interactive)
  (lean-leanpkg-run "configure" 't))

(defun lean-leanpkg-build ()
  "Call leanpkg build"
  (interactive)
  (lean-leanpkg-run "build"))

(defun lean-leanpkg-test ()
  "Call leanpkg test"
  (interactive)
  (lean-leanpkg-run "test"))

(defun lean-leanpkg-find-path-file ()
  (let* ((json-object-type 'plist) (json-array-type 'list) (json-false nil)
         (path-json (shell-command-to-string
                     (concat (shell-quote-argument (lean-get-executable lean-executable-name))
                             " -p")))
         (path-out (json-read-from-string path-json)))
    (when (and (eq major-mode 'lean-mode)
               (plist-get path-out :is_user_leanpkg_path)
               (not lean-leanpkg-running)
               (not lean-leanpkg-configure-prompt-shown)
               (setq lean-leanpkg-configure-prompt-shown t)
               (lean-leanpkg-find-dir)
               (y-or-n-p (format "Found leanpkg.toml in %s, call leanpkg configure?" (lean-leanpkg-find-dir))))
      (save-match-data ; running in timer so that we don't mess up the window layout
        (run-at-time nil nil
                     (lambda (buf)
                       (with-current-buffer buf
                         (lean-leanpkg-configure)))
                     (current-buffer))))
    (setq lean-leanpkg-configure-prompt-shown t)
    (plist-get path-out :leanpkg_path_file)))

(provide 'lean-leanpkg)
