;;  -*- lexical-binding: t -*-
;;
;; Copyright (c) 2017 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Gabriel Ebner
;;

(require 's)
(require 'json)
(require 'lean4-util)

(defun lean4-leanpkg-find-dir-in (dir)
  (when dir
    (or (lean4-leanpkg-find-dir-in (f-parent dir))
        (when (f-exists? (f-join dir "leanpkg.toml")) dir))))

(defun lean4-leanpkg-find-dir ()
  (and (buffer-file-name)
       (lean4-leanpkg-find-dir-in (f-dirname (buffer-file-name)))))

(defun lean4-leanpkg-find-dir-safe ()
  (or (lean4-leanpkg-find-dir)
      (error (format "cannot find leanpkg.toml for %s" (buffer-file-name)))))

(defun lean4-leanpkg-executable ()
  (lean4-get-executable "leanpkg"))

(defvar lean4-leanpkg-running nil)
(defvar-local lean4-leanpkg-configure-prompt-shown nil)

(defun lean4-leanpkg-run (cmd &optional restart-lean4-server)
  "Call `leanpkg $cmd`"
  (let ((dir (file-name-as-directory (lean4-leanpkg-find-dir-safe)))
        (orig-buf (current-buffer)))
    (with-current-buffer (get-buffer-create "*leanpkg*")
      (let ((inhibit-read-only t)) (erase-buffer))
      (switch-to-buffer-other-window (current-buffer))
      (redisplay)
      (insert (format "> leanpkg %s\n" cmd))
      (setq lean4-leanpkg-running t)
      (let* ((default-directory dir)
             (out-buf (current-buffer))
             (proc (start-process "leanpkg" (current-buffer)
                                  (lean4-leanpkg-executable) cmd)))
        (comint-mode)
        (set-process-filter proc #'comint-output-filter)
        (set-process-sentinel
         proc (lambda (_p _e)
                (setq lean4-leanpkg-running nil)
                (when restart-lean4-server
                  (with-current-buffer out-buf
                    (insert "; restarting lean server\n"))
                  (with-current-buffer orig-buf
                    (lean4-server-restart)))
                (with-current-buffer out-buf
                  (insert "; done"))))))))

(defun lean4-leanpkg-configure ()
  "Call leanpkg configure"
  (interactive)
  (lean4-leanpkg-run "configure" 't))

(defun lean4-leanpkg-build ()
  "Call leanpkg build"
  (interactive)
  (lean4-leanpkg-run "build"))

(defun lean4-leanpkg-test ()
  "Call leanpkg test"
  (interactive)
  (lean4-leanpkg-run "test"))

(defun lean4-leanpkg-find-path-file ()
  (let* ((json-object-type 'plist) (json-array-type 'list) (json-false nil)
         (path-json (shell-command-to-string
                     (concat (shell-quote-argument (lean4-get-executable lean4-executable-name))
                             " -p")))
         (path-out (json-read-from-string path-json)))
    (when (and (eq major-mode 'lean4-mode)
               (plist-get path-out :is_user_leanpkg_path)
               (not lean4-leanpkg-running)
               (not lean4-leanpkg-configure-prompt-shown)
               (setq lean4-leanpkg-configure-prompt-shown t)
               (lean4-leanpkg-find-dir)
               (y-or-n-p (format "Found leanpkg.toml in %s, call leanpkg configure?" (lean4-leanpkg-find-dir))))
      (save-match-data ; running in timer so that we don't mess up the window layout
        (run-at-time nil nil
                     (lambda (buf)
                       (with-current-buffer buf
                         (lean4-leanpkg-configure)))
                     (current-buffer))))
    (setq lean4-leanpkg-configure-prompt-shown t)
    (plist-get path-out :leanpkg_path_file)))

(provide 'lean4-leanpkg)
