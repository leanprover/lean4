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

(defun leanpkg-find-dir-in (dir)
  (when dir
    (or (leanpkg-find-dir-in (f-parent dir))
        (when (f-exists? (f-join dir "leanpkg.toml")) dir))))

(defun leanpkg-find-dir ()
  (and (buffer-file-name)
       (leanpkg-find-dir-in (f-dirname (buffer-file-name)))))

(defun leanpkg-find-dir-safe ()
  (or (leanpkg-find-dir)
      (error (format "cannot find leanpkg.toml for %s" (buffer-file-name)))))

(defun leanpkg-executable ()
  (lean-get-executable "leanpkg"))

(defvar leanpkg-running nil)
(defvar-local leanpkg-configure-prompt-shown nil)

(defun leanpkg-run (cmd &optional restart-lean-server)
  "Call `leanpkg $cmd`"
  (let ((dir (file-name-as-directory (leanpkg-find-dir-safe)))
        (orig-buf (current-buffer)))
    (with-current-buffer (get-buffer-create "*leanpkg*")
      (setq buffer-read-only nil)
      (erase-buffer)
      (switch-to-buffer-other-window (current-buffer))
      (redisplay)
      (insert (format "> leanpkg %s\n" cmd))
      (setq leanpkg-running t)
      (let* ((default-directory dir)
             (out-buf (current-buffer))
             (proc (start-process "leanpkg" (current-buffer)
                                  (leanpkg-executable) cmd)))
        (set-process-sentinel
         proc (lambda (p e)
                (setq leanpkg-running nil)
                (when restart-lean-server
                  (with-current-buffer out-buf
                    (insert "; restarting lean server\n"))
                  (with-current-buffer orig-buf
                    (lean-server-restart)))))))))

(defun leanpkg-configure ()
  "Call leanpkg configure"
  (interactive)
  (leanpkg-run "configure" 't))

(defun leanpkg-build ()
  "Call leanpkg build"
  (interactive)
  (leanpkg-run "build"))

(defun leanpkg-test ()
  "Call leanpkg test"
  (interactive)
  (leanpkg-run "test"))

(defun leanpkg-find-path-file ()
  (let* ((json-object-type 'plist) (json-array-type 'list) (json-false nil)
         (path-json (shell-command-to-string
                     (concat (shell-quote-argument (lean-get-executable lean-executable-name))
                             " -p")))
         (path-out (json-read-from-string path-json)))
    (when (and (eq major-mode 'lean-mode)
               (plist-get path-out :is_user_leanpkg_path)
               (not leanpkg-running)
               (not leanpkg-configure-prompt-shown)
               (setq leanpkg-configure-prompt-shown t)
               (leanpkg-find-dir)
               (y-or-n-p (format "Found leanpkg.toml in %s, call leanpkg configure?" (leanpkg-find-dir))))
      (save-match-data ; running in timer so that we don't mess up the window layout
        (run-at-time nil nil
                     (lambda (buf)
                       (with-current-buffer buf
                         (leanpkg-configure)))
                     (current-buffer))))
    (setq leanpkg-configure-prompt-shown t)
    (plist-get path-out :leanpkg_path_file)))

(provide 'lean-pkg)
