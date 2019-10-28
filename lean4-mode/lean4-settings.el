;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)

(defgroup lean nil
  "Lean Theorem Prover"
  :prefix "lean4-"
  :group 'languages
  :link '(url-link :tag "Website" "http://leanprover.github.io")
  :link '(url-link :tag "Github"  "https://github.com/leanprover/lean"))

(defgroup lean4-keybinding nil
  "Keybindings for lean4-mode."
  :prefix "lean4-"
  :group 'lean)

(defvar-local lean4-default-executable-name
  (cl-case system-type
    ('windows-nt   "lean.exe")
    ('cygwin       "lean.exe")
    (t             "lean_wrapped"))
  "Default executable name of Lean")

(defcustom lean4-rootdir nil
  "Full pathname of lean root directory. It should be defined by user."
  :group 'lean
  :type 'string)

(defcustom lean4-executable-name lean4-default-executable-name
  "Name of lean executable"
  :group 'lean
  :type 'string)

(defcustom lean4-memory-limit 1024
  "Memory limit for lean process in megabytes"
  :group 'lean
  :type 'number)

(defcustom lean4-timeout-limit 100000
  "Deterministic timeout limit (it is approximately the maximum number of memory allocations in thousands)"
  :group 'lean
  :type 'number)

(defcustom lean4-extra-arguments nil
  "Extra command-line arguments to the lean process"
  :group 'lean
  :type '(list string))

(defcustom lean4-eldoc-use t
  "Use eldoc mode for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean4-eldoc-nay-retry-time 0.3
  "When eldoc-function had nay, try again after this amount of time."
  :group 'lean
  :type 'number)

(defcustom lean4-delete-trailing-whitespace nil
  "Set this variable to true to automatically delete trailing
whitespace when a buffer is loaded from a file or when it is
written."
  :group 'lean
  :type 'boolean)

(defcustom lean4-show-type-add-to-kill-ring nil
  "If it is non-nil, add the type information to the kill-ring so
that user can yank(paste) it later. By default, it's
false (nil)."
  :group 'lean
  :type 'boolean)

(defcustom lean4-server-show-pending-tasks t
  "Highlights pending tasks in the current buffer."
  :group 'lean
  :type 'boolean)

(defcustom lean4-server-check-mode 'visible-lines-and-above
  "What parts of the open files the Lean server should check"
  :group 'lean
  :type 'symbol
  :options '(nothing visible-lines visible-lines-and-above visible-files open-files))

(defcustom lean4-keybinding-std-exe1 (kbd "C-c C-x")
  "Lean Keybinding for std-exe #1"
  :group 'lean4-keybinding :type 'key-sequence)
(defcustom lean4-keybinding-std-exe2 (kbd "C-c C-l")
  "Lean Keybinding for std-exe #2"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-show-key (kbd "C-c C-k")
  "Lean Keybinding for show-key"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-server-restart (kbd "C-c C-r")
  "Lean Keybinding for server-restart"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-server-switch-version (kbd "C-c C-s")
  "Lean Keybinding for lean4-server-switch-version"
  :group 'lean4-keybinding :type 'key-sequence)
(defcustom lean4-keybinding-find-definition (kbd "M-.")
  "Lean Keybinding for find-definition"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-tab-indent (kbd "TAB")
  "Lean Keybinding for tab-indent"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-auto-complete (kbd "S-SPC")
  "Lean Keybinding for auto completion"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-hole (kbd "C-c SPC")
  "Lean Keybinding for hole manipulation"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-lean4-toggle-show-goal (kbd "C-c C-g")
  "Lean Keybinding for show-goal-at-pos"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-lean4-toggle-next-error (kbd "C-c C-n")
  "Lean Keybinding for lean4-toggle-next-error"
  :group 'lean4-keybinding  :type 'key-sequence)
(defcustom lean4-keybinding-lean4-message-boxes-toggle (kbd "C-c C-b")
  "Lean Keybinding for lean4-message-boxes-toggle"
  :group 'lean4-keybinding :type 'key-sequence)
(defcustom lean4-keybinding-leanpkg-configure (kbd "C-c C-p C-c")
  "Lean Keybinding for lean4-leanpkg-configure"
  :group 'lean4-keybinding :type 'key-sequence)
(defcustom lean4-keybinding-leanpkg-build (kbd "C-c C-p C-b")
  "Lean Keybinding for lean4-leanpkg-build"
  :group 'lean4-keybinding :type 'key-sequence)
(defcustom lean4-keybinding-leanpkg-test (kbd "C-c C-p C-t")
  "Lean Keybinding for lean4-leanpkg-test"
  :group 'lean4-keybinding :type 'key-sequence)
(provide 'lean4-settings)
