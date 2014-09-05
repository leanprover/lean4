;; Copyright (c) 2014 Microsoft Corporation. All rights reserved.
;; Released under Apache 2.0 license as described in the file LICENSE.
;;
;; Author: Soonho Kong
;;

(require 'cl-lib)

(defgroup lean nil "Lean mode" :prefix 'lean :group 'languages)

(defvar-local lean-default-executable-name
  (cl-case system-type
    ('gnu          "lean")
    ('gnu/linux    "lean")
    ('gnu/kfreebsd "lean")
    ('darwin       "lean")
    ('ms-dos       "lean")
    ('windows-nt   "lean.exe")
    ('cygwin       "lean.exe") ;; TODO(soonhok): check this
    )
  "Default executable name of Lean")

(defcustom lean-rootdir nil
  "Full pathname of lean root directory. It should be defined by user."
  :group 'lean
  :type 'string)

(defcustom lean-executable-name lean-default-executable-name
  "Name of lean executable"
  :group 'lean
  :type 'string)

(defcustom lean-flycheck-use t
  "Use flycheck for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-company-use t
  "Use company mode for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-eldoc-use t
  "Use eldoc mode for lean."
  :group 'lean
  :type 'boolean)

(defcustom lean-eldoc-nay-retry-time 0.3
  "When eldoc-function had nay, try again after this amount of time.")

(defcustom lean-server-retry-time 0.1
  "Retry interval for event-handler")

(defcustom lean-flycheck-checker-name "linja"
  "lean-flychecker checker name"
  :group 'lean
  :type 'string)

(defcustom lean-flycheck-checker-options '("--flycheck" "120")
  "lean-flychecker checker option"
  :group 'lean)

(defcustom lean-delete-trailing-whitespace nil
  "Set this variable to true to automatically delete trailing
whitespace when a buffer is loaded from a file or when it is
written."
  :group 'lean
  :type 'boolean)

(defcustom lean-rule-column 100
  "Specify rule-column."
  :group 'lean
  :type '(choice (integer :tag "Columns")
                 (const :tag "Unlimited" nil))
  :type 'int)

(defcustom lean-rule-color "#cccccc"
  "Color used to draw the fill-column rule"
  :group 'fill-column-indicator
  :tag "Fill-column rule color"
  :type 'color)

(defcustom lean-show-rule-column-method nil
  "If enabled, it highlights column"
  :group 'lean
  :type '(choice (const :tag "Disabled" nil)
                 (const :tag "Vertical Line" vline)
                 ;;(const :tag "Whole Lines" lines)
                 ;;(const :tag "Only Beyond lean-rule-column" lines-tail)
                 ))

(provide 'lean-settings)
