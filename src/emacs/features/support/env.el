(require 'f)

(defvar emacs-support-path
  (f-dirname load-file-name))

(defvar emacs-features-path
  (f-parent emacs-support-path))

(defvar emacs-root-path
  (f-parent emacs-features-path))

(add-to-list 'load-path emacs-root-path)

(require 'emacs)
(require 'espuds)
(require 'ert)

(Setup
 ;; Before anything has run
 )

(Before
 ;; Before each scenario is run
 )

(After
 ;; After each scenario is run
 )

(Teardown
 ;; After when everything has been run
 )
