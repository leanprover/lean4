(require 'company)
(defun company-lean ()
  (set (make-local-variable 'company-backends) '(company-lean))
  (company-mode))
(add-hook 'lean-mode-hook 'company-lean)

(setq company-tooltip-limit 20)                      ; bigger popup window
(setq company-idle-delay .3)                         ; decrease delay before autocompletion popup shows
(setq company-echo-delay 0)                          ; remove annoying blinking
(setq company-begin-commands '(self-insert-command)) ; start autocompletion only after typing

(defun company-lean--prefix ()
  "Returns the symbol to complete. Also, if point is on a dot,
triggers a completion immediately."
  (if company-lean-begin-after-member-access
      (company-grab-symbol-cons "\\." 1)
    (company-grab-symbol)))

(defun company-go--invoke-autocomplete ()
  (let ((temp-buffer (generate-new-buffer "*leancompany*")))
    (prog2
	(call-process-region (point-min)
			     (point-max)
			     "leancompany"
			     nil
			     temp-buffer
			     nil
			     "-f=csv"
			     "autocomplete"
			     (or (buffer-file-name) "")
			     (concat "c" (int-to-string (- (point) 1))))
	(with-current-buffer temp-buffer (buffer-string))
      (kill-buffer temp-buffer))))

(defun company-lean--candidates ()
  (company-lean--get-candidates (split-string (company-lean--invoke-autocomplete) "\n" t)))

;;;###autoload
(defun company-lean (command &optional arg &rest ignored)
  (case command
    (prefix (and (derived-mode-p 'lean-mode)
                 (not (company-in-string-or-comment))
                 (or (company-lean--prefix) 'stop)))
    (candidates (company-lean--candidates))
    (meta (get-text-property 0 'meta arg))
    (annotation
     (when company-lean-show-annotation
       (get-text-property 0 'meta arg)))
    (location (company-lean--location arg))
    (sorted t)))

(provide 'company-lean)

(defun company-lean--doc-buffer (candidate)
    (message "doc candidate = %S" candidate)
  (company-doc-buffer (get-text-property 0 'doc candidate)))

(defun company-lean--annotation (candidate)
  (message "annotation candidate = %S" candidate)
    (let ((anno (get-text-property 0 'kind candidate)))
      (when anno (concat " blabla" anno)))
    " : annotation1")

(defun company-lean--candidates (prefix)
  (cl-loop for x in '("foobar" "foobaz" "foobarbaz")
           collect x
           ))

(defun company-my-backend (command &optional arg &rest ignored)
  (interactive (list 'interactive))
  (case command
    (interactive (company-begin-backend 'company-my-backend))
    (prefix (when (looking-back "foo\\>")
              (match-string 0)))
    (candidates (company-lean--candidates arg))
    (annotation (company-lean--annotation arg))
    ))

(set (make-local-variable 'company-backends) '(company-my-backend))
(company-mode)

