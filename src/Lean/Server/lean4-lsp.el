;; See README.md

(defconst lean4-home "$LEAN4_HOME")

(require 'lsp-mode)
(require 'lean4-mode)

(define-derived-mode lean4-lsp-mode prog-mode "Lean 4 LSP"
  "Major mode for Lean 4 LSP server
\\{lean4-mode-map}
"
  :syntax-table lean4-syntax-table
  :abbrev-table lean4-abbrev-table
  :group 'lean
  (set (make-local-variable 'comment-start) "--")
  (set (make-local-variable 'comment-start-skip) "[-/]-[ \t]*")
  (set (make-local-variable 'comment-end) "")
  (set (make-local-variable 'comment-end-skip) "[ \t]*\\(-/\\|\\s>\\)")
  (set (make-local-variable 'comment-padding) 1)
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'font-lock-defaults) lean4-font-lock-defaults)
  (set (make-local-variable 'indent-tabs-mode) nil)
  (set 'compilation-mode-font-lock-keywords '())
  (set-input-method "Lean")
  (set (make-local-variable 'lisp-indent-function)
       'common-lisp-indent-function)
  (lean4-set-keys)
  (if (fboundp 'electric-indent-local-mode)
      (electric-indent-local-mode -1)))
  ;; (abbrev-mode 1)
  ;;(pcase-dolist (`(,hook . ,fn) lean4-hooks-alist)
  ;;  (add-hook hook fn nil 'local))
  ;;(lean4-mode-setup))

;; Ref: https://emacs-lsp.github.io/lsp-mode/page/adding-new-language/
(add-to-list 'lsp-language-id-configuration
             '(lean4-lsp-mode . "lean4"))

(defconst lean4-server-bin (concat lean4-home "/src/Lean/Server/build/bin/Watchdog"))
(defconst lean4-worker-bin (concat lean4-home "/src/Lean/Server/build/bin/FileWorker"))
(defconst lean4-lib (concat lean4-home "/build/release/stage1/lib/lean/"))

(lsp-register-client
 (make-lsp-client :new-connection (lsp-stdio-connection lean4-server-bin)
                  :major-modes '(lean4-lsp-mode)
                  :environment-fn (lambda ()
                                    '(("LEAN_PATH" . lean4-lib)
                                      ("LEAN_WORKER_PATH" . lean4-worker-bin)
                                      ;; Set to dump LSP communications
                                      ;("LEAN_SERVER_LOG_DIR" . "my/log/dir")
                                      ))
                  :server-id 'lean4-lsp))

(add-hook 'lean4-lsp-mode-hook #'lsp)
