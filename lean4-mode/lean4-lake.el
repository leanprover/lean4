(defun lean4-lake-find-dir-in (dir)
  (when dir
    (or (lean4-lake-find-dir-in (f-parent dir))
        (when (f-exists? (f-join dir "lakefile.lean")) dir))))

(defun lean4-lake-find-dir ()
  (and (buffer-file-name)
       (lean4-lake-find-dir-in (f-dirname (buffer-file-name)))))

(defun lean4-lake-find-dir-safe ()
  (or (lean4-lake-find-dir)
      (error (format "cannot find lakefile.lean for %s" (buffer-file-name)))))

(defun lean4-lake-build ()
  "Call lake build"
  (interactive)
  (let* ((default-directory (file-name-as-directory (lean4-lake-find-dir-safe))))
    (with-existing-directory
      (compile "lake build"))))

(provide 'lean4-lake)
