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
      (compile (concat (lean4-get-executable "lake") " build")))))

(defun lean4-lake-lib-paths ()
  "Returns list of paths to package's oleans and its dependencies."
  (if-let ((dir (lean4-lake-find-dir))
	   (libdir (f-join dir "build" "lib"))
	   (deplibs (mapcar (lambda (pkg_path)
			      (f-join pkg_path "build" "lib"))
			    (f-directories (f-join dir "lean_packages")))))
    (append (list libdir) deplibs)))

(provide 'lean4-lake)
