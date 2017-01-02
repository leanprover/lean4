This is the emacs mode for the [Lean theorem prover][lean].

[lean]: https://github.com/leanprover/lean

Quick-start
===========

If you have built lean from source, all that is necessary is to call the
`leanemacs_build` script which automatically installs all the dependencies and
opens up emacs with lean-mode loaded:
```
~/projects/lean/bin/leanemacs_build
```

If you have installed lean from a binary package, you can run `leanemacs`.

Trying It Out
=============

If things are working correctly, you should see the word ``Lean`` in the
Emacs mode line when you open a file with extension `.lean`. If you type
```lean
check id
```
the word ``check`` will be underlined, and hovering over it will show
you the type of ``id``. The mode line will show ``FlyC:0/1``, indicating
that there are no errors and one piece of information displayed.

Key Bindings and Commands
=========================

| Key                | Function                                                                        |
|--------------------|---------------------------------------------------------------------------------|
| <kbd>M-.</kbd>     | jump to definition in source file (`lean-find-definition`)                      |
| <kbd>TAB</kbd>     | tab complete identifier, option, filename, etc. (`lean-tab-indent-or-complete`) |
| <kbd>C-c C-k</kbd> | shows the keystroke needed to input the symbol under the cursor                 |
| <kbd>C-c C-g</kbd> | show goal in tactic proof (`lean-show-goal-at-pos`)                             |
| <kbd>C-c C-x</kbd> | execute lean in stand-alone mode (`lean-std-exe`)                               |
| <kbd>C-c C-n</kbd> | toggle next-error-mode: shows next error in dedicated lean-info buffer          |
| <kbd>C-c C-r</kbd> | restart the lean server                                                         |
| <kbd>C-c ! n</kbd> | flycheck: go to next error                                                      |
| <kbd>C-c ! p</kbd> | flycheck: go to previous error                                                  |
| <kbd>C-c ! l</kbd> | flycheck: show list of errors                                                   |

In the default configuration, the Flycheck annotation `FlyC:n/n` indicates the
number of errors / responses from Lean; clicking on `FlyC` opens the Flycheck menu.

Requirements
============

``lean-mode`` requires [Emacs 24][emacs24] or later and the following
packages, which can be installed via <kbd>M-x package-install</kbd>:
[dash][dash], [dash-functional][dash], [f][f], [s][s], [company][company],
[flycheck][flycheck], and [fill-column-indicator][fci].

[emacs24]: http://www.gnu.org/software/emacs
[dash]: https://github.com/magnars/dash.el
[f]: https://github.com/rejeep/f.el
[s]: https://github.com/magnars/s.el
[company]: http://company-mode.github.io/
[flycheck]: http://www.flycheck.org/manual/latest/index.html
[fci]: https://github.com/alpaker/Fill-Column-Indicator

Installation
============

You can also include lean-mode permanently in your emacs init file.  In this
case, just put the following code in your Emacs init file (typically `~/.emacs.d/init.el`):
```elisp
;; You need to modify the following two lines:
(setq lean-rootdir "~/projects/lean")
(setq lean-emacs-path "~/projects/lean/src/emacs")

(setq lean-mode-required-packages '(company dash dash-functional f
                               flycheck let-alist s seq))

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
(package-initialize)
(let ((need-to-refresh t))
  (dolist (p lean-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))

(setq load-path (cons lean-emacs-path load-path))

(require 'lean-mode)
```

If you already have the dependencies installed, the following three lines suffice:
```elisp
;; You need to modify the following two lines:
(setq lean-rootdir "~/projects/lean")
(setq load-path (cons "~/projects/lean/src/emacs" load-path))
(require 'lean-mode)
```

Known Issues and Possible Solutions
===================================

Unicode
-------

If you experience a problem rendering unicode symbols on emacs,
please download the following fonts and install them on your machine:

 - [Quivira.ttf](http://www.quivira-font.com/files/Quivira.ttf)
 - [Dejavu Fonts](http://sourceforge.net/projects/dejavu/files/dejavu/2.35/dejavu-fonts-ttf-2.35.tar.bz2)
 - [NotoSans](https://github.com/googlei18n/noto-fonts/blob/master/hinted/NotoSans-Regular.ttc?raw=true)
 - [NotoSansSymbols](https://github.com/googlei18n/noto-fonts/blob/master/unhinted/NotoSansSymbols-Regular.ttf?raw=true)

Then, have the following lines in your emacs setup to use `DejaVu Sans Mono` font:

```elisp
(when (member "DejaVu Sans Mono" (font-family-list))
  (set-face-attribute 'default nil :font "DejaVu Sans Mono-11"))
```

You may also need to install [emacs-unicode-fonts](https://github.com/rolandwalker/unicode-fonts) package.

 - Run `M-x package-refresh-contents`, `M-x package-install`, and type `unicode-fonts`.
 - Add the following lines in your emacs setup:

   ```lisp
(require 'unicode-fonts)
(unicode-fonts-setup)
   ```

"Variable binding depth exceeds max-specpdl-size" Error
---------------------------------------------------------

See [Issue 906](https://github.com/leanprover/lean/issues/906) for details.
[Moritz Kiefer](https://github.com/cocreature) reported that `proofgeneral`
comes with an old version of `mmm-mode` (0.4.8, released in 2004) on ArchLinux
and it caused this problem. Either removing `proofgeneral` or upgrading
`mmm-mode` to the latest version (0.5.1 as of 2015 Dec) resolves this issue.

Contributions
=============

Contributions are welcome!

Install [Cask](https://github.com/cask/cask) if you haven't already, then:

    $ cd /path/to/lean/src/emacs
    $ cask

Run all tests with:

    $ make
