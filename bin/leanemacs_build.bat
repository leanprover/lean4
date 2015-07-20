SET MY_PATH=%~dp0
SET LEAN_ROOTDIR=%MY_PATH%/..
SET LEAN_EMACS_PATH=%MY_PATH%/../src/emacs
emacs -load %LEAN_EMACS_PATH%/load-lean.el
