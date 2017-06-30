@ECHO OFF

SET LEANDIR=%~dp0%../
SET LIBDIR=%LEANDIR%\lib\lean
IF NOT EXIST %LIBDIR% SET LIBDIR=%LEANDIR%
SET LEAN_PATH=%LIBDIR%\library;%LIBDIR%\leanpkg
SET PATH=%LEANDIR%\bin;%PATH%

lean --run %LIBDIR%\leanpkg\leanpkg\main.lean %*
