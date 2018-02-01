[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

Lean for Windows
----------------

A native Lean binary for Windows can be generated using [msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++11 compiler.


## Installing dependencies

[The official webpage of msys2][msys2] provides one-click installers.
We assume that you install [msys2][msys2] at `c:\msys64`.
Once installed it, you should run the "MSYS2 MinGW 64-bit shell" from the start menu.
It has a package management system, [pacman][pacman], which is used in Arch Linux.

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
pacman -S mingw-w64-x86_64-gcc mingw-w64-x86_64-ninja mingw-w64-x86_64-cmake git
```

Then follow the [generic build instructions](index.md) in the [msys2] shell.

## Install lean

You can use the `install` ninja/make target to install Lean into, by, default,
`C:\\User Programs (x86)\\LEAN`. To change this, add `-DCMAKE_INSTALL_PREFIX=path/you/want`
to your cmake invocation.
