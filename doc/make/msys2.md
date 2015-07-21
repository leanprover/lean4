[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

Lean for Windows
----------------

A native Lean binary for Windows can be generated using [msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++11 compiler.


## Installing dependencies

Lean requires Python2 or Python3. If you do not have a Python installation on your machine, 
please download and install one from [Python.org](https://www.python.org/downloads/windows).
Also please make sure that your `PATH` environment variable includes the installed 
Python directory (i.e. `C:\Python27`).

[The official webpage of msys2][msys2] provides one-click installers.
We assume that you install [msys2][msys2] at `c:\msys64`.
Once installed it, you can run msys2 shell from the start menu.
It has a package management system, [pacman][pacman], which is used in Arch Linux.

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
# Install gcc (4.9.1)
pacman -S mingw-w64-x86_64-gcc

# Install mpfr, gmp, lua
pacman -S mingw-w64-x86_64-mpfr mingw-w64-x86_64-gmp mingw-w64-x86_64-lua

# Install ninja, cmake
pacman -S mingw-w64-x86_64-ninja mingw-w64-x86_64-cmake

# Install git
pacman -S git
```

Close the msys2 shell and add `c:\msys64\mingw64\bin` into the `PATH`
environment variable.

 - Windows 7/8: Control Panel > System and Security > System > Advanced
   System Settings > Environment Variables... > Edit User variable
   `Path`

## Build Lean

In the [msys2] shell, execute the following commands.

```bash
cd /c/
git clone https://github.com/leanprover/lean
git clone http://github.com/leanprover/emacs-dependencies
mkdir -p lean/src/emacs/dependencies
cp -R emacs-dependencies/* lean/src/emacs/dependencies
cd lean
mkdir build && cd build
cmake -D CMAKE_CXX_COMPILER=g++.exe -G Ninja ../src
ninja
```

## Build Lean using Boost

To install Boost in the [msys2] shell, use the following command:

```bash
pacman -S mingw-w64-x86_64-boost
```

In the [msys2] shell, execute the following commands.

```bash
cd /c/
git clone https://github.com/leanprover/lean
cd lean
mkdir build && cd build
cmake -D CMAKE_CXX_COMPILER=g++.exe -D BOOST=ON -G Ninja ../src
ninja
```
