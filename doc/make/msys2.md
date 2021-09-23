[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

# Lean for Windows

A native Lean binary for Windows can be generated using [MSYS2][msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++14 compiler.

An alternative to MSYS2 is to use [Lean in Windows WSL](wsl.md).

## Installing dependencies

[The official webpage of MSYS2][msys2] provides one-click installers.
Once installed, you should run the "MSYS2 MinGW 64-bit shell" from the start menu.
(The one that runs `mingw64.exe`)
Do not run "MSYS2 MSYS" instead!
MSYS2 has a package management system, [pacman][pacman], which is used in Arch Linux.

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
pacman -S make python mingw-w64-x86_64-cmake mingw-w64-x86_64-clang mingw-w64-x86_64-ccache git unzip diffutils binutils
```

You should now be able to run these commands:

```bash
clang --version
cmake --version
```

Then follow the [generic build instructions](index.md) in the MSYS2
MinGW shell, using:
```
cmake ../.. -G "Unix Makefiles"  -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
```
instead of `cmake ../..`. This ensures that cmake will call `sh` instead of `cmd.exe`
for script tasks and it will use the clang compiler instead of gcc, which is required.

## Install lean

Follow the steps in [Dev setup using
elan](../dev/index.md#dev-setup-using-elan) regarding installation of the
bits you just built.  Note that in an msys2 environment `elan-init.sh`
reports you need to add `%USERPROFILE%\.elan\bin` to your path, but of
course in msys2 that needs to be a valid linux style path, like this:
```bash
export PATH="$PATH:/c/users/$USERNAME/.elan/bin"
```

## Running

You can run `lean --version` to see if your binaries work.

If you want a version that can run independently of your MSYS install
then you need to copy the following dependent DLL's from where ever
they are installed in your MSYS setup:

- libgcc_s_seh-1.dll
- libstdc++-6.dll
- libgmp-10.dll
- libwinpthread-1.dll

The following linux command will do that:

```bash
cp $(ldd lean.exe | cut -f3 -d' ' | grep mingw) .
```

## Trouble shooting

**-bash: gcc: command not found**

Make sure `/mingw64/bin` is in your PATH environment.  If it is not then
check you launched the MSYS2 MinGW 64-bit shell from the start menu.
(The one that runs `mingw64.exe`).
