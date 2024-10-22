[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

# Lean for Windows

A native Lean binary for Windows can be generated using [MSYS2][msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++14 compiler.

An alternative to MSYS2 is to use [Lean in Windows WSL](wsl.md).

While not necessary for pure building, you should first activate [Developer
Mode](https://docs.microsoft.com/en-us/windows/apps/get-started/enable-your-device-for-development)
(Settings > Update & Security > For developers > Developer Mode),
which will allow Lean to create symlinks that e.g. enable go-to-definition in
the stdlib.

## Installing the Windows SDK

Install the Windows SDK from [Microsoft](https://developer.microsoft.com/en-us/windows/downloads/windows-sdk/).
The oldest supported version is 10.0.18362.0. If you installed the Windows SDK to the default location,
then there should be a directory with the version number at `C:\Program Files (x86)\Windows Kits\10\Include`.
If there are multiple directories, only the highest version number matters.

## Installing dependencies

[The official webpage of MSYS2][msys2] provides one-click installers.
Once installed, you should run the "MSYS2 CLANG64" shell from the start menu (the one that runs `clang64.exe`).
Do not run "MSYS2 MSYS" or "MSYS2 MINGW64" instead!
MSYS2 has a package management system, [pacman][pacman].

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
pacman -S make python mingw-w64-clang-x86_64-cmake mingw-w64-clang-x86_64-clang mingw-w64-clang-x86_64-ccache mingw-w64-clang-x86_64-libuv mingw-w64-clang-x86_64-gmp git unzip diffutils binutils
```

You should now be able to run these commands:

```bash
clang --version
cmake --version
```

Then follow the [generic build instructions](index.md) in the MSYS2
MinGW shell, using:
```
cmake --preset release -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
```
instead of `cmake --preset release`. This will use the clang compiler instead of gcc, which is required with msys2.

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

- libc++.dll
- libgmp-10.dll
- libuv-1.dll
- libwinpthread-1.dll

The following linux command will do that:

```bash
cp $(ldd lean.exe | cut -f3 -d' ' | grep mingw) .
```

However, if you plan to use this build to compile lean programs
to executable binaries using `lake build` in normal Windows command
prompt outside of msys2 environment you will also need to add a windows
version clang to your path.

## Trouble shooting

**-bash: gcc: command not found**

Make sure `/clang64/bin` is in your PATH environment.  If it is not then
check you launched the MSYS2 CLANG64 shell from the start menu.
(The one that runs `clang64.exe`).
