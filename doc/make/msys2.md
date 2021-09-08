[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

Lean for Windows
----------------

A native Lean binary for Windows can be generated using [MSYS2][msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++14 compiler.


## Installing dependencies

[The official webpage of MSYS2][msys2] provides one-click installers.
Once installed, you should run the "MSYS2 MinGW 64-bit shell" from the start menu.
(The one that runs `mingw64.exe`)
Do not run "MSYS2 MSYS" instead!
MSYS2 has a package management system, [pacman][pacman], which is used in Arch Linux.

Here are the commands to install all dependencies needed to compile Lean on your machine.

```bash
pacman -S make mingw-w64-x86_64-cmake mingw-w64-x86_64-ccache mingw-w64-x86_64-gcc git
```

You should now be able to run these commands:

```bash
gcc --version
cmake --version
```

Then follow the [generic build instructions](index.md) in the MSYS2 MinGW shell, using
`cmake ../.. -G "Unix Makefiles"` instead of `cmake ../..`. This ensures that cmake will call `sh` instead
of `cmd.exe` for script tasks.

## Install lean

You can use the `install` ninja/make target to install Lean into, by default,
`./build/release/stage1/msys64/lean/`. To change this, add `-DCMAKE_INSTALL_PREFIX=path/you/want`
to your initial cmake invocation.

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

**file INSTALL cannot make directory "C:/Program Files (x86)/LEAN/include/lean": No such file or directory**

If you get this error from `make install` or `ninja install` then it
may be a permissions issue since the default "C:/Program Files
(x86)/LEAN" install target folder is not writable by non-admin users.
If you really want lean installed there then try running `make
install` from an admin command prompt.  

If you want to change the default install location use this command line:
```
cmake ../.. -G "Unix Makefiles" -DCMAKE_INSTALL_PREFIX=~/lean4
```
This will move the lean4 installation location to your home folder which is
writable by default.  Note that you have to delete any previous `build/release` folder you created otherwise the new CMAKE_INSTALL_PREFIX will not
be used.