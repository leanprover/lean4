# Compiling Lean with Visual Studio

WARNING: Compiling Lean with Visual Studio doesn't currently work.
There's an ongoing effort to port Lean to Visual Studio.
The instructions below are for VS 2017.

In the meantime you can use [MSYS2](msys2.md) or [WSL](wsl.md).

## Installing dependencies

First, install `vcpkg` from https://github.com/Microsoft/vcpkg if you haven't
done so already.
Then, open a console in the directory you cloned `vcpkg` to, and type:
`vcpkg install mpir` for the 32-bit library or
`vcpkg install mpir:x64-windows` for the x64 one.

In Visual Studio, use the "open folder" feature and open the Lean directory.
Go to the `CMake->Change CMake Settings` menu. File `CMakeSettings.json` opens.
In each of the targets, add the following snippet (i.e., after every
`ctestCommandArgs`):

```json
    "variables": [
      {
        "name": "CMAKE_TOOLCHAIN_FILE",
        "value": "C:\\path\\to\\vcpkg\\scripts\\buildsystems\\vcpkg.cmake"
      }
    ]
```

## Enable Intellisense

In Visual Studio, press Ctrl+Q and type `CppProperties.json` and press Enter.
Ensure `includePath` variables include `"${workspaceRoot}\\src"`.


## Build Lean

Press F7.
