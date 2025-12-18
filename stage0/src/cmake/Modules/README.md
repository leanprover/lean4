# CMake modules required for building Lean

The files `GetGitRevisionDescription.cmake`, `GetGitRevisionDescription.cmake.in` and
`FindWindowsSDK.cmake` are part of the `cmake-modules` project by Rylie Pavlik. They
are licensed under the Boost Software License, Version 1.0.

The modules should be updated when a new version of the Windows SDK is released. To do
so, obtain an up-to-date checkout of the `cmake-modules` project from
https://github.com/rpavlik/cmake-modules and run the following command from the root
of the `cmake-modules` repository:

```bash
./update-modules.sh /path-to-lean4-repo/src/cmake/Modules
```
