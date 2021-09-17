Lean for Windows WSL
--------------------

For the most part setup in WSL is the same as [Ubuntu](Ubuntu-16.04.md).

This document provides additional information on how to setup Windows
VSCode remote debugging into your WSL environment using the lean
extension running in WSL.

It is recommended that you setup Ubuntu in [WSL 2](https://docs.microsoft.com/en-us/windows/wsl/compare-versions).

Then follow the [Basic lean4 Setup](../setup.md) in your WSL environment.

Specifically the following parts:
```shell
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain none
source ~/.profile
elan toolchain install leanprover/lean4:nightly
elan default leanprover/lean4:nightly
```

## Visual Studio Code setup on Windows

Install [Visual Studio Code](https://code.visualstudio.com/Download) on Windows.

Type `Ctrl+Shift+P` and select `Remote-WSL: Open Folder in WSL...` to
open a folder containing your hello world lean package.

## Troubleshooting

**[Error - 1:23:55 PM] Connection to server is erroring. Shutting down server.**

Watchdog error: no such file or directory (error code: 2)
  file: D:\Temp\lean_examples\logs/wdIn.txt