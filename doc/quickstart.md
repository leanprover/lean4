# Quickstart

These instructions will walk you through setting up Lean using the "basic" setup and VS Code as the editor.
See [Setup](./setup.md) for other ways and more details on setting up Lean.

1. Install the latest Lean 4 nightly through [`elan`](https://github.com/Kha/elan): in any bash-compatible shell, run
    ```sh
    $ curl https://raw.githubusercontent.com/Kha/elan/master/elan-init.sh -sSf | sh -s -- --default-toolchain leanprover/lean4:nightly
    ```
See the `elan` link above for other installation options and details.
1. Install [VS Code](https://code.visualstudio.com/).
1. Open VS Code and install the `lean4` extension.  
![installing the vscode-lean4 extension](images/code-ext.png)
1. Create a new file with the extension `.lean` and add the following code:
    ```lean
    import Leanpkg
    
    #eval Leanpkg.leanVersionString
    ```
You should get a syntax-highlighted file with a "Lean Infoview" on the right that tells you the installed Lean version when placing your cursor on the last line.  
![successful setup](images/code-success.png)
1. You are set up! Try opening a Lean package with a `leanpkg.toml`. You can create your own packages using `leanpkg init` on the command line.
Packages **have** to be opened using "File > Open Folder..." for imports to work.
Saved changes are visibly in other files after running "Lean 4: Refresh File Dependencies" (`Ctrl+Shift+X`) in them.
