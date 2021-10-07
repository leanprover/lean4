# Quickstart

These instructions will walk you through setting up Lean using the "basic" setup and VS Code as the editor.
See [Setup](./setup.md) for other ways and more details on setting up Lean.

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

1. You are set up! Try opening a Lean folder containing a package file `leanpkg.toml`. You can create your own packages using `leanpkg init` on the command line.
   Packages **have** to be opened using "File > Open Folder..." for imports to work.
   Saved changes are visible in other files after running "Lean 4: Refresh File Dependencies" (`Ctrl+Shift+X`).
