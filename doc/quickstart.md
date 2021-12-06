# Quickstart

These instructions will walk you through setting up Lean using the "basic" setup and VS Code as the editor.
See [Setup](./setup.md) for other ways and more details on setting up Lean.

1. Install [VS Code](https://code.visualstudio.com/).

1. Create a new folder called `foo` and add a file named `hello.lean`
containing the following:

    ```lean
    import Lake
    #eval Lake.leanVersionString
    ```

    and a file named `lean-toolchain` containing just this:

    ```
    leanprover/lean4:nightly
    ```

1. Open this folder in VS Code and install the `lean4` extension.

    ![installing the vscode-lean4 extension](images/code-ext.png)

1. Open the file named `foo.lean` and you should see the following popup:
    ![elan](images/install_elan.png)

    Click the "Install Lean using Elan" link and follow the progress
    pressing ENTER in the terminal window to install lean.  You should see some progress output like this:

    ```
    info: syncing channel updates for 'nightly'
    info: latest update on nightly, lean version nightly-2021-12-05
    info: downloading component 'lean'
    ```

    You should get a syntax-highlighted file with a "Lean Infoview" on the right.  You will see the output of the #eval statement when
    you place your cursor at the end of the #eval statement.

    ![successful setup](images/code-success.png)

1. You are set up! You can now also run `lake init foo` from the command line to create a package, followed by `lake build` to get an executable version of your Lean program.

Note: Packages **have** to be opened using "File > Open Folder..." for imports to work.
Saved changes are visible in other files after running "Lean 4: Refresh File Dependencies" (`Ctrl+Shift+X`).