# Quickstart

These instructions will walk you through setting up Lean using the "basic" setup and VS Code as the editor.
See [Setup](./setup.md) for other ways and more details on setting up Lean.

1. Install [VS Code](https://code.visualstudio.com/).

1. Launch VS Code and install the `lean4` extension.

    ![installing the vscode-lean4 extension](images/code-ext.png)

1. Create a new file using  "File > New File" and click the `Select a language` link and type in `lean4` and hit ENTER.  You should see the following popup:
    ![elan](images/install_elan.png)

    Click the "Install Lean using Elan" link and follow the progress
    pressing ENTER in the terminal window to install lean.  You should see some progress output like this:

    ```
    info: syncing channel updates for 'nightly'
    info: latest update on nightly, lean version nightly-2021-12-05
    info: downloading component 'lean'
    ```

1. While it is installing you can paste the following Lean program into the new file:

    ```lean
    #eval Lean.versionString
    ```

    When the install finishes the Lean Language Server should start automatically and you should get a syntax-highlighting and a "Lean Infoview" popping up on the right.  You will see the output of the #eval statement when
    you place your cursor at the end of the #eval statement.

    ![successful setup](images/code-success.png)

You are set up!

## Create a Lean Project

You can now create a Lean project in a new folder. Run `lake init foo` from the "View > Terminal" to create a package, followed by `lake build` to get an executable version of your Lean program.
On Linux/macOS, you first have to follow the instructions printed by the Lean installation or log out and in again for the Lean executables to be available in you terminal.

Note: Packages **have** to be opened using "File > Open Folder..." for imports to work.
Saved changes are visible in other files after running "Lean 4: Refresh File Dependencies" (`Ctrl+Shift+X`).

## Troubleshooting

**The InfoView says "Waiting for Lean server to start..." forever.**

Check that the VS Code Terminal is not prompting you with `Press ENTER key to start Lean:`.  If so click in the terminal window and pressthe  ENTER key.
If that doesn't work try also running the VS Code command `Developer: Reload Window`.
