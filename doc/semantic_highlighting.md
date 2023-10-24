Semantic Highlighting
---------------------

The Lean language server provides semantic highlighting information to editors. In order to benefit from this in VSCode, you may need to activate the "Editor > Semantic Highlighting" option in the preferences (this is translates to `"editor.semanticHighlighting.enabled": true,`
in `settings.json`). The default option here is to let your color theme decides whether it activates semantic highlighting (the default themes Dark+ and Light+ do activate it for instance).

However this may be insufficient if your color theme does not distinguish enough syntax categories or distinguishes them very subtly. For instance the default Light+ theme uses color `#001080` for variables. This is awfully close to `#000000` that is used as the default text color. This makes it very easy to miss an accidental use of [auto bound implicit arguments](https://lean-lang.org/lean4/doc/autobound.html). For instance in
```lean
def my_id (n : nat) := n
```
maybe `nat` is a typo and `Nat` was intended. If your color theme is good enough then you should see that `n` and `nat` have the same color since they are both marked as variables by semantic highlighting. If you rather write `(n : Nat)` then `n` keeps its variable color but `Nat` gets the default text color.

If you use such a bad theme, you can fix things by modifying the `Semantic Token Color Customizations` configuration. This cannot be done directly in the preferences dialog but you can click on "Edit in settings.json" to directly edit the settings file. Beware that you must save this file (in the same way you save any file opened in VSCode) before seeing any effect in other tabs or VSCode windows.

In the main config object, you can add something like
```
"editor.semanticTokenColorCustomizations": {
        "[Default Light+]": {"rules": {"function": "#ff0000", "property": "#00ff00", "variable": "#ff00ff"}}
    },
```
The colors in this example are not meant to be nice but to be easy to spot in your file when testing. Of course you need to replace `Default Light+` with the name of your theme, and you can customize several themes if you use several themes. VSCode will display small colored boxes next to the HTML color specifications. Hovering on top of a color specification opens a convenient color picker dialog.

In order to understand what `function`, `property` and `variable` mean in the above example, the easiest path is to open a Lean file and ask VSCode about its classification of various bits of your file. Open the command palette with Ctrl-shift-p (or ⌘-shift-p on a Mac) and search for "Inspect Editor Tokens and Scopes" (typing the word "tokens" should be enough to see it). You can then click on any word in your file and look if there is a "semantic token type" line in the displayed information.
