# Documentation

The Lean `doc` folder contains the [Lean Manual](https://lean-lang.org/lean4/doc/) and is
authored in a combination of markdown (`*.md`) files and literate Lean files.  The .lean files are
preprocessed using a tool called [LeanInk](https://github.com/leanprover/leanink) and
[Alectryon](https://github.com/Kha/alectryon) which produces a generated markdown file.  We then run
`mdbook` on the result to generate the html pages.


## Settings

We are using the following settings while editing the markdown docs.

```json
{
    "files.insertFinalNewline": true,
    "files.trimTrailingWhitespace": true,
    "[markdown]": {
        "rewrap.wrappingColumn": 70
    }
}
```

## Build

### Using Nix

Building the manual using Nix (which is what the CI does) is as easy as
```bash
$ nix build --update-input lean ./doc
```
You can also open a shell with `mdbook` for running the commands mentioned below with
`nix develop ./doc#book`. Otherwise, read on.

### Manually

To build and test the book you have to preprocess the .lean files with Alectryon then use our own
fork of the Rust tool named [mdbook](https://github.com/leanprover/mdbook). We have our own fork of
mdBook with the following additional features:

* Add support for hiding lines in other languages
  [#1339](https://github.com/rust-lang/mdBook/pull/1339)
* Make `mdbook test` call the `lean` compiler to test the snippets.
* Ability to test a single chapter at a time which is handy when you
are working on that chapter.  See the `--chapter` option.

So you need to setup these tools before you can run `mdBook`.

1. install [Rust](https://www.rust-lang.org/tools/install)
which provides you with the `cargo` tool for building rust packages.
Then run the following:
    ```bash
    cargo install --git https://github.com/leanprover/mdBook mdbook
    ```

1. Clone https://github.com/leanprover/LeanInk.git and run `lake build` then make the resulting
   binary available to Alectryon using e.g.
    ```bash
    # make `leanInk` available in the current shell
    export PATH=$PWD/build/bin:$PATH
    ```

1. Create a Python 3.10 environment.

1. Install Alectryon:
    ```
    python3 -m pip install git+https://github.com/Kha/alectryon.git@typeid
    ```

1. Now you are ready to process the `*.lean` files using Alectryon as follows:

    ```
    cd lean4/doc
    alectryon --frontend lean4+markup examples/palindromes.lean --backend webpage -o palindromes.lean.md
    ```

    Repeat this for the other .lean files you care about or write a script to process them all.

1. Now you can build the book using:
    ```
    cd lean4/doc
    mdbook build
    ```

This will put the HTML in a `out` folder so you can load `out/index.html` in your web browser and
it should look like https://lean-lang.org/lean4/doc/.

1. It is also handy to use e.g. [`mdbook watch`](https://rust-lang.github.io/mdBook/cli/watch.html)
   in the `doc/` folder so that it keeps the html up to date while you are editing.

    ```bash
    mdbook watch --open  # opens the output in `out/` in your default browser
    ```

## Testing Lean Snippets

You can run the following in the `doc/` folder to test all the lean code snippets.

    ```bash
    mdbook test
    ```

and you can use the `--chapter` option to test a specific chapter that you are working on:

    ```bash
    mdbook test --chapter Array
    ```

Use chapter name `?` to get a list of all the chapter names.
