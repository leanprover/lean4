/-!
This test checks how Markdown docstring highlighting measures indentation. The indentation that is
stripped from each line is the least indentation of the non-blank lines after the first, as in the
stored docstring. The columns of the delimiters do not limit it, and a line that follows a blank
line counts toward it.
-/

/--
    The content of this docstring is indented four columns past its delimiters.

    This is a paragraph, because it is at the least indentation.

        This line is indented code.
-/
def pastDelimiters := ()

/--
The first line does not count toward the indentation.

  The least-indented line after the first follows a blank line.

      This line is indented code.
-/
def afterBlankLine := ()

--^ textDocument/semanticTokens/full
