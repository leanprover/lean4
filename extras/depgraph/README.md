Generating Dependency Graph
============================

Usage:

    leandeps.py [options] dir/file

If argument is a directory, all source files below that directory will be included in the graph.

 - `-h`/`--help` : prints this message
 - `-o <file>`/`--output <file>` : saves the DOT output in the specified file

If no output file is specified, `deps.gv` and `deps.gv.dot` is written to.

You need the [graphviz python library][python-graphviz]. If you already have [pip][pip], you can do:

    pip install graphviz

The resulting `deps.gv.dot` file can be run through [dot][graphviz] (and maybe tred first) from graphviz to produce, 
e.g., an svg file. For example:

    tred deps.gv.dot > treddeps.dot
    dot -Tsvg -O treddeps.dot

[python-graphviz]: https://pypi.python.org/pypi/graphviz
[graphviz]: http://www.graphviz.org/
[pip]: https://pip.readthedocs.org/en/stable/installing/#install-pip
