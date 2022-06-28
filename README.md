# Implementation of a method to verify pattern elimination in Constructor based Term Rewrite Systems

For more details, please see the papers presented at:
<ul>
  <li><a href="https://hal.inria.fr/hal-02476012/">LOPSTR 2020</a></li>
  <li><a href="https://hal.inria.fr/hal-03528254">PPDP 2021</a></li>
</ul>

## Compilation instruction:
```console
$ ghc Main
```

## Execution instruction:
The execution take a path towards a file to parse and analyze
```console
$ ./Main example_file
```

The execution returns a map of not semantics preserving rules of the CTRS
with terms, which ground semantics are included in the deep semantics of the
right-hand side, but that do not satisfy the pattern-free property required
by the left-hand side.

You can create your own example files for testing.
Do not hesitate to look at existing example files for syntax guidance.

An online interface is also available <a href="http://htmlpreview.github.io/?https://github.com/plermusiaux/pfree_check/blob/webnix/out/index.html">here</a>.
