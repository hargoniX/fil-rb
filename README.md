# FiL RB trees
A Red-Black-Tree Formalization for LMU's [Formalization in Lean (FiL) WS 2024/25](https://www.tcs.ifi.lmu.de/lehre/ws-2024-25/forma_lean_de.html).

## Graphviz
```lean
def exTree1 : Raw Int := .node (.node .nil 0 .red .nil) 2 .black (.node .nil 3 .red .nil)
#eval IO.FS.writeFile "examples/tree-preinsert.gv" exTree1.toGraphviz
```

Then execute the following command on a machine with graphviz installed:
```bash
dot -Tsvg tree.gv -o tree.svg
```
or the following for png:
```bash
dot -T png tree.gv -O
```
and you can look at the rendered file.
