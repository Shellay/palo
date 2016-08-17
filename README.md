yalog
==============

This is a mini-module for experimenting basic *datalog* within *Python* environment. Features include:

<!-- + knowledge base *KB* with `dict` indexing -->
+ mini-engine with *backward-chain* algorithm for inference process
+ `metaclass` frontend for easy-writing **facts** and **rules** of *KB*



## First Example

A *KB* can be defined like with ease in *prolog*-style:

``` python
from yalog import kbmeta

class kb(metaclass=kbmeta):

    # Facts

    father['opa', 'pa']
    mother['oma', 'pa']
    father['pa', 'a']
    father['pa', 'b']
    mother['mum', 'a']
    mother['mum', 'b']
    not_eq['a', 'b']
    not_eq['b', 'a']

    # Horn clauses

    grandfather[X, Y] = father[X, Z], father[Z, Y]
    parent[X, Y] = father[X, Y]
    parent[X, Y] = mother[X, Y]
    sibling[X, Y] = parent[Z, X], parent[Z, Y], not_eq[X, Y]
```

and goals can be queried by simply accessing `kb`\'s attributes with corresponding rule names:

``` python
>>> from yalog import var
>>> q = kb.sibling[var.X, var.Y]
>>> list(q)
[{X: 'a', Y: 'b'}, {X: 'b', Y: 'a'}, {X: 'a', Y: 'b'}, {X: 'b', Y: 'a'}]

>>> q = kb.sibling[var.Z, "b"]
>>> list(q)
[{Z: 'a'}, {Z: 'a'}]
```

note the repetition is valid due to the alternative rules for `parent` during inferencing `sibling`.

<!--
The trick is to support `__getitem__` method for the `dict`-like reader returned by `kbmeta.__prepare__` so that any identifier get automatically declared and returned as a dedicated object.
-->

## TODO

- Support goals defined with equality and non-equality.
