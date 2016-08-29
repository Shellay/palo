yalog
==============

This is a mini-module for experimenting basic *datalog* within *Python* environment. Features include:

<!-- + knowledge base *KB* with `dict` indexing -->
+ mini-engine with *backward-chain* algorithm for inference process
+ `metaclass` frontend for easy-writing **facts** and **rules** of *KB*



## First Example

A *KB* can be defined like with ease in *prolog*-like style:

``` python
from yalog import var, kbmeta

class kb(metaclass=kbmeta):

    # Facts

    father('ooopa', 'opa')
    father('opa', 'ucl')
    father('opa', 'pa')
    mother('oma', 'pa')
    father('pa', 'a')
    father('pa', 'b')
    mother('mum', 'a')
    mother('mum', 'b')

    # Definite clauses

    grandfather(X, Y) <= [
        father(X, Z), father(Z, Y)
    ]

    parent(X, Y) <= father(X, Y)
    parent(X, Y) <= mother(X, Y)

    sibling(X, Y) <= [
        parent(Z, X) , parent(Z, Y) , (X != Y)
    ]

    ancester(X, Y) <= father(X, Y)
    ancester(X, Y) <= [
        father(X, Z), ancester(Z, Y)
    ]

```

and goals can be queried by simply accessing attributes `kb` with corresponding rule names:

``` python
from yalog import var

q = kb.sibling(var.X, var.Y)

>>> list(q)
[{x: 'ucl', y: 'pa'},
 {x: 'pa', y: 'ucl'},
 {x: 'a', y: 'b'},
 {x: 'b', y: 'a'},
 {x: 'a', y: 'b'},
 {x: 'b', y: 'a'}]

q = kb.ancester(var.W, 'a')

>>> list(q)
[{W: 'pa'}, {W: 'ooopa'}, {W: 'opa'}]
```

note the repetition in query results is valid due to the alternative rules for `parent` during inferencing `sibling`.

Equality and non-equality are supported by extending the `back-chaining-OR` function.

<!--
The trick is to support `__getitem__` method for the `dict`-like reader returned by `kbmeta.__prepare__` so that any identifier get automatically declared and returned as a dedicated object.
-->

## TODO

- Support `NOT` expressions in definite clauses.

