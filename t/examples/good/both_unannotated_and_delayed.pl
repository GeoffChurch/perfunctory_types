:- use_module(library(perfunctory_types)).

:- discontiguous p/1, q/1.

:- type list(X) ---> [] ; [X|list(X)].
:- type color ---> r ; g ; b.
:- type direction ---> n ; s ; e ; w.

p([]). % ok, type(p) = p(list(P)) for some unknown P
q([[]]). % ok, type(q) = q(list(list(Q))) for some unknown Q
p(X) :- q(X). % ok, type(X) = list(P), and list(Q) subsumes P, forcing P to be of form list(R) for some R subsumed by Q
p([[r]]). % ok, type(p) = p(list(list(color))), so R = color, and type(q) = q(list(list(Q))) for some unknown Q subsuming color
q([[r]]). % ok, Q = color