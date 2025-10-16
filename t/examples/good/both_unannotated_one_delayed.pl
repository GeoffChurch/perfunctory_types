:- use_module(library(perfunctory_types)).

:- type color ---> r ; g ; b.
:- type _ ---> X = X. % (=)/2 demands arguments of the same type.

p(r). % ok, type(p) = p(color)
p(g). % ok, type(g) = color
p(X) :- X = b. % ok, type(b) = color
p(X) :- q(X). % ok, q's unknown type subsumes q(color).

q(r). % okay, type(q) = q(color), which trivially subsumes q(color).
