:- use_module(library(perfunctory_types)).

:- type color ---> r ; g ; b.
:- type _ ---> X = X. % (=)/2 demands arguments of the same type.

p(r). % ok, p has type p(color)
p(g). % ok, g is a color
p(X) :- X = a. % ok, a is in T.
p(X) :- q(X). % ok, q's unknown type subsumes type(q(X)) = q(T).

q(c). % FAIL, q has existential type q(skolemize(c)), which does not subsume q(T).
