:- use_module(library(perfunctory_types)).

:- (type T ---> a ; b), % T has two constructors, a and b.
   (type _ ---> p(T)). % p/1 demands an argument of type T, i.e. a or b.
:- type _ ---> X = X. % (=)/2 demands arguments of the same type.

p(a). % ok, a is in T.
p(b). % ok, b is in T.
p(X) :- X = a. % ok, a is in T.
p(X) :- q(X). % ok, q's unknown type subsumes type(q(X)) = q(T).

q(a). % ok, q has existential type q(T), which trivially subsumes q(T).
