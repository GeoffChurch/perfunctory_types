:- use_module("../../../prolog/typecheck_semantic").

:- (type T ---> a ; b), % T has two constructors, a and b.
   (type _ ---> p(T)). % p/1 demands an argument of type T, i.e. a or b.
:- type _ ---> X = X. % (=)/2 demands arguments of the same type.

p(a).
p(b).
p(X) :- X = a.
p(X) :- q(X). % Fails because q's inferred type is (type _ ---> q(c)).

q(c).
