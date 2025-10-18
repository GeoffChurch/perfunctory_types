:- use_module(library(perfunctory_types)).

:- type _ ---> p(_). % p is parametric

p(a). % ok, this clause's head has type p(a)
p(b). % FAIL, p(b) is syntactically well-formed but the predicate fails the semantic check
