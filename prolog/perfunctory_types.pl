:- module(typecheck_syntactic, []).

:- reexport(library(perfunctory_types/declaration)).

:- dynamic term_to_check/1.

user:term_expansion(end_of_file, []) :-
    forall(retract(term_to_check(Term)),
	   perfunctory_types:typecheck(Term, _)).

user:term_expansion(Term, [Term]) :-
    assertz(term_to_check(Term)).
