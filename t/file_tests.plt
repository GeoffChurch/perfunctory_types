:- use_module("../prolog/core").

:- dynamic error_happened/1.

file_error(File, Error) :-
    assertz((user:message_hook(Term, error, _Lines) :-
		 assertz(error_happened(Term))), Ref),
    consult(File),
    $(retract(error_happened(Error))),
    erase(Ref),
    unload_file(File).

:- begin_tests(file_tests, [cleanup(retract_all_types_and_aliases)]).

test(fail_intra_clause,
     [E == ill_typed(expected_type(ab), got_untyped_term(c))]) :-
    file_error("examples/bad/fail_intra_clause.pl", error(E, _)).

test(fail_inter_clause,
     [E == ill_typed(expected_type(ab), got_type(c)),
      blocked('semantic checking not yet implemented')]) :-
    file_error("examples/bad/fail_inter_clause.pl", error(E, _)).

:- end_tests(file_tests).
