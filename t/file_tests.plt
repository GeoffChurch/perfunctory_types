:- use_module(library(perfunctory_types/declaration)).

:- multifile user:message_hook/3.

:- dynamic error_happened/1.

file_error(File, Error) :-
    assertz((user:message_hook(Term, error, _Lines) :- assertz(error_happened(Term))),
            Ref),
    consult(File),
    $(retract(error_happened(Error))),
    erase(Ref),
    unload_file(File).

file_directory_path(F, D, P) :- directory_file_path(D, F, P).

example_file(Name, Path) :-
    predicate_property(file_error(_,_), file(ThisFile)),
    call_dcg(
        (
            file_directory_name,
            file_directory_path('examples/bad'),
            file_directory_path(Name)),
        ThisFile, Path).

:- begin_tests(file_tests, [cleanup(retract_all_types_and_aliases)]).

test(fail_intra_clause,
     [E == ill_typed(expected_type(ab), got_untyped_term(c))]) :-
    example_file('fail_intra_clause.pl', File),
    file_error(File, error(E, _)).

test(fail_inter_clause,
     [E == ill_typed(expected_type(ab), got_type(c)),
      blocked('semantic checking not yet implemented')]) :-
    example_file('fail_inter_clause.pl', File),
    file_error(File, error(E, _)).

:- end_tests(file_tests).
