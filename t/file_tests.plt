:- use_module(library(perfunctory_types/declaration)).
:- use_module(library(apply), [maplist/2]).

:- multifile user:message_hook/3.

:- dynamic error_happened/1.

file_directory_path(F, D, P) :- directory_file_path(D, F, P).

with_example(File, Goal) :-
    retractall(error_happened(_)),
    retract_all_types_and_aliases,
    setup_call_cleanup(
        assertz((user:message_hook(Term, error, _Lines) :- assertz(error_happened(Term))),
                Ref),
        ( catch(consult(File), error(E, Ctx), assertz(error_happened(error(E, Ctx)))),
          call(Goal)
        ),
        ( erase(Ref),
          unload_file(File),
          retract_all_types_and_aliases,
          retractall(error_happened(_))
        )
    ).

examples_dir(Subdir, Dir) :-
    predicate_property(with_example(_,_), file(ThisFile)),
    call_dcg((file_directory_name, file_directory_path('examples'), file_directory_path(Subdir)), ThisFile, Dir).

example_files --> examples_dir, file_directory_path('*.pl'), expand_file_name.

assert_ill_typed(Term) :-
    functor(Term, ill_typed, _) -> true ; throw(error(not_ill_typed(Term), _)).

expect_bad(File) :-
    with_example(File,
                 ( findall(E, error_happened(error(E, _)), Errors),
                   Errors \= [],
                   maplist(assert_ill_typed, Errors)
                 )).

expect_good(File) :-
    with_example(File, \+ error_happened(_)).

:- begin_tests(file_tests, [cleanup(retract_all_types_and_aliases)]).

test(bad_examples_fail_with_ill_typed) :-
    example_files(bad, Files),
    Files \= [],
    maplist(expect_bad, Files).

test(good_examples_load_without_errors) :-
    example_files(good, Files),
    Files \= [],
    maplist(expect_good, Files).

:- end_tests(file_tests).
