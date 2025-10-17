:- module(perfunctory_types, []).

:- reexport(library(perfunctory_types/exports)).

:- dynamic term_to_check/1.

rule_head(H :- _, Head) => Head = H.
rule_head(Fact,   Head) => Head = Fact.

term_functor(Term, F) :-
    functor(Term, F, _).

fst_pair(X, X-_).

init_infers -->
    maplist(rule_head),
    maplist(term_functor),
    sort,
    maplist(fst_pair),
    list_to_assoc.

unwanted_term(begin_of_file).
unwanted_term(:- _).

check_and_infer(Infers, Term, Type) :-
    $(typecheck(Infers, Term, Type)),
    % Unify rule's head type with predicate's inferred type.
    $(rule_head(Term, Head)),
    $(term_functor(Head, F)),
    $(get_assoc(F, Infers, HeadType_)),
    $(rule_head(Type, HeadType)), % (:-)/2 gets skolemized so we can take its head as though it were a term.
    (HeadType_ = HeadType
    -> true
    ;  throw(error(ill_typed(failed_unification(HeadType_ = HeadType)), _))
    ).

user:term_expansion(end_of_file, []) :-
    % Collect stored terms
    findall(Term, retract(term_to_check(Term)), Terms),
    init_infers(Terms, Infers),
    writeln('Terms:'),
    maplist(writeln, Terms),
    maplist(check_and_infer(Infers), Terms, _).

user:term_expansion(Term, [Term]) :-
    \+ unwanted_term(Term),
    assertz(term_to_check(Term)). % Store term
