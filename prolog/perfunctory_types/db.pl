:- module(db, [get_type/2, get_types/1, get_alias/2, get_aliases/1, current_ctor/3, retract_ctor/3, retract_all_types_and_aliases/0, cyclesafe_assert_type/3, cyclesafe_assert_alias_canonical/2]).

:- use_module(library(assoc), [list_to_assoc/2]).
:- use_module(library(terms), [term_factorized/3]).

:- dynamic ctor_pretype_type/3. % Type definitions.
:- dynamic alias_canonical/2. % Type aliases.

cyclesafe_assert_type(Ctor, PreType, Type) :-
    term_factorization(PreType, PTF),
    assertz(ctor_pretype_type(Ctor, PTF, Type)).

get_type(Ctor, pretype_type(PreType, Type)) :-
    ctor_pretype_type(Ctor, PTF, Type),
    term_factorization(PreType, PTF).

:- det(get_types/1).
get_types(Types) :-
    $(findall(Ctor-TypeRule, get_type(Ctor, TypeRule), Types_)),
    $(list_to_assoc(Types_, Types)).

cyclesafe_assert_alias_canonical(A, C) :-
    term_factorization(C, Factorization),
    assertz(alias_canonical(A, Factorization)).

get_alias(A, C) :-
    alias_canonical(A, F),
    term_factorization(C, F).

:- det(get_aliases/1).
get_aliases(Als) :-
    $(findall(A-C, get_alias(A, C), Als_)),
    $(list_to_assoc(Als_, Als)).

current_ctor(Name, Arity, Type) :-
    ctor_pretype_type(Name, PreType, Type),
    functor(PreType, Name, Arity).

retract_ctor(Name, Arity, Type) :-
    ctor_pretype_type(Name, PreType, Type),
    $(functor(PreType, Name, Arity)),
    $(retract(ctor_pretype_type(Name, PreType, Type))),
    (ctor_pretype_type(_, _, Type)
    -> true
    ;  retractall(alias_canonical(Type, _)),
       retractall(alias_canonical(_, Type))).

retract_all_types_and_aliases :-
    % forall(current_ctor(Name, Arity, Type),
    %        retract_ctor(Name, Arity, Type)).
    retractall(ctor_pretype_type(_, _, _)),
    retractall(alias_canonical(_, _)).

term_factorization(Term, acyclic(Term_)) => Term = Term_.
term_factorization(Term, skel_subst(Skel, Subst)) =>
    Term = Skel,
    maplist(call, Subst).
term_factorization(Term, Factorization), var(Factorization) =>
    cyclic_term(Term)
    -> term_factorized(Term, Skel, Subst),
       Factorization = skel_subst(Skel, Subst)
    ;  Factorization = acyclic(Term).