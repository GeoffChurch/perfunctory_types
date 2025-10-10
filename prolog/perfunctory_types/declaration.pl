:- module(perfunctory_types, [
	      op(1150,  fx, type),
	      op(1130, xfx, --->),
	      (type)/1,
	      typecheck/2,
	      current_ctor/3,
	      retract_ctor/3,
	      retract_all_types_and_aliases/0
	  ]).

:- use_module(library(perfunctory_types/check)).
:- use_module(library(perfunctory_types/util)).

:- use_module(library(apply), [maplist/4, foldl/4, maplist/2]).
:- use_module(library(assoc), [get_assoc/3, list_to_assoc/2]).
:- use_module(library(lists), [reverse/2]).
:- use_module(library(ordsets), [ord_subset/2, list_to_ord_set/2]).
:- use_module(library(prolog_code), [semicolon_list/2]).
:- use_module(library(terms), [mapargs/3, term_factorized/3]).

:- dynamic ctor_pretype_type/3. % Type definitions.
:- dynamic alias_canonical/2. % Type aliases.

% Declare a new type. `PreTypes` should be a semicolon-delimited list
% of terms whose arguments are types. If `Type` is var it will be
% unified with a default type whose functor is the concatenation of
% the functors of `PreTypes` and whose parameters are their variables.
type Type ---> PreTypes =>
    $(nonvar(PreTypes)), % This ensures semicolon_list is det.
    $(semicolon_list(PreTypes, PreTypeListR)),
    $(reverse(PreTypeListR, PreTypeList)),
    (var(Type)
     -> $(maplist(functor, PreTypeList, Functors, _Arities)),
	$(foldl(atom_concat, Functors, '', TypeName)),
	$(term_variables(PreTypes, Vars)),
	$(Type =.. [TypeName|Vars])
    ;   $(Type =.. [_TypeName|Subterms]),
	$(maplist(var, Subterms)),
        $(vars_preserved(PreTypes, Type))),
    $(allowed_functor(Type)),
    $(get_types(Types)),
    $(get_aliases(Als)),
    % Guardrail: single-definition.
    $(must_be_undeclared_type(Types, Als, Type)),
    % Guardrail: not ctor of other type.
    $(must_be_undeclared_ctor(Types, Type)),
    $(maplist(assert_type(Types, Als, Type), PreTypeList)).

% Declare `A` as an alias of `B`.
type A == B =>
    $(nonvar(A)),
    $(nonvar(B)),
    $(allowed_functor(A)),
    $(get_types(Types)),
    $(get_aliases(Als)),
    $(must_be_undeclared_type(Types, Als, A)),
    $(catapred(must_be_declared_type(Types, Als), B)),
    $(must_be_undeclared_ctor(Types, A)),
    % In order to allow phantom types, just require subset rather than
    % full equality.
    $(vars_preserved(B, A)),
    $(dealias(Als, B, C)), % Path compression.
    $(cyclesafe_assert_alias_canonical(A, C)).

typecheck(Term, Type) :-
    $(get_types(Types)),
    $(get_aliases(Aliases)),
    $(check:typecheck(Types, Aliases, Term, Type)).

assert_type(Types, Als, Type, PreType) :-
    $(allowed_functor(PreType)),
    % If a ctor could appear in distinct type declarations it would
    % require linear space and exponential time to find the right
    % type.
    $(must_be_undeclared_ctor(Types, PreType)),
    % Normalize arguments. This could just be dealias(PreType, NPT).
    $(mapargs(dealias(Als), PreType, NPT)),
    $(functor(NPT, Ctor, _)),
    % As of SWI 9.2.6, cyclic terms cannot be directly asserted.
    $(cyclesafe_assert_type(Ctor, NPT, Type)).

% See https://www.cs.cmu.edu/~fp/courses/lp/lectures/10-poly.pdf (type
% preservation).
vars_preserved(A, B) :-
    term_vars_ord(A, AVs),
    term_vars_ord(B, BVs),
    ord_subset(AVs, BVs)
    *-> true
    ;   throw(error(ill_typed(vars_not_preserved(A, B)), _)).

term_vars_ord --> term_variables, list_to_ord_set.

allowed_functor(Term), nonvar(Term) =>
    Term \= (_ ; _), % Reserved for sum types.
    Term \= (_ -> _), % Reserved for function types.
    Term \= cata_escape(_) % Reserved for cata escapes.
    -> true
    ;  throw(error(ill_typed(illegal_functor(Term)), _)).

must_be_undeclared_ctor(Types, PreType), nonvar(PreType) =>
    $(functor(PreType, Ctor, _)),
    $(copy_term(Types, Types_)),
    get_assoc(Ctor, Types_, _)
    -> throw(error(ill_typed(already_declared_ctor(PreType)), _))
    ;  true.

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
