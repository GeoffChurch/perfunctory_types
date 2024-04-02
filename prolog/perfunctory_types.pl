% Copyright (C) Geoffrey Churchill 2023-2024
%
% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.
%
% This program is distributed in the hope that it will be useful, but
% WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
% General Public License for more details.
%
% You should have received a copy of the GNU General Public License
% along with this program. If not, see
% <https://www.gnu.org/licenses/>. 

:- module(perfunctory_types, [
	      op(1150,  fx, type),
	      op(1130, xfx, --->),
	      op(1130,  fx, --->),
	      (type)/1,
	      typecheck/2,
	      retract_all_types/0
	  ]).

:- dynamic ctor_pretype_type/3. % Type definitions, e.g. ctor_pretype_type(s, s(nat), nat).
:- dynamic alias_canonical/2. % Type aliases, e.g. alias_canonical(intlist, list(int)).

:- det((type)/1).

% Declare a new type. `PreTypes` should be a semicolon-delimited list of terms whose arguments are types.
type Type ---> PreTypes =>
    $(nonvar(Type)),
    $(nonvar(PreTypes)), % This ensures semicolon_list is det.
    $(allowed_functor(Type)),
    $(\+ declared_type(Type)), % Guardrail: single-definition.
    $(\+ declared_ctor(Type)), % Guardrail: types can't be ctors of other types.
    $(vars_preserved(PreTypes, Type)),
    $(semicolon_list(PreTypes, PreTypeList)),
    $(normalize(Type, NT)),
    maplist(assert_type(NT), PreTypeList).

% If the derived type is omitted it will default to be the same as the ctor. This can be done in order to constrain a ctor's arity or argument types without needing to come up with a name for the derived type.
type ---> PreType => type PreType ---> PreType.

% Declare `A` as an alias of `B`.
type A == B =>
    $(nonvar(A)),
    $(nonvar(B)),
    $(allowed_functor(A)),
    $(\+ declared_type(A)),
    $(\+ declared_ctor(A)),
    $(vars_preserved(B, A)), % This allows phantom types
    $(normalize(B, C)),
    $(assert_possibly_cyclic_alias_canonical(A, C)).

normalize(A, C) :- cata(normalize_, A, C).
normalize_(A, C), A =@= (_ -> _) => C = A.
normalize_(A, C) => get_possibly_cyclic_alias_canonical(A, C) *-> true ; C = A.

cata(F, A, B) :-
    copy_term(A, A_),
    rb_empty(Seen),
    cata_(F, Seen, A_, B),
    unescape(A_, A).
cata_(_, _,    A,  B), var(A) => A = please_evaluate_me_to(B).
cata_(_, _,   please_evaluate_me_to(B_), B) => B = B_.
cata_(F, Seen, A,  B) =>
    rb_insert_new(Seen, A, B, Seen1)
    -> same_functor(A, C), % Apply constraint early
       call(F, C, B),
       mapargs(cata_(F, Seen1), A, C)
    ;  rb_lookup(A, B, Seen). % Tie the knot

unescape(A, B) :-
    rb_empty(Seen),
    cata_(=, Seen, A, B).

assert_type(Type, PreType) :-
    $(allowed_functor(PreType)),
    $(\+ declared_ctor(PreType)), % If a ctor could appear in distinct type declarations it would require linear space and exponential time to find the right type.
    $(mapargs(normalize, PreType, NPT)), % Normalize arguments. This could just be normalize(PreType, NPT).
    $(functor(NPT, Ctor, _)),
    $(assert_possibly_cyclic_type(Ctor, NPT, Type)). % As of SWI 9.0.4, cyclic terms cannot be directly asserted.

% See https://www.cs.cmu.edu/~fp/courses/lp/lectures/10-poly.pdf (type preservation).
vars_preserved(PreType, Type) :-
    term_vars_ord(PreType, PTVs),
    term_vars_ord(Type, TVs),
    ord_subset(PTVs, TVs).

term_vars_ord --> term_variables, list_to_ord_set.

allowed_functor(Term), nonvar(Term) =>
    Term \= (_ -> _), % (->)/2 is reserved for function types.
    Term \= please_evaluate_me_to(_). % (\)/1 is reserved for cata escapes.

declared_type(Type) :-
    $(same_functor(Type, Skel)), % This allows arity-overloaded types. TODO Maybe should be disallowed as is done for ctors.
    (get_possibly_cyclic_type(_, _, Skel) ; alias_canonical(Skel, _)), !.

declared_ctor(PreType) :-
    $(functor(PreType, Ctor, _)),
    ctor_pretype_type(Ctor, _, _).

assert_possibly_cyclic_type(Ctor, PreType, Type) :-
    term_factorization(PreType, PTF),
    term_factorization(Type, TF),
    assertz(ctor_pretype_type(Ctor, PTF, TF)).

get_possibly_cyclic_type(Ctor, PreType, Type) :-
    ctor_pretype_type(Ctor, PTF, TF),
    term_factorization(PreType, PTF),
    term_factorization(Type, TF).

assert_possibly_cyclic_alias_canonical(A, C) :-
    term_factorization(C, Factorization),
    assertz(alias_canonical(A, Factorization)).

get_possibly_cyclic_alias_canonical(A, C) :-
    alias_canonical(A, Factorization),
    term_factorization(C, Factorization).

retract_all_types :-
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

typecheck(Term, Type) :-
    $(copy_term(Term, Term_)),
    $(normalize(Type, CanonicalType)),
    cata(typecheck_, Term_, CanonicalType).
typecheck_(PreType, Type) =>
    % Try to look up the "full" type (if PreType is a function type then Type is too).
    functor(PreType, Ctor, _),
    get_possibly_cyclic_type(Ctor, FullPreType, FullType)
    *-> % Resolve Type to FullType, possibly prefixed with arrows if missing arguments.
	matchargs(PreType, Type, FullPreType, FullType)
    ;   % Otherwise, do an ad-hoc type declaration/skolemization.
	% This is similar to having declared
	% `same_functor(PreType, Skel), (type Skel ---> Skel)` ahead of time, so that
	% PreType is polymorphic in all arguments and has a unique type (the difference
        % is that the declaration would constrain the arity). In other words,
	% the ambient algebra is left free except where it has been explicitly
	% coalesced by declaring types with multiple ctors.
        $(\+ declared_type(PreType)), % Block skolemization when the term is a type, so that we can't inject into a type with the same functor as PreType.
	Type = PreType. % Skolemize.

matchargs(PartTerm, PartType, FullTerm, FullType) :-
    $(PartTerm =.. [F|PartArgs]),
    $(FullTerm =.. [F|FullArgs]),
    append(PartArgs, RestArgs, FullArgs), % If RestArgs = [] then PartType = FullType.
    % PartType should be a chain of arrows through each of RestArgs before ending at FullType
    arrow_list(PartType, RestArgs, FullType).

arrow_list(FullType, [], FullType).
arrow_list(X->Arrows, [X|List], RestArrows) :- arrow_list(Arrows, List, RestArrows).
