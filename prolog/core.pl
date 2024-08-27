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
	      (type)/1,
	      typecheck/2,
	      current_ctor/3,
	      retract_ctor/3,
	      retract_all_types_and_aliases/0
	  ]).

:- autoload(library(apply), [maplist/2, maplist/4, foldl/4]).
:- autoload(library(lists), [reverse/2, append/3]).
:- autoload(library(ordsets), [ord_subset/2, list_to_ord_set/2]).
:- autoload(library(prolog_code), [semicolon_list/2]).
:- autoload(library(rbtrees), [rb_empty/1, rb_insert_new/4,
			       rb_lookup/3]).
:- autoload(library(terms), [same_functor/2, mapargs/3,
			     term_factorized/3]).

:- dynamic ctor_pretype_type/3. % Type definitions.
:- dynamic alias_canonical/2. % Type aliases.

:- det((type)/1).

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
	foldl(atom_concat, Functors, '', TypeName),
	term_variables(PreTypes, Vars),
	Type =.. [TypeName|Vars]
    ;   Type =.. [_TypeName|Subterms],
	$(maplist(var, Subterms)),
        $(vars_preserved(PreTypes, Type))),
    $(allowed_functor(Type)),
    $(\+ declared_type(Type)), % Guardrail: single-definition.
    $(\+ declared_ctor(Type)), % Guardrail: not ctor of other type.
    maplist(assert_type(Type), PreTypeList).

% Declare `A` as an alias of `B`.
type A == B =>
    $(nonvar(A)),
    $(nonvar(B)),
    $(allowed_functor(A)),
    $(\+ declared_type(A)),
    $(\+ declared_ctor(A)),
    % In order to allow phantom types, just require subset rather than
    % full equality.
    $(vars_preserved(B, A)),
    $(dealias(B, C)),
    $(cyclesafe_assert_alias_canonical(A, C)).


:- meta_predicate cata(2, ?, ?).
cata(F) --> { rb_empty(Seen) }, cata_(F, Seen).

:- meta_predicate cata_(2, +, ?, ?).
cata_(_, _, A, B), var(A)  => $(A = \B). % Escape.
cata_(_, _, A, B), A = \B_ => $(B = B_). % Unescape.
cata_(F, S, A, B) =>
    rb_insert_new(S, A, B, S1)
    -> $(same_functor(A, C)), % Apply constraint early.
       call(F, C, B),
       mapargs(cata_(F, S1), A, C)
    ;  $(rb_lookup(A, B, S)). % Tie the knot.

dealias(A, C) :-
    copy_term(A, A_),
    cata(dealias_, A_, C),
    cata(=, A_, A). % Unescape everything.

dealias_ --> cyclesafe_alias_canonical *-> {} ; {}.

assert_type(Type, PreType) :-
    $(allowed_functor(PreType)),
    % If a ctor could appear in distinct type declarations it would
    % require linear space and exponential time to find the right
    % type.
    $(\+ declared_ctor(PreType)),
    % Normalize arguments. This could just be dealias(PreType, NPT).
    $(mapargs(dealias, PreType, NPT)),
    $(functor(NPT, Ctor, _)),
    % As of SWI 9.2.6, cyclic terms cannot be directly asserted.
    $(cyclesafe_assert_type(Ctor, NPT, Type)).

% See https://www.cs.cmu.edu/~fp/courses/lp/lectures/10-poly.pdf (type
% preservation).
vars_preserved(PreType, Type) :-
    term_vars_ord(PreType, PTVs),
    term_vars_ord(Type, TVs),
    ord_subset(PTVs, TVs).

term_vars_ord --> term_variables, list_to_ord_set.

allowed_functor(Term), nonvar(Term) =>
    Term \= (_ ; _), % Reserved for sum types.
    Term \= (_ -> _), % Reserved for function types.
    Term \= (\_). % Reserved for cata escapes.

declared_type(Type) :-
    % This allows arity-overloaded types. TODO maybe should be
    % disallowed as is done for ctors.
    $(same_functor(Type, Skel)),
    (cyclesafe_type(_, _, Skel) ; alias_canonical(Skel, _)),
    !.

declared_ctor(PreType) :-
    $(functor(PreType, Ctor, _)),
    ctor_pretype_type(Ctor, _, _).

cyclesafe_assert_type(Ctor, PreType, Type) :-
    term_factorization(PreType, PTF),
    assertz(ctor_pretype_type(Ctor, PTF, Type)).

cyclesafe_type(Ctor, PreType, Type) :-
    ctor_pretype_type(Ctor, PTF, Type),
    term_factorization(PreType, PTF).

cyclesafe_assert_alias_canonical(A, C) :-
    term_factorization(C, Factorization),
    assertz(alias_canonical(A, Factorization)).

cyclesafe_alias_canonical(A, C) :-
    alias_canonical(A, Factorization),
    term_factorization(C, Factorization).

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

:- det(typecheck/2).

typecheck(Term, Type) :-
    $(dealias(Type, CanonicalType)),
    catch(cata(typecheck_, Term, CanonicalType),
	  error(determinism_error(PT=T,det,fail,goal), Ctx),
	  throw(error(ill_typed(
			  expected_type(T),
			  got_type(PT)
		      ), Ctx))).

typecheck_(PreType, Type) =>
    % Try to look up the "full" type (if PreType is a function type
    % then Type is too).
    functor(PreType, Ctor, _),
    cyclesafe_type(Ctor, FullPreType, FullType)
    *-> % Resolve Type to FullType, possibly prefixed with arrows if
	% missing arguments.
	$(matchargs(PreType, Type, FullPreType, FullType))
    ;   % Otherwise, do an ad-hoc type declaration/skolemization.
	% This is similar to having declared `same_functor(PreType,
	% Skel), (type Skel ---> Skel)` ahead of time, so that PreType
	% is polymorphic in all arguments and has a unique type (the
	% difference is that an explicit declaration would constrain
	% the arity). In other words, the ambient algebra is left free
	% except where it has been explicitly coalesced by declaring
	% types with multiple ctors.

        % Block skolemization when the term is a type, so that we
        % can't inject into a type with the same functor as PreType.
        $(\+ declared_type(PreType)),
	(Type = PreType % Skolemize.
	-> true
	;  throw(error(
		     ill_typed(
			 expected_type(Type),
			 got_untyped_term(PreType)), _))).

matchargs(PartTerm, PartType, FullTerm, FullType) :-
    $(PartTerm =.. [F|PartArgs]),
    $(FullTerm =.. [F|FullArgs]),
    % If RestArgs = [] then PartType = FullType.
    (append(PartArgs, RestArgs, FullArgs)
    *-> true
    ;  throw(error(ill_typed(
		       expected(FullTerm),
		       got(PartTerm)), _))),
    % PartType should be a chain of arrows through each of RestArgs
    % before ending at FullType.
    (arrow_list(PartType, RestArgs, FullType)
    *-> true
    ;   throw(error(ill_typed(
			expected_type(FullType),
			got(PartType)), _))).

arrow_list(FullType, [], FullType).
arrow_list(X->Arrows, [X|List], RestArrows) :-
    arrow_list(Arrows, List, RestArrows).
