:- module(util, [cata/3, catapred/2, cyclesafe_alias_canonical/3,
		 cyclesafe_type/4, dealias/3, must_be_declared_type/3,
		 must_be_undeclared_type/3]).

:- autoload(library(rbtrees), [rb_empty/1, rb_insert_new/4,
			       rb_lookup/3]).
:- autoload(library(terms), [same_functor/2, mapargs/3]).
:- autoload(library(assoc), [gen_assoc/3]).

:- meta_predicate cata(2, ?, ?).
cata(F) --> { rb_empty(Seen) }, cata_(F, Seen).

:- meta_predicate cata_(2, +, ?, ?).
cata_(_, _, A, B), var(A)  => $(A = cata_escape(B)). % Escape.
cata_(_, _, A, B), A = cata_escape(B_) => $(B = B_). % Unescape.
cata_(F, S, A, B) =>
    rb_insert_new(S, A, B, S1)
    -> $(same_functor(A, C)), % Apply constraint early.
       call(F, C, B),
       mapargs(cata_(F, S1), A, C)
    ;  $(rb_lookup(A, B, S)). % Tie the knot.

:- meta_predicate streampred(1, ?, ?).
streampred(G, X, X) :-
    $(call(G, X)).

:- meta_predicate catapred(1, ?).
catapred(G, X) :-
    $(copy_term(X, X_)),
    $(cata(streampred(G), X_, _)).

dealias(Als, A, C) :-
    copy_term(A, A_),
    cata(dealias_(Als), A_, C),
    cata(=, A_, A). % Unescape everything.

dealias_(Als) --> cyclesafe_alias_canonical(Als) *-> {} ; {}.

cyclesafe_alias_canonical(Als, A, C), var(C), nonvar(A) =>
    copy_term(Als, Als_),
    bagof(C_, gen_assoc(A, Als_, C_), [C]).

cyclesafe_type(Types, Ctor, PreType, Type), var(PreType) =>
    copy_term(Types, Types_),
    gen_assoc(Ctor, Types_, pretype_type(PreType, Type)).

must_be_declared_type(Types, Als, Type) :-
    declared_type(Types, Als, Type)
    -> true
    ;  throw(error(ill_typed(undeclared_type(Type)), _)).

must_be_undeclared_type(Types, Als, Type) :-
    declared_type(Types, Als, Type)
    -> throw(error(ill_typed(already_declared_type(Type)), _))
    ;  true.

declared_type(_, _, (_ -> _)) => true.
declared_type(Types, Als, Type), nonvar(Type) =>
    % This allows arity-overloaded types. TODO maybe should be
    % disallowed as is done for ctors.
    $(same_functor(Type, Skel)),
    (cyclesafe_type(Types, _, _, Skel)
    ; cyclesafe_alias_canonical(Als, Skel, _)).
