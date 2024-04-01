:- use_module("../prolog/perfunctory_types").

setup :-
    % Some type declarations
    $(type refl(A) ---> A = A), % This could have just been a constraint (type ---> A = A), but refl(A) is more readable.
    $(type nat     ---> z ; s(nat)),
    $(type         ---> even(nat)),
    $(type color   ---> red ; green ; blue),
    $(type list(X) ---> [] ; [X|list(X)]),
    $(type         ---> pair(_, _)), % This is an "arity constraint" so that pair(z) has type X -> pair(nat, X).
    $(type         ---> call((A -> _), A)), % ctors can't be arity-overloaded, so we'd need e.g. call0, call1, etc.

    % Some type aliases
    $(StreamT = pair(X, StreamT)),
    $(type stream(X)       == StreamT), % Equirecursion via cyclic terms and type aliasing.
    $(type streamstream(X) == stream(stream(X))),
    $(type succ_alias      == (nat -> nat)),
    $(type cons_alias(X)   == (list(X) -> list(X))).

:- begin_tests(perfunctory_types, [setup(setup), cleanup(retract_all_types)]).

test(setup_cleanup) :-
    retract_all_types,
    setup,
    retract_all_types,
    setup.

test(var, [Var-Type =@= _-_]) :-
    typecheck(Var, Type).

test(incomplete_list, [Type =@= list(list(_))]) :-
    typecheck([[],[]], Type).

test(complete_list, [Type == list(list(nat))]) :-
    typecheck([[],[s(s(z))]], Type).

test(heterogeneous_list, [fail]) :-
    typecheck([[z],[red]], _).

test(whole_program, [Type == (nat, (nat     :- nat ), even(nat), (even(nat)     :- even(nat)))]) :-
    typecheck(               (z,   (s(s(N)) :- s(N)), even(z),   (even(s(s(N))) :- even(N))), Type).

test(typecheck_fail_propagates, [fail]) :-
    typecheck([even(red)], _).

test(var_preservation, [error(determinism_error(vars_preserved(f(_), potato), det, fail, goal), _)]) :-
    type potato ---> f(_).

test(ctor_already_declared, [error(determinism_error(\+declared_ctor(z), det, fail, goal), _)]) :-
    type letter ---> z.

test(var_type, [error(determinism_error(nonvar(_), det, fail, goal), _)]) :-
    type _ ---> potato.

test(var_ctor, [error(determinism_error(nonvar(_), det, fail, goal), _)]) :-
    (type potato ---> _).

test(alias_unpreserved_var, [error(determinism_error(vars_preserved(_,_), det, fail, goal), _)]) :-
    type st(X) ---> thread_ret(_Thread, X).

test(var_alias_lhs, [error(determinism_error(nonvar(_), det, fail, goal), _)]) :-
    type _ == nat.

test(var_alias_rhs, [error(determinism_error(nonvar(_), det, fail, goal), _)]) :-
    type nat == _.

test(var_alias_both, [error(determinism_error(nonvar(_), det, fail, goal), _)]) :-
    type X == X.

test(arity_overloaded_type) :-
    % TODO: This is not necessarily desirable.
    % Overloading is already disallowed for term ctors so that currying always unambiguous.
    type nat(X) ---> new_nat(X).

test(type_as_term, [error(determinism_error(\+declared_type(nat), det, fail, goal), _)]) :-
    typecheck([nat], _).

test(type_as_ctor, [error(determinism_error(\+declared_type(nat), det, fail, goal), _)]) :-
    type ---> nat.

test(disallowed_type_functor, [error(determinism_error(allowed_functor(_->_), det, fail, goal), _)]) :-
    type arrow(A, B) ---> (A -> B).

test(disallowed_ctor_functor, [error(determinism_error(allowed_functor(_->_), det, fail, goal), _)]) :-
    type (A -> B) ---> arrow(A, B).

test(unification_success, [Type == refl(nat)]) :-
    typecheck(z = s(z), Type).

test(unification_failure, [fail]) :-
    typecheck(z = red, _).

test(unification_skolem_success, [Type == refl(f)]) :-
    typecheck(f = f, Type).

test(annotated_skolem_success, [X-Y-Type =@= _-_-list(f(_))]) :-
    typecheck([f(X), f(Y)], Type).

test(unification_skolem_failure, [fail]) :-
    typecheck(f(z) = f(red), _).

test(annotated_skolem_failure, [fail]) :-
    typecheck([f(z), f(red)], _).

test(ho_multi, [Type =@= (X->list(X)->list(X))]) :-
    typecheck('[|]', Type).

test(ho_curry, [Type =@= (list(list(X))->list(list(X)))]) :-
    typecheck('[|]'([]), Type).

test(call) :-
    typecheck(call(s, s(z)), Type),
    Type == call((nat -> nat), nat),
    \+ typecheck(call(s, red), _).

test(alias_when_requested, [ListNat == list(nat)]) :-
    typecheck(pair([z], _), stream(ListNat)).

test(no_alias_when_not_requested, [Type =@= pair(list(nat), _)]) :-
    typecheck(pair([z], _), Type).

test(failure_propagates_through_alias, [fail]) :- % red is a color, not a nat
    typecheck(pair([red], _), stream(list(nat))).

test(nested_alias) :-
    typecheck(pair(pair(_,_),_), stream(stream(_))).

test(nested_alias_collapse) :-
    typecheck(pair(pair(_,_),_), streamstream(_)).

test(function_alias, [Nat == nat]) :-
    typecheck('[|]'(z), cons_alias(Nat)).

test(failed_alias, [fail]) :- % z is a nat, not a stream.
    typecheck(pair(_, z), stream(_)).

test(argument_of_alias_inferred, [Nat == nat]) :-
    typecheck(pair(z, _), stream(Nat)).

test(pure_recursive_type, [Type == prec]) :-
    (type prec ---> prec(prec)),
    Prec = prec(Prec),
    typecheck(Prec, Type).

test(mutually_recursive_types, [Type == mutrecA]) :-
    (type mutrecA ---> mutrecA(mutrecB)),
    (type mutrecB ---> mutrecB(mutrecA)),
    RecTerm = mutrecA(mutrecB(RecTerm)),
    typecheck(RecTerm, Type).

test(empty_alias) :-
    % TODO: This is not necessarily desirable.
    (type empty == empty),
    (type also_empty == empty),
    (type abcdefg == hijklmnop),
    typecheck(_, empty).

test(union_alias, [error(determinism_error(\+declared_type(nat_or_color), det, fail, goal), _)]) :-
    (type nat_or_color == nat),
    (type nat_or_color == color).

test(rectype_curry_nat_neither, [Type =@= (X -> pair(nat, X))]) :-
    typecheck(pair(z), Type).

test(rectype_curry_var_neither, [Type =@= (X -> pair(_, X))]) :-
    typecheck(pair(_), Type).

test(rectype_curry_nat_lhs, [Type == (stream(X) -> pair(nat, Stream))]) :-
    Type = (stream(X) -> _),
    typecheck(pair(z), Type),
    Stream = pair(X, Stream).

test(rectype_curry_var_lhs, [Type =@= (stream(X) -> pair(_, Stream))]) :-
    Type = (stream(X) -> _),
    typecheck(pair(_), Type),
    Stream = pair(X, Stream).

test(rectype_curry_nat_rhs) :-
    Type = (StreamNat -> stream(Nat)),
    typecheck(pair(z), Type),
    Nat == nat,
    StreamNat == pair(nat, StreamNat).

test(rectype_curry_var_rhs) :-
    Type = (StreamT -> stream(X)),
    typecheck(pair(_), Type),
    StreamT == pair(X, StreamT).

test(rectype_curry_nat_both, [Type == (stream(nat) -> stream(nat))]) :-
    Type = (stream(_) -> stream(_)),
    typecheck(pair(z), Type).

test(rectype_curry_var_both, [Type =@= (stream(X) -> stream(X))]) :-
    Type = (stream(_) -> stream(_)),
    typecheck(pair(_), Type).

test(internal_skolemize_to_recursive_type) :-
    \+ typecheck((X = g(X), f(red) = f(X)), _),
    \+ typecheck((X = g(X), f(X) = f(red)), _),
    \+ typecheck((f(red) = f(X), X = g(X)), _),
    \+ typecheck((f(X) = f(red), X = g(X)), _).

test(internal_recursive_term_type_deduced, [Type==(refl(list(color)),refl(f(list(color))))]) :-
    typecheck((X = [_|X], f([red]) = f(X)), Type).

test(external_skolemize_to_recursive_type_fail_first) :-
    X = g(X),
    \+ typecheck((f(red) = f(X), X), _).

test(external_skolemize_to_recursive_type_fail_second) :- % This requires cycle safety.
    X = g(X),
    \+ typecheck((X, f(red) = f(X)), _).

test(recursive_type_terminates) :-
    Stream = pair(_, Stream),
    typecheck(_, Stream).

:- end_tests(perfunctory_types).

:- begin_tests(examples, [setup(specialized_cata_setup)
			  , cleanup(retract_all_types)
			 ]).

specialized_cata_setup :-
    (type natF(A) ---> z ; s(A)),
    NatT = natF(NatT),
    (type nat == NatT),
    (type arity ---> even ; odd),
    (type ---> nat_arity(natF(arity), arity)),
    (type ---> fmapNat((A -> B -> _), natF(A), natF(B))),
    (type ---> cataNat((natF(A) -> A -> _), nat, A)).

test(nat_arity, [Type == (nat_arity(natF(arity), arity), nat_arity(natF(arity), arity), nat_arity(natF(arity), arity))]) :-
    typecheck((nat_arity(z, even),
	       nat_arity(s(even), odd),
	       nat_arity(s(odd), even)), Type).

test(fmapNat, [Type =@= (fmapNat((A->B->_),natF(A),natF(B)),fmapNat((X->Y->Z),natF(X),natF(Y)):-call((X->Y->Z),X,Y))]) :-
    typecheck((fmapNat(_, z, z),
	       fmapNat(F, s(X), s(Y)) :- call(F, X, Y)), Type).

test(cataNat_unaliased, [Type =@= (cataNat((natF(CoD)->CoD->AlgT),Nat,CoD):-fmapNat((Nat->CoD->cataNat((natF(CoD)->CoD->AlgT),Nat,CoD)),natF(Nat),natF(CoD)),call((natF(CoD)->CoD->AlgT),natF(CoD),CoD))]) :-
    Nat = natF(Nat),
    typecheck((cataNat(Alg, A, B) :- fmapNat(cataNat(Alg), A, B0), call(Alg, B0, B)), Type).

test(cataNat_aliased, [Type =@= (cataNat((natF(CoD)->CoD->AlgT),nat,CoD):-fmapNat((nat->CoD->cataNat((natF(CoD)->CoD->AlgT),nat,CoD)),nat,natF(CoD)),call((natF(CoD)->CoD->AlgT),natF(CoD),CoD))]) :-
    Type = (cataNat(_,nat,_):-fmapNat((nat->_->cataNat(_,nat,_)),nat,_),call(_,_,_)),
    typecheck((cataNat(Alg, A, B) :- fmapNat(cataNat(Alg), A, B0), call(Alg, B0, B)), Type).

:- end_tests(examples).

:- run_tests.

