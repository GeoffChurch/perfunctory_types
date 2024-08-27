:- use_module("../prolog/core").

setup :-
    % Some type declarations
    $(type refl(A) ---> A = A), % This could have just been a constraint (type _ ---> A = A), but refl(A) is more readable.
    $(type _       ---> unit),
    $(type nat     ---> z ; s(nat)),
    $(type _       ---> even(nat)),
    $(type list(X) ---> [] ; [X|list(X)]),
    $(type _       ---> pair(_, _)), % This is an "arity constraint" so that pair(z) has type X -> pair(nat, X).
    $(type _       ---> call((A -> _), A)), % ctors can't be arity-overloaded, so we'd need e.g. call0, call1, etc.

    % Some type aliases
    $(StreamT = pair(X, StreamT)),
    $(type stream(X)       == StreamT), % Equirecursion via cyclic terms and type aliasing.
    $(type streamstream(X) == stream(stream(X))),
    $(type succ_alias      == (nat -> nat)),
    $(type cons_alias(X)   == (list(X) -> list(X))).

catch_error(Goal, E) :-
    catch(Goal, error(E, _), true).

:- begin_tests(basic, [setup(setup), cleanup(retract_all_types_and_aliases)]).

test(setup_cleanup) :-
    retract_all_types_and_aliases,
    setup,
    retract_all_types_and_aliases,
    setup.

test(var, [Var == \Type]) :-
    typecheck(Var, Type).

test(incomplete_list, [Type =@= list(list(_))]) :-
    typecheck([[],[]], Type).

test(complete_list, [Type == list(list(nat))]) :-
    typecheck([[],[s(s(z))]], Type).

test(heterogeneous_list, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck([[z],[[]]], _), E).

test(whole_program, [Type == (nat, (nat     :- nat ), even,      (even          :- even))]) :-
    typecheck(               (z,   (s(s(N)) :- s(N)), even(z),   (even(s(s(N))) :- even(N))), Type).

test(typecheck_fail_propagates, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck([even([])], _), E).

test(var_preservation, [error(determinism_error(vars_preserved(f(_), potato), det, fail, goal), _)]) :-
    type potato ---> f(_).

test(ctor_already_declared, [error(determinism_error(\+declared_ctor(z), det, fail, goal), _)]) :-
    type letter ---> z.

test(var_type, [Type == abcd(X,Y,Z)]) :-
    type Type ---> a(X) ; b(X,Y) ; c(Z) ; d.

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

test(too_many_args, [E =@= ill_typed(expected(s(nat)),got(s(_, _)))]) :-
    catch_error(typecheck(s(z, z), _), E).

test(arity_overloaded_type) :-
    % TODO: This is not necessarily desirable.
    % Overloading is already disallowed for term ctors so that currying always unambiguous.
    type nat(X) ---> new_nat(X).

test(type_as_term, [error(determinism_error(\+declared_type(nat), det, fail, goal), _)]) :-
    typecheck([nat], _).

test(type_as_ctor, [error(determinism_error(\+declared_type(nat), det, fail, goal), _)]) :-
    type _ ---> nat.

test(disallowed_type_functor, [error(determinism_error(allowed_functor(_->_), det, fail, goal), _)]) :-
    type arrow(A, B) ---> (A -> B).

test(disallowed_ctor_functor, [error(determinism_error(allowed_functor(_->_), det, fail, goal), _)]) :-
    type (A -> B) ---> arrow(A, B).

test(unification_success, [Type == refl(nat)]) :-
    typecheck(z = s(z), Type).

test(unification_failure, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck(z = [], _), E).

test(unification_skolem_success, [Type == refl(f)]) :-
    typecheck(f = f, Type).

test(annotated_skolem_success, [X-Y-Type =@= (\T)-(\T)-list(f(T))]) :-
    typecheck([f(X), f(Y)], Type).

test(unification_skolem_failure, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck(f(z) = f([]), _), E).

test(annotated_skolem_failure, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck([f(z), f([])], _), E).

test(ho_multi, [Type =@= (X->list(X)->list(X))]) :-
    typecheck('[|]', Type).

test(ho_curry, [Type =@= (list(list(X))->list(list(X)))]) :-
    typecheck('[|]'([]), Type).

test(call_success, [Type == call(nat, nat)]) :-
    typecheck(call(s, s(z)), Type).

test(call_failure, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck(call(s, []), _), E).

test(alias_when_requested, [ListNat == list(nat)]) :-
    typecheck(pair([z], _), stream(ListNat)).

test(no_alias_when_not_requested, [Type =@= pair(list(nat), _)]) :-
    typecheck(pair([z], _), Type).

test(failure_propagates_through_alias, [E =@= ill_typed(expected_type(list(_)),got(nat))]) :-
    catch_error(typecheck(pair([[]], _), stream(list(nat))), E).

test(nested_alias) :-
    typecheck(pair(pair(_,_),_), stream(stream(_))).

test(nested_alias_collapse) :-
    typecheck(pair(pair(_,_),_), streamstream(_)).

test(function_alias, [Nat == nat]) :-
    typecheck('[|]'(z), cons_alias(Nat)).

test(failed_alias, [E =@= ill_typed(expected_type(nat),got(Stream))]) :-
    Stream = pair(_, Stream),
    catch_error(typecheck(pair(_, z), stream(_)), E).

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

test(union_alias, [error(determinism_error(\+declared_type(alias), det, fail, goal), _)]) :-
    (type alias == nat),
    (type alias == list(nat)).

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

test(internal_skolemize_to_recursive_type1, [E == ill_typed(expected_type(G),got_type(nat))]) :-
    G = g(G),
    catch_error(typecheck((X = g(X), f(z) = f(X)), _), E).

test(internal_skolemize_to_recursive_type2, [E == ill_typed(expected_type(nat),got(G))]) :-
    G = g(G),
    catch_error(typecheck((X = g(X), f(X) = f(z)), _), E).

test(internal_skolemize_to_recursive_type3, [E =@= ill_typed(expected_type(nat),got_untyped_term(g(_)))]) :-
    catch_error(typecheck((f(z) = f(X), X = g(X)), _), E).

test(internal_skolemize_to_recursive_type4, [E =@= ill_typed(expected_type(nat),got_untyped_term(g(_)))]) :-
    catch_error(typecheck((f(X) = f(z), X = g(X)), _), E).

test(internal_recursive_term_type_deduced, [Type==(refl(list(unit)),refl(f(list(unit))))]) :-
    typecheck((X = [_|X], f([unit]) = f(X)), Type).

test(external_skolemize_to_recursive_type_fail_first, [E =@= ill_typed(expected_type(nat),got_untyped_term(g(_)))]) :-
    X = g(X),
    catch_error(typecheck((f(z) = f(X), X), _), E).

test(external_skolemize_to_recursive_type_fail_second, [E =@= ill_typed(expected_type(nat),got_untyped_term(g(_)))]) :- % This requires cycle safety.
    X = g(X),
    catch_error(typecheck((X, f(z) = f(X)), _), E).

test(recursive_type_terminates) :-
    Stream = pair(_, Stream),
    typecheck(_, Stream).

:- end_tests(basic).

:- begin_tests(cata, [setup(specialized_cata_setup), cleanup(retract_all_types_and_aliases)]).

specialized_cata_setup :-
    (type natF(A) ---> z ; s(A)),
    NatT = natF(NatT),
    (type nat == NatT),
    (type arity ---> even ; odd),
    (type _ ---> nat_arity(natF(arity), arity)),
    (type _ ---> fmapNat((A -> B -> _), natF(A), natF(B))),
    (type _ ---> cataNat((natF(A) -> A -> _), nat, A)).

test(nat_arity, [Type == (nat_arity, nat_arity, nat_arity)]) :-
    typecheck((nat_arity(z, even),
	       nat_arity(s(even), odd),
	       nat_arity(s(odd), even)), Type).

test(fmapNat, [Type =@= (fmapNat(_,_,_),fmapNat(Q,R,S):-call((Q->R->S),Q,R))]) :-
    typecheck((fmapNat(_, z, z),
	       fmapNat(F, s(X), s(Y)) :- call(F, X, Y)), Type).

test(cataNat_unaliased, [Type =@= (cataNat(CoD,AlgT):-fmapNat(Nat,CoD,cataNat(CoD,AlgT)),call((natF(CoD)->CoD->AlgT),natF(CoD),CoD))]) :-
    Nat = natF(Nat),
    typecheck((cataNat(Alg, A, B) :- fmapNat(cataNat(Alg), A, B0), call(Alg, B0, B)), Type).

test(cataNat_aliased, [Type =@= (cataNat(CoD,AlgT):-fmapNat(nat,CoD,cataNat(CoD,AlgT)),call((natF(CoD)->CoD->AlgT),natF(CoD),CoD))]) :-
    Type = (_:-fmapNat(nat,_,_),_), % Force natF(natF(...)) to be aliased to nat.
    typecheck((cataNat(Alg, A, B) :- fmapNat(cataNat(Alg), A, B0), call(Alg, B0, B)), Type).

:- end_tests(cata).
