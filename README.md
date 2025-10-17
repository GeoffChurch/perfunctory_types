# `perfunctory_types`

`perfunctory_types` is a static type system for SWI-Prolog.

There might be bugs. Feedback is welcome!

See [the tests](t/) for lots of examples.

## Overview

There is a syntactic and a semantic side to the type system. The semantic side builds on top of the syntactic side.

### Syntactic checking

The basic idea is that type declarations _constrain_ and _coalesce_ the ambient "term algebra" (the Herbrand algebra) into a "type algebra".

The algebra is _constrained_ into a subalgebra by constraining the types of a constructor's arguments.

The algebra is _coalesced_ into a quotient algebra by declaring types with multiple constructors.

Syntactic typechecking amounts to checking that a term is a member of the algebra induced by the type declarations.

### Semantic checking

Prolog's semantics are handled by inferring a type for each untyped predicate, and checking that each usage of the predicate conforms to the inferred type. If all predicates already have syntactic type declarations, then syntactic checking already suffices and there is no need for explicit semantic checking. Inference is implemented by unifying the types of the heads of all clauses for a given predicate, where each clause is syntactically typechecked in isolation. Checking is implemented by constraining each usage to be subsumed by the inferred type, using library(subsumes) for pure/relational subsumption. 

For example, the following is ill-typed because `color` and `list(_)` cannot be unified:
```prolog
:- use_module(library(perfunctory_types)).

:- type color ---> red ; green ; blue.
:- type list(X) ---> [] ; [X|list(X)].

p(red).
p([]).
```

## Key features

### Skolemization

The algebra is left free except where explicitly coalesced/constrained by type declarations.

```prolog
?- typecheck(f(x), Type).
Type = f(x). % x/0 and f/1 are "skolemized" so that type(x) = x and type(f(A)) = f(A).
```

### Parametric polymorphism

```prolog
?- type list(X) ---> [] ; [X|list(X)].
true.

?- typecheck([[]], Type).
Type = list(list(_)).
```

### Function types

```prolog
?- typecheck('[|]', Type).
Type = (_A->list(_A)->list(_A)).
```

### Equirecursive fixpoints

```prolog
?- type natF(X) ---> z ; s(X).
true.

?- NatT = natF(NatT), (type nat == NatT). % Declare `nat` as an alias for `natF(natF(...))`.
NatT = natF(NatT).

?- typecheck(s(z), Type). % Types are not aliased by default.
Type = natF(natF(_)).

?- typecheck(s(z), nat). % Only upon request.
true.
```

### Cycle safety

```prolog
?- Omega = s(Omega), typecheck(Omega, Type).
Omega = s(Omega),
Type = natF(Type).

?- Omega = s(Omega), typecheck(Omega, nat).
Omega = s(Omega).
```

### Type preservation

Unification forces us to preserve polymorphic arguments (see Frank Pfenning's [lecture on polymorphism in LP](https://www.cs.cmu.edu/~fp/courses/lp/lectures/10-poly.pdf)).

```prolog
?- type natvector ---> natxyz(nat, nat, nat). % This is okay.
true.

?- type vector ---> xyz(A, A, A). % This is not okay - polymorphic `A` is not preserved.
ERROR: Goal vars_preserved(xyz(_13642,_13642,_13642),vector) failed

?- type vector(A) ---> xyz(A, A, A). % This is okay - polymorphic `A` is preserved.
true.
```

### No higher-rank types

This is an implementation-friendly consequence of type preservation. So (anyway questionable) entities like [`ST`](https://wiki.haskell.org/Monad/ST) are prohibited.

### Syntax is similar to that of the very different [`type_check`](https://www.swi-prolog.org/pack/list?p=type_check) pack.

---

## TODOs

### Higher-kinded types

There don't appear to be any technical blockers. Hopefully the [`hilog`](https://us.swi-prolog.org/pack/list?p=hilog) pack can do the heavy-lifting.

### Tooling integration aka red squigglies

Some options are:

[`style_check/1`](https://www.swi-prolog.org/pldoc/man?predicate=style_check/1)

[`lsp_server`](https://www.swi-prolog.org/pack/list?p=lsp_server)

[`prolog_lsp`](https://www.swi-prolog.org/pack/list?p=prolog_lsp)

## Installation in SWI-Prolog

```prolog
?- pack_install(perfunctory_types).
```

## Testing

```shell
for file in t/*.plt; do swipl -g "consult('$file'), run_tests" -t halt; done
```

---

(Note to self) To publish a new version:
1. update `pack.pl`
2. do GitHub release with new tag matching the pack.pl version
3. execute:
```prolog
?- make_directory(potato), pack_install(perfunctory_types, [url('http://github.com/GeoffChurch/perfunctory_types/archive/13.17.zip'), package_directory(potato)]).
```
