# `perfunctory_types`

`perfunctory_types` is a static type system for SWI-Prolog.

It might be bugged or at least irreparably flawed. Feedback is very welcome!

See [the tests](t/) for lots of examples.

## Overview

The basic idea is that type declarations constrain and coalesce the ambient "term algebra" into a "type algebra".

The algebra is constrained into a subalgebra by constraining the types of a constructor's arguments.

The algebra is coalesced into a quotient algebra by declaring types with multiple constructors.

Typechecking amounts to checking that a term is a member of the algebra induced by the type constraints.


## Salient aspects

### Gradual typing

The algebra is left free except where explicitly coalesced/constrained by type declarations.

```prolog
?- typecheck(f(x), Type).
Type = f(x).
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

### No distinction between predicates and other terms

Typechecking is applied to terms, which may be entire programs. Types are "per-functor-y".

### Syntax is similar to that of the very different [`type_check`](https://www.swi-prolog.org/pack/list?p=type_check) pack.

---

## TODOs

### Semantic checking

Right now, type checking is "syntactic" in that it applies to terms and is completely unaware of predicates. More powerful semantic checking will be added soon, and will amount to inferring the type of a predicate's head functor as the unification of its per-clause head types.

### Higher-kinded types

There don't appear to be any technical blockers. Hopefully the [`hilog`](https://us.swi-prolog.org/pack/list?p=hilog) pack can do the heavy-lifting.

### Tooling integration

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
$ cd t/
$ swipl -g "consult('*.plt'), run_tests" -t halt
```

---

(Note to self) To publish a new version:
1. update `pack.pl`
2. do GitHub release with new tag matching the pack.pl version
3. execute:
```prolog
?- make_directory(potato), pack_install(perfunctory_types, [url('http://github.com/GeoffChurch/perfunctory_types/archive/13.17.zip'), package_directory(potato)]).
```
