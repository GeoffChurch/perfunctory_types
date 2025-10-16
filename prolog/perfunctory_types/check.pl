:- module(check, [typecheck/5]).

:- use_module(library(perfunctory_types/util), [cata/3, cyclesafe_type/4, dealias/3,
		     must_be_undeclared_type/3]).

:- use_module(library(subsumes), [subsumes/2]).

:- det(typecheck/5).

predcheck(Infers, Ctor, TermType) :-
    get_assoc(Ctor, Infers, PredType)
    -> subsumes(PredType, TermType)
    ;  true.

typecheck(Types, Aliases, Infers, Term, Type) :-
    $(dealias(Aliases, Type, CanonicalType)),
    catch(cata(typecheck_(Types, Aliases, Infers), Term, CanonicalType),
	  error(determinism_error(PT=T,det,fail,goal), Ctx),
	  throw(error(ill_typed(expected_type(T), got_type(PT)),
		      Ctx))).

typecheck_(Types, Aliases, Infers, PreType, Type) =>
    % Try to look up the "full" type (if PreType is a function type
    % then Type is too).
    $(functor(PreType, Ctor, _)),
    predcheck(Infers, Ctor, Type),
    (
        cyclesafe_type(Types, Ctor, FullPreType, FullType)
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
            must_be_undeclared_type(Types, Aliases, PreType),
            (Type = PreType % Skolemize.
            -> true
            ;  throw(error(ill_typed(expected_type(Type),
                                    got_untyped_term(PreType)), _)))
    ).

matchargs(PartTerm, PartType, FullTerm, FullType) :-
    $(PartTerm =.. [F|PartArgs]),
    $(FullTerm =.. [F|FullArgs]),
    % If RestArgs = [] then PartType = FullType.
    (append(PartArgs, RestArgs, FullArgs)
    *-> true
    ;  throw(error(ill_typed(expected(FullTerm), got(PartTerm)), _))),
    % PartType should be a chain of arrows through each of RestArgs
    % before ending at FullType.
    (arrow_list(PartType, RestArgs, FullType)
    *-> true
    ;   throw(error(ill_typed(expected_type(FullType), got(PartType)),
		    _))).

arrow_list(FullType, [], FullType).
arrow_list(X->Arrows, [X|List], RestArrows) :-
    arrow_list(Arrows, List, RestArrows).
