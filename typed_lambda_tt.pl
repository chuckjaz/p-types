:- use_module(tokens).
:- use_module(tc).
:- op(1150, xfx, >>=).

% Parsing

% T -> Type ::= C | void | T -> T | T * T | T + T | {| (l: T)* |} | ref T | unit

type_expression_primitive(ast(name(Name), source(S, E), type(_))) --> [identifier(Name, S, E)].
type_expression_primitive(ast(void, source(S, E), type(_))) --> [void(S, E)].
type_expression_primitive(ast(unit, source(S, E), type(_))) --> [unit(S, E)].
type_expression_primitive(ast(record(Members), source(S, E), type(_))) -->
    [op(open_record, S, _)],
    record_members(Members),
    [op(close_record, _, E)].
type_expression_primitive(ast(ref(Target), source(S, E), type(_))) -->
    [ref(S, _)],
    type_expression(Target),
    { ast(_, source(_, E), _) = Target }.
type_expression_primitive(TypeExpression) -->
    [op(open_paren, _, _)],
    type_expression(TypeExpression),
    [op(close_paren, _, _)].

record_members(Members) -->
    record_member(Member),
    record_member_tail(Member, Members).
record_members([]) --> [].

record_member_tail(Member, [Member | Members]) -->
    [op(semicolon, _, _)],
    record_member(NewMember),
    record_member_tail(NewMember, Members).
record_member_tail(Member, [Member]) --> [].

record_member(ast(member(N, Type), source(S, E), type(_))) -->
    [identifier(N, S, _)],
    [op(colon, _, _)],
    type_expression(Type),
    { ast(_, source(_, E), _) = Type}.

type_expression(TypeExpression) -->
    tuple_type_expression(Left),
    type_expression_tail(Left, TypeExpression).

type_expression_tail(Left, TypeExpression) -->
    [op(arrow, _, _)],
    type_expression(Right),
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), _) = Right },
    { TypeExpression = ast(lambda(Left, Right), source(S, E), type(_)) }.
type_expression_tail(Left, Left) --> [].

tuple_type_expression(TypeExpression) -->
    or_type_expression(Left),
    tuple_type_expression_tail(Left, TypeExpression).

tuple_type_expression_tail(Left, TypeExpression) -->
    [op(multiply, _, _)],
    tuple_type_expression(Right),
    { simplify_tuple(Left, Right, TypeExpression) }.
tuple_type_expression_tail(Left, Left) --> [].

simplify_tuple(
    ast(tuple(Left), source(S, _), _),
    ast(tuple(Right), source(_, E), _),
    ast(tuple(Both), source(S, E), type(_))) :- append(Left, Right, Both).
simplify_tuple(Type, ast(tuple(Right), source(_, E), type(_)), ast(tuple([Type|Right]), source(S, E), type(_))) :-
    ast(_, source(S, _), _) = Type.
simplify_tuple(ast(tuple(Left), source(S, _), _), Type, ast(tuple(Both), source(S, E), type(_))) :-
    ast(_, source(_, E), _) = Type,
    append(Left, [Type], Both).
simplify_tuple(T1, T2, ast(tuple([T1, T2]), source(S, E), type(_))) :-
    ast(_, source(S, _), _) = T1,
    ast(_, source(_, E), _) = T2.

or_type_expression(TypeExpression) -->
    type_expression_primitive(Left),
    or_type_expression_tail(Left, TypeExpression).

or_type_expression_tail(Left, TypeExpression) -->
    [op(add, _, _)],
    or_type_expression(Right),
    { simplify_or(Left, Right, TypeExpression) }.
or_type_expression_tail(Left, Left) --> [].

simplify_or(
    ast(or(Left), source(S, _), _),
    ast(or(Right), source(_, E), _),
    ast(or(Both), source(S, E), type(_))) :- append(Left, Right, Both).
simplify_or(Type, ast(or(Right), source(_, E), type(_)), ast(or([Type|Right]), source(S, E), type(_))) :-
    ast(_, source(S, _), _) = Type.
simplify_or(ast(or(Left), source(S, _), _), Type, ast(or(Both), source(S, E), type(_))) :-
    ast(_, source(_, E), _) = Type,
    append(Left, [Type], Both).
simplify_or(T1, T2, ast(or([T1, T2]), source(S, E), type(_))) :-
    ast(_, source(S, _), _) = T1,
    ast(_, source(_, E), _) = T2.


% M -> RLCE ::= x | c | unit | fun(x: T).M | M N | < M* > | proj(M) |
%               case M of (x: T then M)* [else M] |
%               in[T](M) | {| (l: T = M)* |} | M.l |
%               ref M | null | val M | if M then { M } else { M } |
%               nop | N := M | M ; N

primitive_expression(ast(name(Name), source(S, E), type(_))) --> [identifier(Name, S, E)].
primitive_expression(ast(number(N), source(S, E), type(_))) --> [number(N, S, E)].
primitive_expression(ast(boolean(true), source(S, E), type(_))) --> [true(S, E)].
primitive_expression(ast(boolean(false), source(S, E), type(_))) --> [false(S, E)].
primitive_expression(ast(unit, source(S, E), type(_))) --> [unit(S, E)].
primitive_expression(ast(null, source(S, E), type(_))) --> [null(S, E)].
primitive_expression(ast(void, source(S, E), type(_))) --> [void(S, E)].
primitive_expression(ast(lambda(Parameter, Type, Body), source(S, E), type(_))) -->
    [fun(S, _)],
    [op(open_paren, _, _)],
    [identifier(Parameter, _, _)],
    [op(colon, _, _)],
    type_expression(Type),
    [op(close_paren, _, _)],
    [op(dot, _, _)],
    expression(Body),
    { ast(_, source(_, E), type(_)) = Body }.
primitive_expression(ast(tuple(Members), source(S, E), type(_))) -->
    [op(lt, S, _)],
    tuple_expression_members(Members),
    [op(gt, _, E)].
primitive_expression(ast(case(Target, Clauses), source(S, E), type(_))) -->
    [case(S, _)],
    expression(Target),
    [of(_, _)],
    case_clauses(Clauses),
    { last_of_l(Clauses, E) }.
primitive_expression(ast(in(Type, Body), source(S, E), type(_))) -->
    [in(S, _)],
    [op(open_bracket, _, _)],
    type_expression(Type),
    [op(close_bracket, _, _)],
    [op(open_paren, _, _)],
    expression(Body),
    [op(close_paren, _, E)].
primitive_expression(ast(record(Members), source(S, E), type(_))) -->
    [op(open_record, S, _)],
    record_expression_members(Members),
    [op(close_record, _, E)].
primitive_expression(ast(ref(Target), source(S, E), type(_))) -->
    [ref(S, _)],
    simple_expression(Target),
    { ast(_, source(_, E), _) = Target }.
primitive_expression(ast(val(Target), source(S, E), type(_))) -->
    [val(S, _)],
    simple_expression(Target),
    { ast(_, source(_, E), _) = Target }.
primitive_expression(ast(if(Cond, Then, Else), source(S, E), type(_))) -->
    [if(S, _)],
    expression(Cond),
    [then(_, _)],
    [op(open_brace, _, _)],
    expression(Then),
    [op(close_brace, _, _)],
    [else(_, _)],
    [op(open_brace, _, _)],
    expression(Else),
    [op(close_brace, _, E)].
primitive_expression(ast(nop, source(S, E), type(_))) -->
    [nop(S, E)].
primitive_expression(Expression) -->
    [op(open_paren, _, _)],
    expression(Expression),
    [op(close_paren, _, _)].

tuple_expression_members(Members) -->
    expression(Member),
    tuple_expression_members_tail(Member, Members).

tuple_expression_members_tail(Member, [Member| Members]) -->
    [op(comma, _, _)],
    expression(NewMember),
    tuple_expression_members_tail(NewMember, Members).
tuple_expression_members_tail(Member, [Member]) --> [].

case_clauses(Clauses) -->
    case_clause(Clause),
    case_clauses_tail(Clause, Clauses).

case_clauses_tail(Clause, [Clause | Clauses]) -->
    case_clause(NewClause),
    case_clauses_tail(NewClause, Clauses).
case_clauses_tail(Clause, [Clause]) --> [].

case_clause(ast(then(Name, Type, Body), source(S, E), type(_))) -->
    [identifier(Name, S, _)],
    [op(colon, _, _)],
    type_expression(Type),
    [then(_, _)],
    expression(Body),
    { ast(_, source(_, E), _) = Body }.
case_clause(ast(else(Body), source(S, E),type(_))) -->
    [else(S, _)],
    expression(Body),
    { ast(_, source(_, E), _) = Body }.

type_list(Types) -->
    type_expression(Type), type_list_tail(Type, Types).

type_list_tail(Type, [Type | Types]) -->
    [op(comma, _, _)],
    type_expression(NewType),
    type_list_tail(NewType, Types).
type_list_tail(Type, [Type]) --> [].

record_expression_members(Members) -->
    record_expression_member(Member),
    record_expression_members_tail(Member, Members).

record_expression_members_tail(Member, [Member | Members]) -->
    [op(comma, _, _)],
    record_expression_member(NewMember),
    record_expression_members_tail(NewMember, Members).
record_expression_members_tail(Member, [Member]) --> [].

record_expression_member(ast(member(Name, Type, Value), source(S, E), type(_))) -->
    [identifier(Name, S, _)],
    [op(colon, _, _)],
    type_expression(Type),
    [op(assign, _, _)],
    expression(Value),
    { ast(_, source(_, E), _) = Value }.

simple_expression(Expression) -->
    primitive_expression(Left),
    simple_expression_tail(Left, Expression).

simple_expression_tail(Left, Expression) --> [op(dot, _, _)], selection_tail(Left, Expression).
simple_expression_tail(Left, Expression) --> [op(dot, _, _)], projection_tail(Left, Expression).
simple_expression_tail(Left, ast(write(Left, Right), source(S, E), type(_))) -->
    [op(write, _, _)],
    expression(Right),
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), _) = Right }.
simple_expression_tail(Left, Left) --> [].

selection_tail(Left, Expression) -->
    [identifier(Name, _, E)],
    { NewLeft = ast(selection(Left, Name), source(S, E), type(_)) },
    { ast(_, source(S, _), _) = Left },
    simple_expression_tail(NewLeft, Expression).

projection_tail(Left, Expression) -->
    [number(N, _, E)],
    { NewLeft = ast(projection(Left, N), source(S, E), type(_)) },
    { ast(_, source(S, _), _) = Left },
    simple_expression_tail(NewLeft, Expression).

apply_expression(Expression) -->
    simple_expression(Left),
    apply_expression_tail(Left, Expression).

apply_expression_tail(Left, Expression) -->
    simple_expression(Right),
    { NewLeft = ast(apply(Left, Right), source(S, E), type(_)) },
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), type(_)) = Right },
    apply_expression_tail(NewLeft, Expression).
apply_expression_tail(Left, Left) --> [].

sequence(Expression) -->
    apply_expression(Left),
    sequence_tail(Left, Expression).
sequence_tail(Left, Expression) -->
    [op(semicolon, _, _)],
    apply_expression(Right),
    { NewLeft = ast(sequence(Left, Right), source(S, E), type(_)) },
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), type(_)) = Right },
    sequence_tail(NewLeft, Expression).
sequence_tail(Left, Left) --> [].

expression(Expression) --> sequence(Expression).

% Type Checking

% Identifier: E + {x: T} |- x: T
type_check(ast(name(Name), S, type(Type))) >>= lookup(Name, S, Type).

% Constant: E |- c: N
type_check(ast(number(_), _, type(int))) >>= !.
type_check(ast(boolean(_), _, type(boolean))) >>= !.

% Void: E |- void: void
type_check(ast(void, _, type(void))) >>= !.
type_check(ast(unit, _, type(unit))) >>= !.

% Function: (E + {x: S} |- M: T) |- (E |- fun(x: S).M: S -> T)
type_check(ast(lambda(ParameterName, ParameterTypeExpr, Body), _, type(FunctionType))) >>=
    type_of_type(ParameterTypeExpr, ParameterType),
    enter(ParameterName, ParameterType),
    type_check(Body),
    matches_a(Body, ResultType),
    { FunctionType = lambda(ParameterType, ResultType) }.

% Apply: (E |- M: S -> T, E |- N: S) |- (E |- M N : T)
type_check(ast(apply(Left, Right), _, type(Type))) >>=
    type_check(Left),
    type_check(Right),
    matches_a(Left, lambda(Parameter, Type)),
    matches_a(Right, Parameter).

% Tuple: (E |- M[i]: T[i], for all i <= i <= n) |- (E |- <M[1]..M[n])>: T[i] * ... T[n]
type_check(ast(tuple(Expressions), S, type(Type))) >>=
    type_check_l(Expressions, Types),
    matches(Type, tuple(Types), S).

% Projection: (E |- M: T[i] * ... * T[n]) |- ( E |- proj[i](M): T[i])
type_check(ast(projection(Target, N), _, type(Type))) >>=
    type_check(Target),
    projection_check_a(Target, N, Type).

% Sum: (E |- M: T[i] for some 1 <= i <= n) |- (E |- in[T[1]+ ... T[n]](M): T[1]+ ... T[n]])
type_check(ast(in(TypeExpression, Target), _, type(Type))) >>=
    type_check(Target),
    type_of_type(TypeExpression, Type),
    match_or_type_a_a(Target, TypeExpression).

% Case: (E |- M: T[1] + ... + T[n], E + { x[i]: T[i] } |- E[i]: U) |- (E |- case M of x[1] then E[1] ... x[n] then E[n]: U)
type_check(ast(case(Target, Clauses), _, type(Type))) >>=
    type_check(Target),
    type_check_clauses(Target, Clauses, Type).

% Record: (E |- M[i] : T[i]) |- (E |- {| l[i]: T[i] = M[i] |}: {| l[i]: M[i] })
type_check(ast(record(MemberAsts), _, type(record(Members)))) >>=
    type_check_members(MemberAsts, Members).

% Selection: (E |- M : {| l[i] : T[i] |}) |- (E |- M.l[i] : T[i])
type_check(ast(selection(Target, Name), _, type(Type))) >>=
    type_check(Target),
    type_check_selection(Target, Name, Type).

% Reference: (E |- M: T) |- (E |- ref M: Ref T)
type_check(ast(ref(Target), _, type(Type))) >>=
    type_check(Target),
    matches_a(Target, TargetType),
    matches(Type, ref(TargetType)).

% Null: (E |- null: Ref T)
type_check(ast(null, _, type(ref(_)))) >>= !.

% Value: (E |- M: Ref T) |- (E |- val M: T)
type_check(ast(val(Target), _, type(Type))) >>=
    type_check(Target),
    matches_a(Target, ref(Type)).

% No-op: (E |- nop: Unit)
type_check(ast(nop, _, type(unit))) >>= !.

% Assignment: (E |- N: Ref T, M: T) |- (E |- N := M : Unit)
type_check(ast(write(Target, Value), _, type(unit))) >>=
    type_check(Target),
    type_check(Value),
    matches_a(Target, ref(TargetType)),
    matches_a(Value, ValueType),
    matches(TargetType, ValueType).

% Conditional: (E |- B: Boolean, E |- M:T, E |- N: T) |- (E |- if B then { M } else { N } : T)
type_check(ast(if(Cond, Then, Else), _, type(Type))) >>=
    type_check(Cond),
    type_check(Then),
    type_check(Else),
    matches_a(Cond, boolean),
    matches_a(Then, Type),
    matches_a(Else, Type).

% Sequence: (E := M: S, E |- N: T) |- (E |- M ; N : T)
type_check(ast(sequence(Left, Right), _, type(Type))) >>=
    type_check(Left),
    type_check(Right),
    matches_a(Right, Type).

type_check_l([Expression|Expressions], [Type|Types]) >>=
    type_check(Expression),
    matches_a(Expression, Type),
    type_check_l(Expressions, Types).
type_check_l([], []) >>= !.

projection_check_a(ast(_, S, type(tuple(Types))), N, Type) >>= projection_check(Types, N, S, Type).
projection_check_a(ast(_, S, type(error)), _, error) >>= report(["Expected a tuple type", S]).

projection_check([Type|_ ], 1, _, Type) >>= !.
projection_check(_, 0, S, error) >>= report(["Projection index out of bound", S]).
projection_check([_|Types], N, S, Type) >>=
    { NN is N - 1 },
    projection_check(Types, NN, S, Type).

type_check_clauses(Target, [Clause|Clauses], Type) >>=
    type_check_clause(Target, Clause, Type),
    type_check_clauses(Target, Clauses, Type).

type_check_clause(Target, ast(then(Name, TypeExpression, Body), _, type(BodyType)), Type) >>=
    type_of_type(TypeExpression, NameType),
    match_or_type_a_a(Target, TypeExpression),
    enter(Name, NameType),
    type_check(Body),
    retract,
    matches_a(Body, BodyType),
    matches_a(Body, Type).

type_check_clause(_, ast(else(Body), _, type(BodyType)), Type) >>=
    type_check(Body),
    matches_a(Body, BodyType),
    matches_a(Body, Type).

type_check_members([MemberAst | MemberAsts], [Member | Members]) >>=
    type_check_member(MemberAst, Member),
    type_check_members(MemberAsts, Members).
type_check_members([], []) >>= !.

type_check_member(ast(member(Name, TypeExpression, Value), _, type(MemberType)), member(Name, MemberType)) >>=
    type_of_type(TypeExpression, MemberType),
    type_check(Value),
    matches_a(Value, MemberType).

type_check_selection(ast(_, S, type(record(Members))), Name, Type) >>=
    type_check_selection_l(Name, S, Members, Type).
type_check_selection(ast(_, S, _), Name, error) >>= report(["Expected a record type with a member named", Name, S]).

type_check_selection_l(Name, _, [member(Name, Type)|_], Type) >>= !.
type_check_selection_l(Name, S, [_|Members], Type) >>= type_check_selection_l(Name, S, Members, Type).
type_check_selection_l(Name, S, [], error) >>=
    report(["Record has no member named", Name, S]).

type_of_type(ast(name(Name), S, type(Type)), Type) >>= lookup_type(Name, S, Type).
type_of_type(ast(void, _, type(void)), void) >>= !.
type_of_type(ast(unit, _, type(unit)), unit) >>= !.
type_of_type(ast(lambda(Parameter, Result), _, type(Type)), Type) >>=
    type_of_type(Parameter, ParameterType),
    type_of_type(Result, ResultType),
    matches(Type, lambda(ParameterType, ResultType)).
type_of_type(ast(tuple(TypeExpressions), _, type(Type)), Type) >>=
    type_of_type_l(TypeExpressions, Types),
    matches(Type, tuple(Types)).
type_of_type(ast(or(TypeExpressions), S, type(Type)), Type) >>=
    type_of_type_l(TypeExpressions, Types),
    matches(Type, or(Types), S).
type_of_type(ast(record(MembersAst), _, type(Type)), Type) >>=
    type_of_members(MembersAst, Members),
    matches(Type, record(Members)).
type_of_type(ast(ref(TypeExpression), _, type(Type)), Type) >>=
    type_of_type(TypeExpression, Target),
    matches(Type, ref(Target)).

type_of_type_l([TypeExpression|TypeExpressions], [Type|Types]) >>=
    type_of_type(TypeExpression, Type),
    type_of_type_l(TypeExpressions, Types).
type_of_type_l([], []) >>= !.

type_of_members([MemberAst | MemberAsts], [Member | Members]) >>=
    type_of_member(MemberAst, Member),
    type_of_members(MemberAsts, Members).
type_of_members([], []) >>= !.

type_of_member(ast(member(Name, TypeExpression), _, type(Type)), member(Name, Type)) >>=
    type_of_type(TypeExpression, Type).

match_or_type_a_a(ast(_, _, type(TargetType)), ast(_, S, type(or(Types)))) >>=
    match_one_of(TargetType, S, Types).
match_or_type_a_a(ast(_, S, _), _) >>=
    report(["Expected OR type", S]).

match_one_of(Type, _, [Type|_]) >>= !.
match_one_of(Type, S, []) >>= report(["Type", Type, "doesn't match any part of the sum type", S]).

% Utilities

last_of(ast(_, source(_, E), _), E).
last_of_l([ast(_, source(_, E), _)], E).
last_of_l([_|T], E) :- last_of_l(T, E).

matches_a(ast(_, S, type(T1)), T2) >>= matches(T1, T2, S).

matches_a_a(ast(_, S, type(T1)), ast(_, _, type(T2))) >>= matches(T1, T2, S).

matches(T, T, _) >>= !.
matches(error, _, _) >>= !.
matches(_, error, _) >>= !.
matches(T1, T2, S) >>= report(["Types do not match", T1, T2, S]).

enter(Name, Type, InEnv, InErr, [bind(Name, Type)|InEnv], InErr).
enter(Name, Type, InEnv, InErr, [type(Name, Type)|InEnv], InErr).

retract([_|InEnv], InErr, InEnv, InErr).

lookup(Name, S, Type, InEnv, InErr, InEnv, OutErr) :- lookup_in(bind(Name, Type), S, InEnv, InErr, OutErr).

lookup_type(Name, S, Type, InEnv, InErr, InEnv, OutErr) :- lookup_in(type(Name, Type), S, InEnv, InErr, OutErr).

lookup_in(Binding, _, [Binding|_], InErr, InErr).
lookup_in(Binding, S, [_|Env], InErr, OutErr) :- lookup_in(Binding, S, Env, InErr, OutErr).
lookup_in(Binding, S, _, InErr, OutErr) :-
    name_of(Binding, Name),
    report(["Undefined", Name, S], [], [], InErr, OutErr).

name_of(bind(Name, _), Name  ).
name_of(type(Name, _), Name).

report(Msg, InEnv, InEnv, InErr, OutErr) :- append([Msg], InErr, OutErr).

t(String, Parser) :-
    tokenize(String, Tokens),
    phrase(Parser, Tokens), !.

builtins([
    type("Integer", int),
    type("Boolean", boolean)
]).

tc(String, Ast, Errors) :-
    tokenize(String, Tokens),
    phrase(expression(Ast), Tokens),
    builtins(Builtins),
    type_check(Ast, Builtins, [], _, Errors).

tc(String) :- tc(String, Ast, Errors), write("Ast: "), write(Ast), write("\nErrors: "), write(Errors), !.

ttc(String) :-
    tokenize(String, Tokens),
    phrase(expression(Ast), Tokens),
    builtins(Builtins),
    trace,
    type_check(Ast, Builtins, [], _, Errors), !.

test(String, Type) :-
    tc(String, Ast, Errors),
    validate(String, Ast, Type, Errors), !.

validate(String, ast(_, _, type(Type)), Type, []) :- write("pass: "), write(String), write("~>"), write(Type), write("\n"), !.
validate(String, ast(_, _, type(Type)), Expected, Errors) :- write("failed: "), write(String), write(" "), write(Errors), write("\n"),
    write(" ...Expected: "), write(Expected), write(" Received: "), write(Type), write("\n"), !.

tests :-
    test("1", int),
    test("true", boolean),
    test("false", boolean),
    test("void", void),
    test("unit", unit),
    test("fun(x: Integer).x", lambda(int, int)),
    test("<1, true>", tuple([int, boolean])),
    test("<1, true>.1", int),
    test("<1, true>.2", boolean),
    test("in[Integer+Boolean](1)", or([int, boolean])),
    test("{| x: Integer = 1, y: Integer = 2 |}", record([member("x", int), member("y", int)])),
    test("{| x: Integer = 1, y: Integer = 2 |}.x", int).