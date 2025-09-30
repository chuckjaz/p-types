:- use_module(tokens).
:- use_module(tc).
:- op(1150, xfx, >>=).

% T -> Type ::= C | T -> T | (T)
% C -> TC ::= TypeIdent

% M. M -> TLCE ::= c | x | λ(x: T).M | M N | (M)

% T -> Type ::= C | T -> T | (T)


% T -> Type ::= C | T -> T | (T)
% C -> TC ::= TypeIdent
type_expression_primitive(ast(name(N), source(S, E), type(_))) -->
    [identifier(N, S, E)], !.
type_expression_primitive(TypeExpression) -->
    [op(open_paren, _, _)], !,
    type_expression(TypeExpression),
    [op(close_paren, _, _)].

type_expression(TypeExpression) -->
    type_expression_primitive(Primitive),
    type_expression_tail(Primitive, TypeExpression).

type_expression_tail(Left, TypeExpression) -->
    [op(arrow, _, _)], !,
    type_expression(Right),
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), _) = Right },
    type_expression_tail(ast(arrow(Left, Right), source(S, E), type(_)), TypeExpression).
type_expression_tail(Left, Left) --> [].


expression_primitive(ast(number(N), source(S, E), type(_))) -->
    [number(N, S, E)].
expression_primitive(ast(name(N), source(S, E), type(_))) -->
    [identifier(N, S, E)].
expression_primitive(ast(lambda(P, T, B), source(S, E), type(_))) -->
    fun_prefix(S),
    [op(open_paren, _, _)],
    [identifier(P, _, _)],
    [op(colon, _, _)],
    type_expression(T),
    [op(close_paren, _, _)],
    [op(dot, _, _)],
    expression(B),
    { ast(_, source(_, E), _) = B}.
expression_primitive(Expression) -->
    [op(open_paren, _, _)],
    expression(Expression),
    [op(close_paren, _, _)].

fun_prefix(S) --> [op(lambda, S, _)].
fun_prefix(S) --> [fun(S, _)].

expression(Expression) -->
    expression_primitive(Left),
    expression_tail(Left, Expression).

expression_tail(Left, Expression) -->
    expression(Right),
    { ast(_, source(S, _), _) = Left, ast(_, source(_, E), _) = Right },
    expression_tail(ast(apply(Left, Right), source(S, E), type(_)), Expression).
expression_tail(Left, Left) --> [].


type_check(ast(number(_), _, type("Integer"))) >>= !.
type_check(ast(name(N), S, type(Type))) >>= lookup(N, S, Type).
type_check(ast(lambda(P, T, B), _, type(lambda(ParameterType, ResultType)))) >>=
    type_of_type(T, ParameterType),
    enter(P, ParameterType),
    type_check(B),
    matches_a(B, ResultType),
    retract.
type_check(ast(apply(Left, Right), _, type(Type))) >>=
    type_check(Left),
    type_check(Right),
    expect_lambda_type_a(Left, ParameterType, Type),
    matches_a(Right, ParameterType).
type_check(ast(_, S, type(error))) >>= report(["Unrecognized expression", S]).

type_of_type(ast(name(Name), _, type(Name)), Name) >>= !.
type_of_type(ast(arrow(Left, Right), _, type(Type)), Type) >>=
    type_of_type(Left, ParameterType),
    type_of_type(Right, ResultType),
    { Type = lambda(ParameterType, ResultType) }.
type_of_type(ast(_, S, type(error)), error) >>= report(["Unrecognized type expression", S]).

expect_lambda_type_a(ast(_, S, type(Type)), ParameterType, ResultType) >>=
    expect_lambda_type(Type, S, ParameterType, ResultType).
expect_lambda_type(lambda(ParameterType, ResultType), _, ParameterType, ResultType) >>= !.
expect_lambda_type(Type, S, error, error) >>=
    report(["Expected", Type, "to be a lambda type", S]).

matches_a(ast(_, S, type(T1)), T2) >>= matches(T1, T2, S).

matches(T, T, _) >>= !.
matches(error, _, _) >>= !.
matches(_, error, _) >>= !.
matches(T1, T2, S) >>= report(["Types do not match", T1, T2, S]).

enter(Name, Type, InEnv, InErr, [bind(Name, Type)|InEnv], InErr).
retract([_|InEnv], InErr, InEnv, InErr).
lookup(Name, S, Type, InEnv, InErr, InEnv, OutErr) :- lookup_in(Name, S, Type, InEnv, InErr, OutErr).

lookup_in(Name, _, Type, [bind(Name, Type)|_], InErr, InErr).
lookup_in(Name, S, Type, [_|Env], InErr, OutErr) :- lookup_in(Name, Type, S, Env, InErr, OutErr).
lookup_in(Name, S, error, [], InErr, OutErr) :-
    report(["Undefined", Name, S], [], [], InErr, OutErr).

report(Msg, InEnv, InEnv, InErr, OutErr) :- append([Msg], InErr, OutErr).

t(String, Parser) :-
    tokenize(String, Tokens),
    phrase(Parser, Tokens), !.

tc(String, Ast, Errors) :-
    tokenize(String, Tokens),
    phrase(expression(Ast), Tokens),
    type_check(Ast, [], _, [], Errors).