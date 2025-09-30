:- module(tokens, [tokenize/2]).

offsets([], _, []).
offsets([H|T1], N, [char(H, N)|T2]) :- N2 is N + 1, offsets(T1, N2, T2).
offsets(String, 0, Offsets) :- string_chars(String, Chars), offsets(Chars, 0, Offsets).

offsets(String, Offsets) :- offsets(String, 0, Offsets).

tokens([Token|Tokens]) -->
  token(Token), !,
  blanks,
  tokens(Tokens).
tokens([]) -->
  blanks.
tokens([Token]) -->
  token(Token).

token(op(Op, S, E)) --> { op_info([C1, C2], Op )}, [char(C1, S)], [char(C2, _)], { E is S + 2 }.
token(op(Op, S, E)) --> { op_info(C, Op) }, [char(C, S)], { E is S + 1 }.

token(Tk) -->
    ident_chars(Cs),
    {
      to_chars(Cs, chars(Id, S, E)),
      string_chars(Ids, Id),
      Tk1 = identifier(Ids, S, E),
      reserved_words(Tk1, Tk)
    }.

token(number(N, S, E)) -->
    digits(Ds),
    { to_chars(Ds, chars(Dss, S, E)), number_chars(N, Dss)}.

token(string(String, S, E)) -->
    [char('"', S)],
    string_chars(Chars),
    { string_chars(String, Chars) },
    [char('"', E)].


op_info('(', open_paren).
op_info(')', close_paren).
op_info(['{', '|'], open_record).
op_info(['|', '}'], close_record).
op_info('{', open_brace).
op_info('}', close_brace).
op_info('[', open_bracket).
op_info(']', close_bracket).
op_info('+', add).
op_info('-', subtract).
op_info('*', multiply).
op_info('/', divide).
op_info('%', modulus).
op_info([':', '='], write).
op_info(':', colon).
op_info(';', semicolon).
op_info('>', gt).
op_info(['>', '='], gte).
op_info('<', lt).
op_info(['<', '='], lte).
op_info('!', not).
op_info('=', assign).
op_info(['=', '='], equal).
op_info(['!', '='], not_equal).
op_info(['|', '|'], logical_or).
op_info(['&', '&'], logical_and).
op_info('&', and).
op_info('|', or).
op_info('?', question).
op_info("?:", coalesce).
op_info(',', comma).
op_info('.', dot).
op_info(['?', '.'], safe_dot).
op_info(['?', '('], safe_call).
op_info(['?', '['], safe_index).
op_info(['-', '>'], arrow).
op_info('λ', lambda).

reserved_words(identifier("break", S, E), break(S, E)).
reserved_words(identifier("case", S, E), case(S, E)).
reserved_words(identifier("continue", S, E), continue(S, E)).
reserved_words(identifier("else", S, E), else(S, E)).
reserved_words(identifier("false", S, E), false(S, E)).
reserved_words(identifier("for", S, E), for(S, E)).
reserved_words(identifier("fun", S, E), fun(S, E)).
reserved_words(identifier("if", S, E), if(S, E)).
reserved_words(identifier("in", S, E), in(S, E)).
reserved_words(identifier("is", S, E), is(S, E)).
reserved_words(identifier("interface", S, E), interface(S, E)).
reserved_words(identifier("nop", S, E), nop(S, E)).
reserved_words(identifier("null", S, E), null(S, E)).
reserved_words(identifier("of", S, E), of(S, E)).
reserved_words(identifier("proj", S, E), proj(S, E)).
reserved_words(identifier("ref", S, E), ref(S, E)).
reserved_words(identifier("return", S, E), return(S, E)).
reserved_words(identifier("then", S, E), then(S, E)).
reserved_words(identifier("trait", S, E), trait(S, E)).
reserved_words(identifier("true", S, E), true(S, E)).
reserved_words(identifier("unit", S, E), unit(S, E)).
reserved_words(identifier("val", S, E), val(S, E)).
reserved_words(identifier("value", S, E), value(S, E)).
reserved_words(identifier("var", S, E), var(S, E)).
reserved_words(identifier("void", S, E), void(S, E)).
reserved_words(identifier("when", S, E), when(S, E)).
reserved_words(identifier("while", S, E), while(S, E)).
reserved_words(Id, Id).

blanks --> [char(C, _)], { member(C, [' ', '\t', '\n', '\r'])}, blanks.
blanks --> [].

digits([D|Ds]) --> digit(D), digits(Ds).
digits([D]) --> digit(D).
digit(char(D, S)) --> [char(D, S)], { code_type(D, digit) }.


string_chars([C|Cs]) --> string_continue_char(C), string_chars(Cs).
string_chars([C]) --> string_continue_char(C).

string_continue_char(C) --> [char(C, _)], { \+ C = '"' }.

ident_chars([C|Cs]) --> ident_start(C), ident_tail(Cs).
ident_chars([C]) --> ident_start(C).
ident_tail([C|Cs]) --> ident_continue(C), ident_tail(Cs).
ident_tail([C]) --> ident_continue(C).

ident_start(char(C, S)) --> [char(C, S)], { code_type(C, alpha) }.
ident_start(char(S, S)) --> [char('_', S)].

ident_continue(char(C, S)) --> [char(C, S)], { code_type(C, alnum) }.
ident_continue(char('_', S)) --> [char('_', S)].

to_chars([char(C, S)], chars([C], S, E)) :- E is S + 1.
to_chars([char(C, S)|Cs], chars([C|Ct], S, E)) :-
    to_chars(Cs, chars(Ct, _, E)).

to_reserved([Token|Tokens], [NewToken|NewTokens]) :- reserved_words(Token, NewToken), to_reserved(Tokens, NewTokens).
to_reserved([], []).

tokenize(String, Tokens) :-
    offsets(String, Chars),
    phrase(tokens(Tokens), Chars), !.
