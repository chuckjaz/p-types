:- module(tc,[term_expansion/2]).

% Define >>= to be a transform of >>= similar to DCG --> but for types.

% This adds InEnv, InErr, OutEnv, OutErr arguments to the predicate and
% terms propagating the In/Out arguments to successive rules.

:- op(1150, xfx, >>=).

:- multifile user:term_expansion/2.
:- dynamic user:term_expansion/2.

tx_head(OriginalHead, InEnv, InErr, NewHead, OutEnv, OutErr) :-
    OriginalHead =.. OriginalHeadList,
    append(OriginalHeadList, [InEnv, InErr, OutEnv, OutErr], NewHeadList),
    NewHead =.. NewHeadList.

tx_terms((Term, Terms), InEnv, InErr, (NewTerm,NewTerms), OutEnv, OutErr) :- !,
    tx_term(Term, InEnv, InErr, NewTerm, NewInEnv, NewInErr),
    tx_terms(Terms, NewInEnv, NewInErr, NewTerms, OutEnv, OutErr).
tx_terms(Term, InEnv, InErr, NewTerm, OutEnv, OutErr) :-
    tx_term(Term, InEnv, InErr, NewTerm, OutEnv, OutErr).

tx_term(!, InEnv, InErr, !, InEnv, InErr) :- !.
tx_term(true, InEnv, InErr, true, InEnv, InErr) :- !.
tx_term({NoTxTerms}, InEnv, InErr, NoTxTerms, InEnv, InErr) :- !.
tx_term(Term, InEnv, InErr, NewTerm, OutEnv, OutErr) :-
    Term =.. TermList,
    append(TermList, [InEnv, InErr, OutEnv, OutErr], NewTermList),
    NewTerm =.. NewTermList.

user:term_expansion((OriginalHead >>= OriginalTerms), (NewHead :- NewTerms)) :-
    tx_head(OriginalHead, InEnv, InErr, NewHead, OutEnv, OutErr),
    tx_terms(OriginalTerms, InEnv, InErr, NewTerms, OutEnv, OutErr).