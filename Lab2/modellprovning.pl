% Authors: Felix Hedenström and Jonathan Rinnarv
% Load model, initial state and formula from file.
verify(Input) :-
	see(Input), read(T), read(L), read(S), read(F), seen,
	check(T, L, S, [], F),
	!.
% check(T, L, S, U, F)
%     T - The transitions in form of adjacency lists
%     L - The labeling
%     S - Current state
%     U - Currently recorded states
%     F - CTL Formula to check.
%
% Should evaluate to true iff the sequent below is valid.
%
% (T,L), S  |-    F
%             U
% To execute: consult('your_file.pl'). verify('input.txt').

getValue([[Key|[Return_list]]|_],Key,Return_list):- !.

getValue([_|T],Key,Return_list):-
	getValue(T,Key,Return_list).


% Checks if F and G are true at S
check(T,L,S,_, and(F,G)):-
	check(T,L,S,[],F),
	check(T,L,S,[],G).


% Checks if F or G is true at S
check(T, L, S, _, or(F,G)):-
	check(T,L,S,[],F); 
	check(T,L,S,[],G).


% I alla nästa tillstånd ska F gälla. Man tittar alltså inte nödvändigtvis på sig själv om man inte har en loop som går tillbaka till sig själv
check(T,L,S,_,ax(F)):-
	getValue(T,S,S_NEXTS),
	forall(member(X,S_NEXTS),check(T,L,X,[],F)).

% I något nästa tillstånd ska F gälla. Man behöver inte titta på sig själv
check(T,L,S,_,ex(F)):-
	getValue(T,S,S_NEXTS),
	member(X,S_NEXTS),
	check(T,L,X,[],F).


% AG1
check(T, L, S, U, ag(F)):-
	member(S,U),
	check(T, L, S, [], F).

% AG2
check(T , L, S, U, ag(F)):-
	not(member(S,U)),
	check(T, L, S, [], F),
	getValue(T,S,S_NEXTS),	
	forall(member(X,S_NEXTS), check(T,L,X,[S|U],ag(F))).

% EG1
check(_,_,S, U, eg(_)):-
	member(S,U).

% EG2
check(T , L, S, U, eg(F)):-
	not(member(S,U)),
	check(T, L, S, [], F),
	getValue(T,S,S_NEXTS),
	member(X, S_NEXTS),
	check(T, L, X, [S|U], eg(F)).

% AF1
check(T , L, S, U, af(F)):-
	not(member(S,U)),
	check(T,L,S,[],F).

% AF2
check(T, L, S, U, af(F)):-
	not(member(S,U)),
	getValue(T,S,S_NEXTS),
	forall(member(X,S_NEXTS), check(T,L,X,[S|U],af(F))).

% EF1
check(T, L, S, U, ef(F)):-
	not(member(S,U)),
	check(T,L,S,[],F).

% EF2
check(T,L,S,U,ef(F)):-
	not(member(S,U)),
	getValue(T,S,S_NEXTS),
	member(X,S_NEXTS),
	check(T,L,X,[S|U],ef(F)).

% If X is not present at L(s) this predicate is true
check(_, L, S, [], neg(X)) :- 
	getValue(L,S,List),
	not(member(X,List)).

% If X is present at L(s)
check(_ , L, S, [], X):-
	getValue(L,S,List),
	member(X,List).