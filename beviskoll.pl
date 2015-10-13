% Regler
verify(Input):-
	see(Input),
	read(Prems),
	read(Goal),
	read(Proof),
	seen,
	!,
	valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof):-
	iter_proof(Prems, Goal, Proof, false,Proof),
	!.

iter_proof(_,Goal,[[_,X,_]|[]],IsInBox,_):-
	not(IsInBox),
	!,
	Goal = X.
iter_proof(Prems,_,[H|[]],true,StaticProof):-
	not(isBox(H)),
	!,
	assertRule(H,Prems,StaticProof).
iter_proof(Prems, Goal, [ H	|Tail], IsInBox, StaticProof):-
	not(isBox(H)),
	!,
	assertRule(H,Prems,StaticProof),
	!,
	iter_proof(Prems,Goal, Tail, IsInBox, StaticProof).
%Om vi går in i en ny box
iter_proof(Prems, Goal, [H|Tail], IsInBox, StaticProof):-
	!,
	iter_proof(Prems, Goal, H, true,StaticProof),
	!,
	iter_proof(Prems, Goal, Tail, IsInBox, StaticProof).

isBox([[_|_]|_]).

getStatement(L, [[L,X,_]|_], X):- !.

% Man kan hämta från lådor som man inte har tillåtelse för att hämta ifrån
getStatement(L, [H|Tail],X):-
	isBox(H),
	!,
	getStatement(L,H,X);getStatement(L,Tail,X).

getStatement(Line, [_|Tail], Statement):-
	!,
	getStatement(Line,Tail, Statement).

assertRule([_,X,premise],Prems,_):-
	member(X,Prems).

assertRule([_,_,assumption],_,_).

assertRule([_,X,copy(N)],_,StaticProof):-
	getStatement(N,StaticProof,S),
	X = S.

assertRule([_,and(X,Y),andint(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Y).

assertRule([_,X,andel1(N)],_,StaticProof):-
	getStatement(N1,StaticProof,and(X,_)).

assertRule([_,X,andel2(N)],_,StaticProof):-
	getStatement(N1,StaticProof,and(_,X)).

assertRule([_,X,negnegel(N)],_,StaticProof):-
	getStatement(N,StaticProof,neg(neg(S))),
	X = S.

assertRule([_,X,impel(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,S1),
	getStatement(N2,StaticProof,imp(S1,X)).
assertRule([_,cont,negel(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,S1),
	getStatement(N2,StaticProof,neg(S1)).
assertRule([_,neg(X),negint(N1,N2)],_,StaticProof):-
	getStatement(N2,StaticProof,cont),
	getStatement(N1,StaticProof,X).
assertRule([_,or(X,neg(X)),lem],_,_).

/*
orint1(x).
orint2(x).
orel(x,y,u,v,w).
impint(x,y).
negel(x,y).
contel(x).s
nenegint(x).
negnegel(x).
mt(x,y).
pbc(x,y).*/