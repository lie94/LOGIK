% Regler
verify(Input):-
	see(Input),
	read(Prems),
	read(Goal),
	read(Proof),
	seen,
	valid_proof(Prems, Goal, Proof).

valid_proof(Prems, Goal, Proof):-
	iter_proof(Prems, Goal, Proof, Proof).

iter_proof(_,Goal,[[_,X,_]|[]],_):-
	!,
	Goal = X.
iter_proof(Prems, Goal, [ H	|Tail], StaticProof):-
	not(isBox(H)),
	assertRule(H,Prems,StaticProof),
	iter_proof(Prems,Goal, Tail, StaticProof).

assertRule([_,X,premise],Prems,_):-
	member(X,Prems).

assertRule([_,X,negnegel(Y),_,StaticProof]):-
	getStatement(Y,StaticProof,S),
	X = S.

isBox([[_|_]|_]).

getStatement(L, [[L,X,_]|_], X):- !.

getStatement(L, [H|Tail],X):-
	isBox(H),
	!,
	getStatement(L,H,X);getStatement(L,Tail,X).

getStatement(Line, [_|Tail], Statement):-
	!,
	getStatement(Line,Tail, Statement).


/*premise.
assumption.
copy(x).
andint(x,y).
andel1(x).
andel2(x).
orint1(x).
orint2(x).
orel(x,y,u,v,w).
impint(x,y).
impel(x,y).
negint(x,y).
negel(x,y).
contel(x).s
nenegint(x).
negnegel(x).
mt(x,y).
pbc(x,y).
lem.*/