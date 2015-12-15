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


% L1 är den som försöker hämta information från L2
checkLines(L1,L2,StaticProof):-
	L1 > L2,
	lineIdentifier(L1,L2,StaticProof).

targetLine(_,_,[]):- !,false.
targetLine(L1,L2,[[L2,_,_]|Tail]):-
	callerLine(L1,Tail).

targetLine(L1,L2,[[_,_,_]|Tail]):-
	!,
	targetLine(L1,L2,Tail).
targetLine(L1,L2,[H|Tail]):-
	!,
	targetLine(L1,L2,H);
	targetLine(L1,L2,Tail).

callerLine(_,[]):- false.
callerLine(L1,[[L1,_,_]|_]).
callerLine(L1,[[_,_,_]|Tail]):-
	callerLine(L1,Tail).
callerLine(L1,[H|Tail]):-
	!,
	callerLine(L1,H);
	callerLine(L1,Tail).

getStatement(L, [], _):- false.
getStatement(L, [[L,X,_]|_], X):- !.
% Man kan hämta från lådor som man inte har tillåtelse för att hämta ifrån
getStatement(L, [H|Tail],X):-
	isBox(H),
	getStatement(L,H,X).
getStatement(L, [H|Tail], X):-
	isBox(H),
	getStatement(L,Tail,X).

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
	getStatement(N,StaticProof,and(X,_)).
assertRule([_,X,andel2(N)],_,StaticProof):-
	getStatement(N,StaticProof,and(_,X)).
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
assertRule([_,or(X,_),orint1(N)],_,StaticProof):-
	getStatement(N,StaticProof,X).
assertRule([_,or(_,X),orint1(N)],_,StaticProof):-
	getStatement(N,StaticProof,X).
assertRule([_,Z,orel(N,N1,N2,M1,M2)],_,StaticProof):-
	getStatement(N,StaticProof,or(X,Y)),
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Z),
	getStatement(M1,StaticProof,Y),
	getStatement(M2,StaticProof,Z).
assertRule([_,imp(X,Y),impint(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Y).
assertRule([_,_,contel(N)],_,StaticProof):-
	getStatement(N,StaticProof,cont).
assertRule([_,neg(neg(X)),negnegint(N)],_,StaticProof):-
	getStatement(N,StaticProof,X).
assertRule([_,neg(X),mt(N,M)],_,StaticProof):-
	getStatement(N,StaticProof,imp(X,Y)),
	getStatement(M,StaticProof,neg(Y)).
assertRule([_,X,pcb(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,neg(X)),
	getStatement(N2,StaticProof,cont).