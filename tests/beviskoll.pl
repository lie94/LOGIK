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
	targetLine(L1,L2,StaticProof).%Hitta L2

targetLine(_,_,[]):- !,false.
%Hittad L2 fortsätt till caller
targetLine(L1,L2,[[L2,_,_]|Tail]):-
	callerLine(L1,Tail).

%Inte l2 fortsätt leta
targetLine(L1,L2,[H|Tail]):-
	not(isBox(H)),
	!,
	targetLine(L1,L2,Tail).
%Kolla i box sen efter box
targetLine(L1,L2,[H|_]):-
	isBox(H),
	targetLine(L1,L2,H).
targetLine(L1,L2,[H|Tail]):-
	isBox(H),
	!,
	targetLine(L1,L2,Tail).

%Tom tail betyder att caller ej finns
callerLine(_,[]):- !, false.
%Hittad caller då är det sunt
callerLine(L1,[[L1,_,_]|_]).
%Ej hittad fortsätt
callerLine(L1,[H|Tail]):-
	not(isBox(H)),
	!,
	callerLine(L1,Tail).
%Ny box leta i den sen efter den
callerLine(L1,[H|_]):-
	isBox(H),
	callerLine(L1,H).
callerLine(L1,[H|Tail]):-
	isBox(H),
	!,
	callerLine(L1,Tail).

getStatement(_, [], _):- false.
getStatement(L, [[L,X,_]|_], X):- !.
% Man kan hämta från lådor som man inte har tillåtelse för att hämta ifrån
getStatement(L, [H|_],X):-
	isBox(H),
	getStatement(L,H,X).
getStatement(L, [H|Tail], X):-
	isBox(H),
	getStatement(L,Tail,X).

getStatement(Line, [_|Tail], Statement):-
	!,
	getStatement(Line,Tail, Statement).

startOfBox(_,_).
/*startOfBox(L,[[L,_,_]|_]|Tail]).
startOfBox(L,[H|Tail]):-
	isBox(H),
	!,
	startOfBox(L,Tail).
startOfBox(L,[_|Tail]):-
	startOfBox(L,Tail).*/
assertRule([_,X,premise],Prems,_):-
	member(X,Prems).
assertRule([L,_,assumption],_,StaticProof):-
	startOfBox(L,StaticProof).

assertRule([L,X,copy(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,S),
	X = S.
assertRule([L,and(X,Y),andint(N1,N2)],_,StaticProof):-
	checkLines(L,N1,StaticProof),
	checkLines(L,N2,StaticProof),
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Y).
assertRule([L,X,andel1(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,and(X,_)).
assertRule([L,X,andel2(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,and(_,X)).
assertRule([L,X,negnegel(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,neg(neg(S))),
	X = S.
assertRule([L,X,impel(N1,N2)],_,StaticProof):-
	checkLines(L,N1,StaticProof),
	checkLines(L,N2,StaticProof),
	getStatement(N1,StaticProof,S1),
	getStatement(N2,StaticProof,imp(S1,X)).
assertRule([L,cont,negel(N1,N2)],_,StaticProof):-
	checkLines(L,N1,StaticProof),
	checkLines(L,N2,StaticProof),
	getStatement(N1,StaticProof,S1),
	getStatement(N2,StaticProof,neg(S1)).
%TODO
assertRule([_,neg(X),negint(N1,N2)],_,StaticProof):-
	getStatement(N2,StaticProof,cont),
	getStatement(N1,StaticProof,X).
assertRule([_,or(X,neg(X)),lem],_,_).	
assertRule([L,or(X,_),orint1(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,X).
assertRule([L,or(_,X),orint2(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,X).
%TODO
assertRule([L,Z,orel(N,N1,N2,M1,M2)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,or(X,Y)),
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Z),
	getStatement(M1,StaticProof,Y),
	getStatement(M2,StaticProof,Z).
%TODO
assertRule([_,imp(X,Y),impint(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Y).
assertRule([L,_,contel(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,cont).
assertRule([L,neg(neg(X)),negnegint(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,X).
assertRule([L,neg(X),mt(N,M)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	checkLines(L,M,StaticProof),
	getStatement(N,StaticProof,imp(X,Y)),
	getStatement(M,StaticProof,neg(Y)).
%TODO
assertRule([_,X,pbc(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,neg(X)),
	getStatement(N2,StaticProof,cont).