% Input returnerar sant om input är sunt
verify(Input):-
	see(Input),
	read(Prems),
	read(Goal),
	read(Proof),
	seen,
	!,
	valid_proof(Prems, Goal, Proof).

%Valider checkar beviset utifron premisserna
valid_proof(Prems, Goal, Proof):-
	iter_proof(Prems, Goal, Proof, false,Proof),
	!.
%Om beviset slutar på ett assumption
iter_proof(_,_,[[_,_,assumption]|[]],IsInBox,_):- 
	not(IsInBox),
	!, 
	false.
%När vi kommit till slutet skall statment var lika med Goal
iter_proof(Prems,Goal,[H|[]],IsInBox,StaticProof):-
	not(IsInBox),
	assertRule(H,Prems,StaticProof),
	!,
	H = [_,X,_],
	Goal = X.
%När vi nått slutet av en box (inte slutet av beviset)
iter_proof(Prems,_,[H|[]],true,StaticProof):-
	not(isBox(H)),
	!,
	assertRule(H,Prems,StaticProof).
%Validera rad och sen fortsätt
iter_proof(Prems, Goal, [ H	|Tail], IsInBox, StaticProof):-
	not(isBox(H)),
	!,
	assertRule(H,Prems,StaticProof),
	!,
	iter_proof(Prems,Goal, Tail, IsInBox, StaticProof).

%Om vi går in i en ny box
iter_proof(Prems, Goal, [H|Tail], IsInBox, StaticProof):-
	!,
	isAssumtion(H),
	iter_proof(Prems, Goal, H, true,StaticProof),
	!,
	iter_proof(Prems, Goal, Tail, IsInBox, StaticProof).

%Sant om atomen är en box
isBox([[_|_]|_]).
%Check om detta statement är ett assumption
isAssumtion([[_,_,assumption]|_]).

% Får L1 hämta info från L2
checkLines(L1,L2,StaticProof):-
	L1 > L2,
	targetLine(L1,L2,StaticProof).%Hitta L2

targetLine(_,_,[]):- !,false.
%Hittad L2 fortsätt till caller
targetLine(L1,L2,[[L2,_,_]|Tail]):-
	callerLine(L1,Tail).

%Inte L2 fortsätt leta
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

%Letar efter statement på rad L

getStatement(_, [], _):- false.
%Statement hittad då är det klart
getStatement(L, [[L,X,_]|_], X):- !.
%Om vi är på en box kolla genom boxen sen efter
getStatement(L, [H|_],X):-
	isBox(H),
	getStatement(L,H,X).
getStatement(L, [H|Tail], X):-
	isBox(H),
	getStatement(L,Tail,X).
%Ej hittad fortsätt
getStatement(Line, [_|Tail], Statement):-
	!,
	getStatement(Line,Tail, Statement).

%Kollar i fall L är start på box.

%Hittad L i början a box
startOfBox(L,[H|_]):-
	isBox(H),
	H = [[L,_,_]|_].
%Hittade box (ej rätt) titta igenom den sen efter den
startOfBox(L,[H|_]):-
	isBox(H),
	startOfBox(L,H).
startOfBox(L,[H|Tail]):-
	isBox(H),
	!,
	startOfBox(L,Tail).
%Ej hittad fortsätt
startOfBox(L,[_|Tail]):-
	!,
	startOfBox(L,Tail).

%Får L1 dra slutsatsen får boxen L2
%Har L2 endast en högre level en L1
levelDifferanceAllowed(L1,L2,StaticProof):-
	getLevel(L1,0,Level1,StaticProof),
	getLevel(L2,0,Level2,StaticProof),
	1 is Level2 - Level1.
%L hittad
getLevel(L,LevelCounter,Level,[[L,_,_]|_]):-
	Level = LevelCounter.
%Vi är i box öka level
getLevel(L,LevelCounter,Level,[H|_]):-
	isBox(H),
	getLevel(L,LevelCounter + 1, Level, H).
%Fortsätt leta efterboxen
getLevel(L,LevelCounter,Level,[H|Tail]):-
	isBox(H),
	!,
	getLevel(L,LevelCounter, Level, Tail).
%Ej hittad fortsätt
getLevel(L,LevelCounter,Level, [_|Tail]):-
	getLevel(L,LevelCounter, Level, Tail).

%Validerar varje rad

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
%DONE
assertRule([L,neg(X),negint(N1,N2)],_,StaticProof):-
	getStatement(N2,StaticProof,cont),
	getStatement(N1,StaticProof,X),
	levelDifferanceAllowed(L,N1,StaticProof).
assertRule([_,or(X,neg(X)),lem],_,_).	
assertRule([L,or(X,_),orint1(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,X).
assertRule([L,or(_,X),orint2(N)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,X).
%Done
assertRule([L,Z,orel(N,N1,N2,M1,M2)],_,StaticProof):-
	checkLines(L,N,StaticProof),
	getStatement(N,StaticProof,or(X,Y)),
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Z),
	getStatement(M1,StaticProof,Y),
	getStatement(M2,StaticProof,Z),
	levelDifferanceAllowed(L,N1,StaticProof),
	levelDifferanceAllowed(L,M1,StaticProof).
%Done
assertRule([L,imp(X,Y),impint(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,X),
	getStatement(N2,StaticProof,Y),
	levelDifferanceAllowed(L,N1,StaticProof).
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
assertRule([L,X,pbc(N1,N2)],_,StaticProof):-
	getStatement(N1,StaticProof,neg(X)),
	getStatement(N2,StaticProof,cont),
	levelDifferanceAllowed(L,N1,StaticProof).