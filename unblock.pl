/*
Unblock by Xue Li
*/

/*
initPair : Translate into internal representation and pairs up corresponding elements of two lists
output: NE, a list  of unify iterms [[F|Args]=[F2,Args2]]
*/
initPair(NE):-
	findall(Cl,fact(Cl),Ontology),          % convert each fact to internal representation
	member(C1,Ontology),										% binary inference on every pair
	afterClause(C1,Ontology,AfterOnt),						% make sure every pair visited only once
	member(C2,AfterOnt),
  maplist(convert, C1, NE1S),          % convert Fact1 into internal representation NE1S
  maplist(convert, C2, NE2S),          % convert Fact2 into internal representation NE2S
  pairwise(NE1S,NE2S,NE).                 % Unify each pair of items in a list NE

unblock:- retractall(found), unblock(0).

unblock(N):-
  initPair(NE),			% NE:		[[F|Args]=[F2,Args2]]
  [UIn]= NE,				% UIn: 	[F|Args]=[F2,Args2]
	setof(	((Nf,Nt),(Repairs,[Unblockeds],N)),					% Find a set of all the repairs needed
					(
						% get repaired theory Rout:[parent,vble(x),vble(y)]=[parent,[camilla],[bill]]
						reform2(NE,[],_,success,_,Repairs),
						repairs(Repairs,UIn,Unblockeds),		% Apply forward inference
						costRepairs(Repairs,M), 							% find cost
						M =< N, assert(found),								% if minimal cost, then success
						length([Unblockeds],Nt),Nf=0),
					FullRepairs),														% get all needed repairs

	quicksort(FullRepairs,RepairsSorted),
	eliminateDuplicates(RepairsSorted,SetOfRepairs),		% sort and remove duplicate repairs

	% output each repair
	member(RepairSorted,SetOfRepairs),						% ** unify every sigle repair in the list of repairs (SetOfRepairs) to RepairSorrted
	RepairSorted = ((Nf,Nt),(Repairs,Unblocked,N)), % **?
	findall(C,member(C,Unblocked),Cs),
	length(Cs,Nr), Ni is Nt-Nr,
	convertForm(Cs, Ontology),

	% print screen the repaired theory
  nl, print('Minimal cost of repairs: '),print(N),		% display minimal cost
	print('  Number of inferences: '), print(Ni),			% display heuristic
	nl, print('Repairs: '),nl,
	print(Repairs),nl,nl,
	print('Repaired Ontology: '),nl,
	printAll(Ontology).

	unblock(N) :- \+(found), N1 is N+1, unblock(N1).				% No repairs found with minimal N1 repairs -> try N1+1
	unblock(_) :- retract(found),fail.							% Keep track if a repair is found

/*
convertForm : convert the form of Cs into the original form of ontology
Input [C1=C2]:[[F,Args]=[F2,Args2]]
Output Ontology: [F(Args),F2(Args2)]
*/
	convertForm([C1=C2], Ontology):-
		Clause1=..C1,
		Clause2=..C2,
		Ontology = [[Clause1],[Clause2]].
