/*
upgrade by Xue Li
*/

/*
Read ontology from a collection of fact assertions. (Expected format of the ontology.)
Ontology is the tree of the whole set of Cluases, with format Cluase;
*/
initOntoGoal(Ontology):-
	findall(Cluase,
					(fact(Cl), convertClause(Cl,Cluase)),
					Ontology). % convert all facts to internal representation
	% Find goal which is the negated axiom and then add it into goal tree as the top goal.


/*
limit recursion cost
*/
finiteCost(Cost):- Cost=<10000, !.


upgrade:- retractall(found), upgrade(0).
/*
Nf,Nt is used for sort in quicksort->q_sort->pivoting.
FullRepairs is  list of all possible completed theories with corresponding Repairs;
So every element of FullRepairs is a set of repairs for the GoalsTree.
Repairs is the list of all repairs for every subgoal.
*/
upgrade(N):-
	initOntoGoal(InitialOnt),									% Initialise ontology
	setof(	((Nf,Nt),(Repairs,UpgradedOut,N)),					% Find a set of all the repairs needed
					(
						inference(InitialOnt,InferOnt,[],PairCl,0,ActualCost,GoalsTree),		% Apply forward inference
						finiteCost(ActualCost),

						numofPro(InferOnt, N1),							% The number of positive propositions in rest clauses after inference
						length(GoalsTree, N2),							% The number of negative propositions (goals) in GoalsTree
						N1 = N2,														% Only when there are the same numbers of positive  and negative propositions, this ontology can be reformed

						repair_uncompleted(InferOnt,[],UpgradedOut,PairCl,[],Repairs,GoalsTree,[]),	% Get repairs:Repairs
						costRepairs(Repairs,RepairCost), 							% find cost
						% finiteCost(RepairCost), assert(found),								% if minimal cost, then success
						RepairCost =< N, assert(found),								% if minimal cost, then success
						length(UpgradedOut,Nt),Nf=0),
					FullRepairs),										% get all needed repairs;
	vnl, vprint('FullRepairs '),
	quicksort(FullRepairs,RepairsSorted),
	% eliminateDuplicates(RepairsSorted,SetOfRepairs),		% sort and remove duplicate repairs
	% output each repair
	findall(Clause,fact(Clause),Clauses),
	nl, print('The original theory  : '), nl, printAll(Clauses),
	printOut(RepairsSorted).

upgrade(N) :- \+(found), N1 is N+1, upgrade(N1).				% No repairs found with minimal N1 repairs -> try N1+1
upgrade(_) :- retract(found),fail.							% Keep track if a repair is found

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
/*
Input:
	OldOnt: original set of clauses.
	PairInT [(P1,P1new),(P2,P2new)...] : Original literals and their subsituted ones during resolution last time.
Output:
	PairOutT [(P1,P1new),(P2,P2new)...] : The PairOutT is a tree of pairs which are constituted by original literals and their newest substituted ones.
	RestOnt	: Rest Clauses after resolution.
	ActualCost: Cost of inference.
	GoalsTree: The tree of (goals, clause)
% new inference, add to ontology, or new inconsistency, add to Proofs of contradiction
Recursion info: when resolution failed, go back to member(Clause2,AfterOnt), if it failed again, then go back to
member(Clause1,OldOnt). If it sitll faied, then go to next definition of inference.
*/
inference(OldOnt, RestOnt, PairInT, PairOutT, OldCost, ActualCost, GoalsTree):-
	finiteCost(OldCost),														% if cost within budget
	member(Clause1, OldOnt),										% binary inference on every pair
	afterClause(Clause1, OldOnt, AfterOnt),			% make sure every pair visited only once
	member(Clause2, AfterOnt),													% If there is rest clause for recursion, then continue.
	length(Clause1, L1), enum(L1, LS1), member(I1, LS1),
	length(Clause2, L2), enum(L2, LS2), member(I2, LS2),		% every member is a literal like	[+[cap_of, [london], [britain]]]

	% If there is a goal (negated proposition), continue to resolve. Otherwise, pick next pair from	member((C2,P2),AfterOnt)
	resolution(Clause1, I1, Clause2, I2, PairInT, NewC, NewPair),			% resolve two ontology clauses by every pair of literals
	NewCost = OldCost + 1,
	subtract(OldOnt, [Clause1], Infer_ont1),							% delete resolved literals and add new one
	subtract(Infer_ont1, [Clause2], Infer_ont2),
	% restart Infer with new set of ontology
	inference([NewC|Infer_ont2], RestOnt, NewPair, PairOutT, NewCost, ActualCost, GoalsTree).	% recall with added new clause (restart from line 56)

/*
	Only when the recursion goes to the end(recurse into the last member of axiom and [])
	or when the ActualCost is beyond the limit.
	there is no more inference possible
	then ResOnt is the rest clauses of inference; GoalsTree is the final result of goals
	PairOntNew is the final rest ontology for reforming.
*/
inference(OldOnt, RestOnt, PairOntNew, PairOntNew, CurrentCost, CurrentCost, GoalsTree) :- !,
	(	finiteCost(CurrentCost),														% if cost within budget
		findGoals(OldOnt, GoalsTree),
		subtractGoals(OldOnt, RestOnt),					% delete all the goals/subgoals in ontology. So that all the positive propositions are in the RestOnt and the negated ones are in the Goalstree
		vnl,vprint('End of inference ********************')
	;
		\+finiteCost(CurrentCost),
		vnl,vprint('Infinite inference !!!!!!!!!!!!!!!!!!!!!')
	).
/*
 	1.Resolve a pair of literals: I1th term of C1 and I2th term of C2.
  2.return new pair of literals after substitution
	3.delete subgoals which has been resolved from search tree.
Input:
	C1,C2: the parent clauses of this resolution
	I1,I2: the position of two literals which are going to be resolved in C1,C2 respectively.
	PairCin: the tree of substituted propositions (sp) and their original ones (op), which has the format of [(op, sp), ...]
Output:
	NewC:	New clause after resolution which is constituted by the rest propositions of two parent clauses.
	NewPairT: New tree of sps and ops.

*/
resolution(C1, I1, C2, I2, PairCin, NewC, NewPairT):- !,
	nth1(I1, C1, L1),							% for each pair of terms (L1 is the I1th element in list C1)
	nth1(I2, C2, L2),
	oppositeSigns(L1, L2, R1, R2),				% if opposite literals

	% if successful resolution
	reform3([R1], [R2], _, SubstOut, success, success, []),

	resultingClause(C1, I1, C2, I2, RestLs),			% RestLs is the rest literals of two parent clauses after resolution
	(	\+ SubstOut = [],														% there is substitution during resolving
		subst(SubstOut, RestLs, NewC),							% Substitute rest literals
		pairPro(PairCin, RestLs, NewC, NewPairT) 		% Update new substituted literals and their original ones (This pair information is used in repair_uncompleted)
	;
		NewC = RestLs,
		NewPairT = PairCin
	).



/*
  repair uncompleted literals
Input:
	OldOnt: 		The list of all rest clauses which are not resolved (Including goals).
	UpgradedIn:	The list of repaired clauses.
	PairProT:		The tree of original clauses and substituted clauses, such as [(O1,S1),(O2,S2)....].
	RsIn:				The list of repairs which have been found.
	GoalsIn:		The Goals tree with rest goals to be repaired.
Output:
	UpgradedOut: It is repaired during repair_uncompleted based on Goals.
	RsOut:			 New set of	Repairs.
	GoalsOut:		 New Goals tree which has removed resolved goal.
*/
repair_uncompleted(OldOnt, NewOntoIn, UpgradedOut, PairProT, RsIn, RsOut, GoalsIn, GoalsOut):-
	costRepairs(RsIn, M),
	finiteCost(M),								% if cost within budget
	member((G1, ClauseGoal), GoalsIn),  % repair goal G in format like -[parent,[camilla],[bill]]
	member(Clause1, OldOnt),										% binary inference on every pair
	length(Clause1, LengthC), enum(LengthC, LS1), member(I1, LS1),
	nth1(I1, Clause1, L1),		% L1 is the I1th literal in C1.

	oppositeSigns(L1, G1, L2, G2),		% get a pair of literals
	pairwise([L2], [G2], UnificationPair),
	reform2(UnificationPair, [], _, success, _, Repair),

	% If there was substitution during step of inference, use substituted goal G2 to find repair, then reform its original Goal.
	(	member((OriginalG, G1), PairProT),						% Get Original clause according to substituted one (Clause1)
		( OriginalG = (-OG) ; OriginalG = (+OG) )
		;
		\+member((_, G1), PairProT),  % If L1 is not the result of a substitution.
		OG = G2							% if there is no substitution, then G1 is the original literal itself.
	),

	% If there was substitution during step of inference, use substituted literal L1 to find repair, then reform its original literal.
	(	member((OriLiteral, L1), PairProT),						% Get Original clause according to substituted one (Clause1)
		( OriLiteral = (-OP) ; OriLiteral = (+OP) )	% Get proposition OP of literal OriLiteral
	;
		\+member((_, L1), PairProT),  								% If L1 is not the result of a substitution, then it is the original literal.
		OP = L2																			 	% Get proposition of literal OriLiteral
	),
	pairwise([OP], [OG], OriUnifiPair),							% Pair the original propositions
	[UIn] = OriUnifiPair,

	repairs(Repair, UIn, RepairedOnt),							% repair tragets proposition (* not the whole original clause(remaining literals and resolved ones))

	NewOntology = [RepairedOnt|NewOntoIn],

	RsMid = [Repair | RsIn],
	% Update rest ontology by deleting the pair of repaired literals
	subtract(OldOnt, [Clause1], NewOnt1),							% delete Cluases which repaired literals belongs to
	subtract(Clause1, [L1], NewC1),							% get rest literals by deleting repaired literal
	append(NewOnt1, NewC1, RestOnt),							% add rest literals of the clause which resolved literal belongs to
  subtract(GoalsIn, [(G1,ClauseGoal)], GoalsTree),							% delete resolved goal from goals Tree

	repair_uncompleted(RestOnt, NewOntology, UpgradedOut, PairProT, RsMid, RsOut, GoalsTree, GoalsOut). % continue repair rest goals.


% When both RestOntlogy and Goalstree are empty, the goals are fully proved. Return UpgradedOut & Repairs.
repair_uncompleted([], UpgradedOut, UpgradedOut, _, Repairs, Repairs, [], []):- !,
	vnl,vprint('Completed Ontology').

% When Goalstree is empty, there is still rest clauses,then empty clause is failed prooved.
repair_uncompleted(RestOntlogy, UpgradedOut, UpgradedOut, _, Repairs, Repairs, [], []):- !,
	\+ RestOntlogy = [],
	vnl, vprint('******************************************** RestOntlogy=  '), vprint(RestOntlogy),
	vnl, vprint('Upgraded failed !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!').

/*
	Negated proposition is the goal;
	If input is a negeted proposition, then return true.
	Otherwise, return false.
*/
isGoal(-_):- !.		% negated proposition is the goal.
findgoal((L1, C1), (L2, C2), Goal):-
	(L1=(-_), Goal = (L1, C1) ; Goal = (L2, C2)).


addGoal(Newgoal, OldGoalTrees, OldGoalTrees):-
	 member(Newgoal, OldGoalTrees).

addGoal([], OldGoalTrees, OldGoalTrees):- !.

addGoal(Newgoal, OldGoalTrees, NewGoalTrees):-
	[(L1,_)] = Newgoal,
	isGoal(L1),
	\+ member(Newgoal, OldGoalTrees),
	append(Newgoal, OldGoalTrees, NewGoalTrees).

printOut([H|T]):-
	nl, print('------------------ Repairs as below ------------------'),
	printUpgrOnto(H), printOut(T).
printOut([]):- !.

/*
UpgrOnto is a list whose element is in format of ((Nf,Nt),(Repairs,UpgradedOutology,N))
Repairs is a set of all repairs for Goalstree.
*/
printUpgrOnto(UpgrOnto):-
	UpgrOnto = ((_, Nt), (Repairs, UpgradedOut, N)),
	findall(C, member(C, UpgradedOut), Cs),								% Get every upgraded axiom from the whole set of completed theory.
	convertForm(Cs, OntologyR),
	length(Cs, Nr), Ni is Nt-Nr,

	nl, print('Minimal cost of repairs: '), print(N),		% display minimal cost
	print('  Number of inferences: '), print(Ni),			% display heuristic
	nl, print('Repairs: '),
	nl, printAll(Repairs),
	nl, print('The Upgraded Ontology: '), nl, printAll(OntologyR).

/*
Note:
	* OldPairTree & NewPairTree are the pairs based on [(literal_original , literal_substituted),...].
	* OldClause & NewClause are based on literals, such as [+(), +(), -(), .....].
	* Use 'L' to represent for literal, 'Ls' for literals.
Input:
	Argument1: OldPairTree is ((L1original,L1),(L2original,L2)...)
	Argument2: OldLiterals [L1,L2,...]  L* is the old L which is left after resolving.
						 * OldLiterals are either the original Ls or which have been substituted before.
						 * We only store the original ones and update substituted Ls withh new substituted Ls.
	Argument3: NewLiterals	[L1new,L2new,...] L*new is the newest substituted L* after resolution.
Output:
	Argument4: NewPairTree is ((L1,L1new),(L2,L2new)...) PairOnt is constituted by original Ls and newest substituted Ls.
*/

pairPro(OldPairTree, OldLiterals, NewLiterals, PairTreeOut):-
		OldLiterals = [Hold | Told],	 % Hold is an old L (substituted one \ original one).
		NewLiterals = [Hnew | Tnew],   % Hnew is a newest L (last substituted one).

		% It is a pair of two Ls which are in the same position in OldLiterals and NewLiterals respectively.
		(	member((Hold,_), OldPairTree),
			updatePair(OldPairTree, Hold, Hnew, NewPairTree)	% If L is a substituted ones, this node should be already in the pairTree, then just update.
		;
		  \+ member((Hold,_), OldPairTree),
			addPair(OldPairTree, Hold, Hnew, NewPairTree)			% If L is an original ones, add it.
		),
		pairPro(NewPairTree, Told, Tnew, PairTreeOut).  % continue pairing next Ls.

pairPro(OldPairTree, [], [], OldPairTree):- !.

% Add new substituted P.
addPair(OldPairTree, Original, Substituted, [(Original, Substituted)| OldPairTree]):- !.
addPair(OldPairTree, [], [], OldPairTree):- !.

% Update new substituted proposition and pair it with original clause.
updatePair(OldPairTree, SubOld, SubNew, OutPairTree):-
		subtract(OldPairTree, [(Original, SubOld)], PNew),				% Delete old node and get original Literal.
		append([(Original, SubNew)], PNew, OutPairTree).		% Add newest L pair into Tree.

updatePair(OldPairTree, [], [], OldPairTree):- !.


/*
Input:
	Argument1: Clauses is [ [literal1,literal2,...], [clause2],...]
Output:
	GoalsTree: GoalsTree contains all the negative propositions of frist argument.
*/
findGoals(Clauses, GoalsTree):-
	findall((Goal,Clause),																% Format of Goal: (negated proposition, whole clause)
					(	member(Clause,Clauses),										% get a clause
						member(Goal,Clause), 														% get every literal in the Clause
						isGoal(Goal)),															% negated proposition is goal
					GoalsTree),
		vnl,vprint('GoalsTree is:'),vprintAll(GoalsTree).

findGoals([], []):- !.

/*
Note:
	* If there are three arguments, then delete all the element of GoalsTree from  OldOnt. PositiveOnt = OldOnt - goals of GoalsTree.
	* If there are only two arguments, then the second one is the output which contains all the positive propositions of frist argument.
Input:
	Argument1: OldOnt is the set of clauses which might contain both negative and positive propositions.
	Argument2: GoalsTree is the tree of goals/subgoals.
Output:
	Argument3: PositiveOnt is the set of clauses containing only the positive propositions.
*/
subtractGoals(OldOnt, GoalsTree, PositiveOnt):-
		[(Goal, Gclause)|T] = GoalsTree,
		member(Gclause, OldOnt),
		subtract(Gclause, [Goal], NewClause),
		subtract(OldOnt, [Gclause], Onto1),
		append(Onto1, NewClause, NewOnto),
		subtractGoals(NewOnto, T, PositiveOnt).

subtractGoals([], _, []):- !.
subtractGoals(OldOnt, [], OldOnt):- !.

% Only delete goals from a set of clauses
subtractGoals(Clauses, NewClauses):-
		[Clause | RestCl] = Clauses,
		% There are goals in this clause, then delete them and get the new clause consitituted by rest propositions
		findall(Goal, (member(Goal,Clause),	isGoal(Goal)), Goals),
		subtract(Clause, Goals, NewCl),
		(	\+ NewCl = [],
			append([NewCl], NewRestCl, NewClauses)
		;
			NewCl = [],
			NewRestCl = NewClauses
		),
		subtractGoals(RestCl,NewRestCl).

subtractGoals([], []):- !.


/*
Note:
	* Get the numbers of propositions in Clauses.
Input:
	Argument1: Clauses is the set of clauses which only contain positive propositions.
Output:
	Argument2: Number: The numbers of propositions in Clauses.
*/

numofPro(Clauses, Number):-
	[Clause | RestClause] = Clauses,
	length(Clause, L1),									%  The number of propositions in Clause
	numofPro(RestClause, Lrest),
	Number is L1 + Lrest.

numofPro([], 0):- !.


/*
posArg([x,arg], [a, b, [x,arg], c, [a, [x,arg]]], Pos).
Pos is [3, [5,2]].

posArg(Element, List, PosnOut):-
  % length(List, L1), enum(L1, LS1), member(I1, LS1),
  (  append(Front, [Element|RestList], List),     % Use append backwards to identify each argument Arg in turn
      length(Front, I2),
      Posi1 is I2 + 1,
      posArg(Element, RestList, Posi2),
      append(Posi1, Posi2, PosnOut)
  ; 	% find deeper element
    	findall(P3,
            (	member(EL, List),
	            is_list(EL),
	            posArg(EL, List, P1),
	            posArg(Element, EL, P2),
	            P2 =\= [],
	            append(P1, P2, P3)),   % Work out I :what position of Arg in Args is
            PosnOut)       % Recurse on each argument
  ).

posArg(Exp, Exp, [1]):- !.               % The current expression is at the empty position
posArg([Exp], [Exp], [1]):- !.           % The current expression is at the empty position
posArg([Exp], [[Exp]], [1]):- !.         % The current expression is at the empty position
posArg(_, [], []):- !.            		   % The current expression is at the empty position
*/
