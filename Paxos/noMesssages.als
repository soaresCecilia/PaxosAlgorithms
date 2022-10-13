/***************PAXOS without Messages******************/

//Paxos without Messages

/***************MODULES*******************/

open util/ordering[Ballot]

/***************SIGNATURES*******************/
sig Value {}

sig Ballot {}

sig Acceptor {
	var maxBal : lone Ballot,
	var maxVote: lone Vote,
	var sent : Type -> Ballot -> Payload
}

sig Quorum {
	acceptors : some Acceptor
}

one sig None {}

abstract sig Type {}
one sig M1A,M1B,M2A,M2B extends Type {}

abstract sig Vote {
	value : Value,
	ballot : Ballot
}

sig Payload = Value + Vote + None {}

/********************************FACTS*****************************/
fact AllPossibleVotesExist {
	all v : Value, b : Ballot | some x : Vote | x.value = v and x.ballot = b
}

fact Quorums {
	all x,y : Quorum | some x.acceptors & y.acceptors
	all a: Acceptor | some q: Quorum | a in q.acceptors 
}

//Initial State
fact Init {
	no maxBal
	no maxVote
	no sent 
}

//Next-state actions
fact Next {
	always (nop or
		some b: Ballot | phase1A[b] or
		some a: Acceptor | phase1B[a] or phase2B[a] or
		some v: Value | phase2A[b, v]
	)
}

// PHASE 1 - Prepare 

pred phase1A[b: Ballot] {
	no Acceptor.sent[M1A][b]
	some a : Acceptor | sent' = sent + a->M1A->b->None
	maxBal' = maxBal
	maxVote' = maxVote
}

pred phase1B[a: Acceptor] {
	some b: Acceptor.sent[M1A].None {
		no a.maxBal or gt[b, a.maxBal]
		no a.maxVote implies {
			sent' = sent + (a->M1B->b->None)
		}
		else {
			sent' = sent + (a->M1B->b->(a.maxVote))
		}
		maxBal' = maxBal ++ a->b
		maxVote' = maxVote
	}			
}


// PHASE 2 - Accept

/*All acceptors from a quorum have sent one M1B
and no one had voted in any previous ballot 
*/ 
pred safeNoVote[q: Quorum, b: Ballot] {
	(q.acceptors).sent[M1B][b] = None
}

/*All acceptors from a quorum have sent one M1B
and it's necessary to find the highest-number ballot less than b
that was voted. 
*/
pred safeVotedValue[q: Quorum, b: Ballot, v: Value] {	
	some mb : ((q.acceptors).sent[M1B][b] & value.v).ballot {
		all ob : ((q.acceptors).sent[M1B][b]).ballot | gte[mb,ob]
	}
}

pred phase2A[b: Ballot, v: Value] {
	no Acceptor.sent[M2A][b]
	some q: Quorum {
			all a: q.acceptors | some a.sent[M1B][b]
			safeNoVote[q, b] or safeVotedValue[q, b, v]
	}
	some a : Acceptor | sent' = sent + a->M2A->b->v
	maxVote' = maxVote
	maxBal' = maxBal
}

//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some b : Ballot, x : Acceptor.sent[M2A][b], v : Vote {
		no a.sent[M2B][b]
		no a.maxBal or gte[b, a.maxBal]
		v.ballot = b and v.value = x
		maxBal' = maxBal ++ a->b
		maxVote' = maxVote ++ a->v
		sent' = sent + a->M2B->b->x
	}
}

//System stuttering
pred nop {
	maxBal' = maxBal
	maxVote' = maxVote
	sent' = sent
}

run scenario1 {
    eventually some chosenValues
} for 3 Value, 3 Quorum, 3 Acceptor, 
    3 Ballot, exactly 9 Vote, 9..9 steps expect 1

run scenario2 {
	some disjoint a1, a2: Acceptor, b1: Ballot, v: Value {
		some q: Quorum | a1 + a2 in q.acceptors
		phase1A[b1]; 
		phase1B[a1];
		phase1B[a2];
		phase2A[b1, v];
		phase2B[a2];
		phase2B[a1]
	}
} for 2 Value, 1 Quorum, 2 Acceptor, 2 Ballot, 4 Vote, 7..7 steps expect 1

run scenario3 {
	some disjoint a1, a2, a3: Acceptor, disjoint b1, b2: Ballot, v: Value,
		disjoint q1, q2: Quorum {
		a1 + a2 in q1.acceptors and 
		a2 + a3 in q2.acceptors
		phase1A[b1]; 
		phase1B[a1];
		phase1B[a2];
		phase2A[b1, v];
		phase2B[a2];
		phase2B[a1];
		phase1A[b2];
		phase1B[a3];
		phase1B[a2];
		phase2A[b2, v];
		phase2B[a2];
		phase2B[a3]
	}  
} for exactly 2 Value, exactly 2 Quorum, exactly 3 Acceptor, 
	exactly 2 Ballot, exactly 4 Vote, 13..13 steps expect 1

run scenario4 {
	some disjoint a1, a2, a3: Acceptor, disjoint b1, b2: Ballot,
		disjoint v1, v2: Value, disjoint q1, q2: Quorum { 
		a1 + a2 in q1.acceptors and a2 + a3 in q2.acceptors
		phase1A[b1]; 
		phase1B[a1];
		phase1B[a2];
		phase2A[b1, v1];
		phase2B[a1];
		phase1A[b2];
		phase1B[a2];
		phase1B[a3];
		phase2A[b2, v2];
		phase2B[a2];
		phase2B[a3]
	}  
} for exactly 2 Value, 2 Quorum, exactly 3 Acceptor, exactly 2 Ballot, 
	exactly 4 Vote, 12..12 steps expect 1

run scenario5 {
	eventually some a1: Acceptor, 
		disjoint b1, b2: Ballot {
		gt[b2, b1]
		a1.maxBal = b2
		phase1A[b1];
		phase1B[a1]
	}  
} for exactly 1 Value, 2 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, exactly 2 Vote, 10..10 steps expect 0

/*
An acceptor can receive and respond to a M2A without having
previously respond to a M1A with the same ballot
*/
run scenario6 {
	some disjoint q1, q2: Quorum, disjoint a1, a2, a3: Acceptor, 
		b1: Ballot, v: Value {
		once {
		a1 + a2 in q1.acceptors and a3 + a1 in q2.acceptors
		phase1A[b1];
		phase1B[a1];
		phase1B[a2];
		phase2A[b1, v];
		phase2B[a3];
		phase2B[a1]
		}
	}  
} for exactly 1 Value, 2 Quorum, exactly 3 Acceptor, 
		exactly 2 Ballot, exactly 2 Vote, 8..8 steps expect 1

//Two messages with same ballot can't propose different values
run scenario7 {
	some b: Ballot, disjoint v1, v2: Value{
		eventually phase2A[b, v1] once phase2A[b, v2]
	} 
} for exactly 2 Value, 2 Quorum, exactly 3 Acceptor, 
	exactly 2 Ballot, exactly 4 Vote, 12..12 steps expect 0

//no repeated M2A
run scenario8 {
	some b: Ballot, disjoint v: Value{
		eventually phase2A[b, v] once phase2A[b, v]
	}
} for exactly 1 Value, 1 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, exactly 2 Vote, 6..6 steps expect 0

run scenario9 {
	some disjoint a1, a2: Acceptor, disjoint b1, b2: Ballot, 
		v: Value, q: Quorum { 
		a1 + a2 in q.acceptors
		phase1A[b1]; 
		phase1B[a1];
		phase1B[a2];
		phase2A[b1, v];
		phase2B[a1];
		phase1A[b2];
		phase1B[a1];
		phase1B[a2];
		phase2A[b2, v];
		phase2B[a1];
		phase2B[a2]
	}  
} for exactly 2 Value, 1 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, exactly 4 Vote, 12..12 steps expect 1

/*********************************************/
//SAFETY


//An acceptor a has voted in v in ballot b
pred votedFor[a: Acceptor, b: Ballot, v: Value] {
	v in a.sent[M2B][b]
}

//All acceptors from some quorum have voted for v in ballot b.
pred chosenAt[b: Ballot, v: Value] {
	some q: Quorum | all a: q.acceptors | votedFor[a, b, v]
}

//Choosing at most one value
fun chosenValues : set Value {
	{v: Value | some b: Ballot | chosenAt[b, v]}
}

assert ChosenValue {
	always lone chosenValues
}   

check ChosenValue for 0 Int, exactly 2 Value, 2 Quorum, 
	exactly 3 Acceptor, exactly 2 Ballot, 
	exactly 2 Vote, 9..9 steps

pred didNotVoteAt[a: Acceptor, b: Ballot] {
	all v: Value | not votedFor[a, b, v]
}

//An acceptor a cannot cast any more votes in a ballot < a.maxBal
pred cannotVoteAt[a: Acceptor, b: Ballot] {
	some a.maxBal and gt[a.maxBal, b] and didNotVoteAt[a, b]
}

//An acceptor a has already voted in b->v or he will never cast a vote in ballot b
pred noneOtherChoosableAt[b: Ballot, v: Value] {
	some q: Quorum | all a: q.acceptors | votedFor[a, b, v] or cannotVoteAt[a, b]
}

/* No other value than v has been or can ever be chosen in any
ballot less than b  
*/
pred safeAt[b: Ballot, v: Value] {
	all c: prevs[b] | noneOtherChoosableAt[c, v]
}
assert VotesSafe {
	always (all a : Acceptor, b : Ballot, v : Value | 
		always (votedFor[a, b, v] implies safeAt[b, v]))
}

check VotesSafe for 0 Int, exactly 3 Value, 3 Quorum, exactly 3 Acceptor, 
	exactly 3 Ballot, exactly 9 Vote, 20..20 steps

//Only one vote per Ballot (the value is always the same at the ballot x)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] and votedFor[a2, b, v2]) 
							implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for 0 Int, 3 Value, 3 Quorum, 3 Acceptor, 
	3 Ballot, 9 Vote, 20..20 steps



/****************************THEME********************************/

enum Event {Nop, Phase1A, Phase1B, Phase2A, Phase2B} // event names

/*auxiliary relation, which should be populated 
when the nop event happens
a subset of Event that will be populated 
(by the name Stutter) if the stutter predicate 
is true, and empty otherwise.*/
fun nop_happens : set Event {
  { e: Nop | nop }
}

fun phase1A_happens : Event -> Ballot {
  { e: Phase1A, b: Ballot | phase1A[b] }
}

fun phase1B_happens : Event -> Acceptor {
  { e: Phase1B, a: Acceptor | phase1B[a] }
}

fun phase2A_happens : Event -> Ballot -> Value {
  { e: Phase2A, b: Ballot, v: Value | phase2A[b, v] }
}

fun phase2B_happens : Event -> Acceptor {
  { e: Phase2B, a: Acceptor | phase2B[a] }
}

/*Enhancement to show event parameters as labels.*/
fun events : set Event {
	nop_happens + 
	phase1A_happens.Ballot + 
	phase1B_happens.Acceptor + 
	phase2B_happens.Acceptor + 
	phase2A_happens.Value.Ballot
}

//The Ballot that was voted for a quorum
fun oneBallotChosen : one Ballot {
	{b: Ballot | some v: Value | chosenAt[b,v]}
}

//The value chosen
fun chosen: Ballot -> Value {
	{b: Ballot, v: Value | some q: Quorum | all a: q.acceptors | votedFor[a, b, v]}
}

//Verification of theme
fact trace {
  always some events
}

check singleEvent {
  always one events
} for 1..20 steps



