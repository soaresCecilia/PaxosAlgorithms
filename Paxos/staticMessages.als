/***************PAXOS with Message Box******************/
//Paxos with MsgBox

/******************MODULE*********************/

open util/ordering[Ballot]

/******************SIGNATURES*********************/
sig Acceptor {
	var maxBal : lone Ballot,
	var maxVal: lone Value, 
	var maxVBal: lone Ballot
}

sig Quorum {
	acceptors : some Acceptor
}

sig Value {}

sig Ballot {}

//Messages that will be exchanged
abstract sig Message {
	bal: one Ballot
}

var sig MsgBox in Message{}

//Different types of messages
sig M1A extends Message{}

sig M1B extends Message{
	acceptor: one Acceptor,
	mbal: lone Ballot,
	mval: lone Value
}

sig M2A extends Message{
	value: one Value,
}

sig M2B extends Message {
	acceptor: one Acceptor,
	value: one Value,
}

fact Quorums {
	all x,y : Quorum | some x.acceptors & y.acceptors
	all a: Acceptor | some q: Quorum | a in q.acceptors 
}

//Initial State
fact Init {
	no maxBal
	no maxVal
	no maxVBal
	no MsgBox
}

//Next-state actions
fact Next {
	always (nop or
		some b: Ballot | phase1A[b] or
		some a: Acceptor | phase1B[a] or phase2B[a] or
		some v: Value | phase2A[b, v]
	)
}

//Sending a message
pred send[m : Message] {
	MsgBox' = MsgBox + m
}

// PHASE 1 - Prepare 
pred phase1A[b: Ballot] {
	no m1a: (M1A & MsgBox) | m1a.bal = b

	some m1a: M1A | m1a.bal = b and send[m1a]
	maxBal' = maxBal
	maxVal' = maxVal
	maxVBal' = maxVBal
}

pred phase1B[a: Acceptor] {
	some m1a: M1A & MsgBox { 
		no a.maxBal or gt[m1a.bal, a.maxBal] 
		
		some m1b: M1B {
			m1b.bal = m1a.bal
			m1b.acceptor = a
			m1b.mbal = a.maxVBal
			m1b.mval = a.maxVal
			send[m1b]
		}

		maxBal' = maxBal ++ a->(m1a.bal)
		maxVal' = maxVal
		maxVBal' = maxVBal
	}			
}


// PHASE 2 - Accept


/*All acceptors from a quorum have sent one M1B
and no one had voted in any previous ballot 
*/
pred safeNoVote[q: Quorum, b: Ballot] {
 	all a: q.acceptors {
		some m1b: M1B & MsgBox {
			m1b.acceptor = a
			m1b.bal = b
			no m1b.mbal
		}
		all m1b: M1B & MsgBox | (m1b.acceptor = a and m1b.bal = b) 
			implies no m1b.mbal
	}
}

/*All acceptors from a quorum have sent one M1B
and it's necessary to find the highest-number ballot less than b
that was voted. 
*/
pred safeVotedValue[q: Quorum, b: Ballot, v: Value] {	
	all a: q.acceptors | some m1b: M1B & MsgBox {
		m1b.acceptor = a
		m1b.bal = b
	}

	some n : M1B & MsgBox {
		n.bal = b
		n.acceptor in q.acceptors 
		n.mval = v 
		all m1b: M1B & MsgBox { 
			(m1b.bal = b and m1b.acceptor in q.acceptors) implies {
						gte[n.mbal, m1b.mbal] or no m1b.mbal
			}
		}
	}
}

pred phase2A[b: Ballot, v: Value] {
	no m2a: (M2A & MsgBox) | m2a.bal = b
	
	some q: Quorum | safeNoVote[q, b] or safeVotedValue[q, b, v]

	some m2a: M2A {
		m2a.bal = b
	 	m2a.value = v
		send[m2a]
	}

	maxVal' = maxVal
	maxVBal' = maxVBal
	maxBal' = maxBal
}


//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some m2a: M2A & MsgBox {
		no m2b: (M2B & MsgBox) | (m2b.bal = m2a.bal and m2b.acceptor = a)

		no a.maxBal or gte[m2a.bal, a.maxBal]
		maxBal' = maxBal ++ a->(m2a.bal)
		maxVal' = maxVal ++ a->(m2a.value)
		maxVBal' =  maxVBal ++ a->(m2a.bal)
		
		some m2b: M2B {
			m2b.bal = m2a.bal
			m2b.value = m2a.value 
			m2b.acceptor = a
			send[m2b]
		}
	}
}

//System stuttering
pred nop {
	maxBal' = maxBal
	maxVal' = maxVal
	maxVBal' = maxVBal
	MsgBox' = MsgBox
}


/**********************RUNS**************/

run scenario1 {
    eventually some chosenValues
} for 3 Value, 3 Quorum, 3 Acceptor, 
    3 Ballot, 8 Message, 9..9 steps expect 1


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
} for 2 Value, 1 Quorum, 2 Acceptor, 2 Ballot, 
	6 Message, 7..7 steps expect 1

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
} for exactly 1 Value, exactly 2 Quorum, exactly 3 Acceptor, 
	exactly 2 Ballot, 12 Message, 13..13 steps expect 1

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
} for exactly 2 Value, 2 Quorum, exactly 3 Acceptor, 
exactly 2 Ballot, 11 Message, 12..12 steps expect 1

/*Acceptor can't send M1B because ballot b1 sent in M1A
is smaller than his maxBal 
*/
run scenario5 {
	eventually some a1: Acceptor, 
		disjoint b1, b2: Ballot {
		gt[b2, b1]
		a1.maxBal = b2
		phase1A[b1];
		phase1B[a1]
	}  
} for exactly 1 Value, 2 Quorum, 2 Acceptor, 
exactly 2 Ballot, 9 Message, 10..10 steps expect 0

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
} for exactly 1 Value, exactly 2 Quorum, exactly 3 Acceptor, 
	exactly 1 Ballot, 6 Message, 7..7 steps expect 1

//Two messages with same ballot can't propose different values
run scenario7 {
	some b: Ballot, disjoint v1, v2: Value{
		eventually phase2A[b, v1] once phase2A[b, v2]
	}
} for exactly 2 Value, 2 Quorum, 2 Acceptor,
 exactly 1 Ballot, 9 Message, 10..10 steps expect 0

//no repeated M2A
run scenario8 {
	some b: Ballot, disjoint v: Value{
		eventually phase2A[b, v] once phase2A[b, v]
	} 
} for exactly 1 Value, 2 Quorum, exactly 2 Acceptor, 
exactly 2 Ballot, 9 Message, 10..10 steps expect 0


//consensuas achieved only in second rond
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
} for exactly 1 Value, 1 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, 11 Message, 12..12 steps expect 1


/********************CHECKS*************************/
//SAFETY


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

check ChosenValue for exactly 2 Value, 2 Quorum, 
	exactly 3 Acceptor, exactly 2 Ballot, 
	8 Message, 9..9 steps expect 0


//An acceptor a has voted in v in ballot b
pred votedFor[a: Acceptor, b: Ballot, v: Value] {
	some m2b: M2B & MsgBox {
		m2b.acceptor = a
		m2b.bal = b 
		m2b.value = v
	}
}

pred didNotVoteAt[a: Acceptor, b: Ballot] {
	all v: Value | not votedFor[a, b, v]
}

//An acceptor a can't cast any more votes in a ballot less than a.maxBal
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

check VotesSafe for 17..17 steps, exactly 3 Value, 
	exactly 3 Quorum, exactly 3 Acceptor,
	 exactly 3 Ballot, 12 Message expect 0

//Only one vote per Ballot (the value is always the same at the ballot b)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] and votedFor[a2, b, v2]) 
							implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for exactly 2 Value, exactly 1 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, 11 Message, 12..12 steps expect 0



/*************************THEME***********************************/
enum Event {Nop, Phase1A, Phase1B, Phase2A, Phase2B}

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

//Enhancement to show event parameters as labels.
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

//The set of acceptors that already has voted
fun voters: set Acceptor {
	{a: Acceptor | some b: Ballot , v: Value | a.maxVal = v and a.maxVBal = b}
}


//Verification of theme
fact trace {
	always some events
}

check singleEvent {
	always one events
} for 1..20 steps


