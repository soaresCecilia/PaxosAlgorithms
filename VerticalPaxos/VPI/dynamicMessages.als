/****************VERTICAL PAXOS I - DYNAMIC MSGS*********/

/****************MODULES****************************/

open util/ordering[Ballot]

/****************SIGNATURES****************************/

sig Acceptor {
	var maxBal : lone Ballot,
	var votes: Ballot -> lone Value
}

var sig RcvdNewBal in Leader {} 

sig Leader {
	var safeVal: lone Value,
	var previousBal: lone Ballot, 
	var lCompleteBal: lone Ballot,
	var allPreviousBal: set Ballot,
	id: one Ballot 
}

one sig Master {
	var mCompleteBal: lone Ballot,
	var nextBal: one Ballot
}

sig Value {}

sig Ballot {}

//Each quorum is related to a round
abstract sig Quorum {
	ballot: one Ballot,
	acceptors : some Acceptor
}

//Write Quorum
sig WQuorum extends Quorum {}

//Read Quorum
sig RQuorum extends Quorum {}

var abstract sig BasicMessage {}

//Messages that will be exchanged
var abstract sig ServerMessage extends BasicMessage  {
	var bal: one Ballot
}{
	bal = bal'
}

/*
Client messages are a new type of messages
because they do not have ballot, only one value 
*/
var sig MsgClient extends BasicMessage {
	var value: one Value
}{
	value = value'
}

//Different types of messages
var sig MsgNewBallot extends ServerMessage {
	var completeBal: lone Ballot
}{
	completeBal = completeBal'
}

var sig M1A extends ServerMessage {
	var prevBal: lone Ballot
}{
	prevBal = prevBal'
}

var sig M1B extends ServerMessage {
	var acceptor: one Acceptor,
	var mbal: lone Ballot,
	var mval: lone Value 
}{
	acceptor = acceptor'
	mbal = mbal'
	mval = mval'
}

var sig M2A extends ServerMessage {
	var value: one Value, 
}{
	value = value'
}

var sig M2B extends ServerMessage {
	var acceptor: one Acceptor,
	var value: one Value
}{
	value = value'
	acceptor = acceptor'
}

var sig MsgComplete extends ServerMessage{}


/****************FACTS****************************/

fact Quorum {
	all b: Ballot {
		all wq: WQuorum, rq: RQuorum | (wq.ballot = b and rq.ballot = b) implies
					some (wq.acceptors & rq.acceptors)
		one wq: WQuorum |  wq.ballot = b
		some rq: RQuorum | rq.ballot = b
	}
	all rq: RQuorum | one rq.acceptors
	all a: Acceptor | some q: Quorum | a in q.acceptors
}

fact SetBallotLeader {
	all disjoint l1, l2: Leader | no l1.id & l2.id
	all l : Leader | no b : Ballot | lt[b,l.id] and no id.b  
}

//Initial State
fact Init {
	no maxBal
	no votes
	no safeVal
	no previousBal
	no lCompleteBal
	no mCompleteBal
	Master.nextBal = first
	no BasicMessage
	no allPreviousBal
	no RcvdNewBal
}

//Next-state actions - All possible actions
fact Next {
	always (nop or
		some m: Master | newReconfig[m] or
		completeReconfig[m] or
		some a: Acceptor | phase1B[a] or 
		phase2B[a] or
		some l: Leader | leaderRcvdNewReconfig[l] or
		phase1A[l] or
		allValuesSafeOrOneValueSafe[l] or 
		allValuesSafe[l] or 
		stateTransferCompleted[l] or
		oneValueSafe[l] or 
		some v: Value | clientRequest[v]
	)
}

/****************PREDICATES****************************/

//Sending a message
pred send[m : BasicMessage] {
	BasicMessage' = BasicMessage + m
}

//System stuttering
pred nop {
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	previousBal' = previousBal
	lCompleteBal' = lCompleteBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	BasicMessage' = BasicMessage
}

/**************MASTER***********/

//Master starts a new reconfiguration 
pred newReconfig[m: Master] {
	some msgNew: MsgNewBallot' { 
		msgNew.bal' = m.nextBal
		msgNew.completeBal' = m.mCompleteBal
		send[msgNew]
	}
	nextBal' = next[nextBal]
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	lCompleteBal' = lCompleteBal
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
}

//Reconfiguration is completed when Master receives MsgComplete.
pred completeReconfig[m: Master] {
	some msgComplete : MsgComplete {
		no m.mCompleteBal or gt[msgComplete.bal, m.mCompleteBal]
		mCompleteBal' = mCompleteBal ++ (m->msgComplete.bal)
	}
	maxBal' = maxBal
	votes' = votes
	safeVal' = safeVal
	lCompleteBal' = lCompleteBal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' =  RcvdNewBal
	nextBal' = nextBal
	BasicMessage' = BasicMessage
}

/********************ACCEPTORS *****************/

/* All acceptors from previous views must inform the leader 
which value each one has voted  */
pred phase1B[a: Acceptor] {
	some m1a: M1A {
		no a.maxBal or gt[m1a.bal, a.maxBal] 	
		some m1b: M1B' {
			m1b.bal' = m1a.bal
			m1b.mbal' = m1a.prevBal
			m1b.mval' = a.votes[m1a.prevBal]
			m1b.acceptor' = a
			send[m1b]
		}
		maxBal' = maxBal ++ a->(m1a.bal)
	}	
	votes' = votes
	safeVal' = safeVal
	previousBal' = previousBal
	lCompleteBal' = lCompleteBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal	
}

//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some m: M2A {
		no a.maxBal or gte[m.bal, a.maxBal]
		no m2b: M2B | m2b.bal = m.bal and m2b.acceptor = a
		
		maxBal' = maxBal ++ a->(m.bal)	
		votes' = votes + (a->(m.bal)->(m.value))

		some m2b: M2B' {
			m2b.bal' = m.bal
			m2b.value' = m.value 
			m2b.acceptor' = a
			send[m2b]
		}
	}
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	lCompleteBal' = lCompleteBal
	RcvdNewBal' = RcvdNewBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}


/*******************CLIENT***********/

//Client sends a message
pred clientRequest[v: Value] {
	no m: MsgClient | m.value = v
	some m: MsgClient' {
		m.value' = v
		send[m]
	}
	
	maxBal' = maxBal
	votes' = votes
	nextBal' = nextBal
	mCompleteBal' = mCompleteBal
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
}

/********************LEADER*************************/

//Leader receives NewBallot Message
pred leaderRcvdNewReconfig[l: Leader] {
	some msgNewBallot: MsgNewBallot {
		msgNewBallot.bal = l.id
		lCompleteBal' = lCompleteBal ++ ( l->msgNewBallot.completeBal)
		previousBal' = previousBal ++ (l->prev[msgNewBallot.bal])	
		let allpB = { b: Ballot | (no msgNewBallot.completeBal or gte[b, msgNewBallot.completeBal])
				 and lt[b, l.id]}{
			allPreviousBal' = allPreviousBal ++ (l ->(allpB))
		}
	}
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	RcvdNewBal' = RcvdNewBal + l
	BasicMessage' = BasicMessage
}

pred phase1A[l: Leader] {
	l in RcvdNewBal
	no l.safeVal and (some l.previousBal and 
                                                            (no l.lCompleteBal or 
                                                            (some l.lCompleteBal and gte[l.previousBal, l.lCompleteBal])))
	no m1a: M1A | m1a.bal = l.id and m1a.prevBal = l.previousBal
	
	// Phase 1A
	some m1a: M1A' {
		m1a.bal'= l.id
		m1a.prevBal' = l.previousBal
		send[m1a]
	}
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	previousBal' = previousBal ++ (l->prev[l.previousBal])
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
}

/* This predicate offers alternative paths.*/
pred allValuesSafeOrOneValueSafe[l: Leader] {
	l in RcvdNewBal	
	no l.safeVal and no msgComp: MsgComplete | msgComp.bal = l.id 
	noPreviousValueChosen[l] implies {
		sendComplete[l]
	}
 	else {
		someOneVoted[l]
	}
}

/*All acceptors from a read quorum of some previous view had sent a M1B
and no one from that quorum voted.
For all previousBal there is some read quorum that has not voted.
It's only necessary to verify one read quorum of each previous round because 
we write for all elements.
 */
pred noPreviousValueChosen[l: Leader] {
	all b: l.allPreviousBal {
		some rq: RQuorum {
			rq.ballot = b
			some m1b: M1B {
				m1b.acceptor = rq.acceptors
				m1b.bal = l.id
				m1b.mbal = b
				no m1b.mval
			}
		}
	}
}

/* Some acceptors from one of readQuorums of previous round 
has voted in some value. Therefore, is stored in safeVal because
our model garantees that every read quorum has only a single acceptor
*/
pred someOneVoted[l: Leader] {	
	some b: l.allPreviousBal | some rq: RQuorum  {
		rq.ballot = b
		some m1b: M1B {
			m1b.acceptor = rq.acceptors
			m1b.bal = l.id
			m1b.mbal = b
			some m1b.mval
			
			safeVal' = safeVal ++ (l->m1b.mval)
		}
	}
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	BasicMessage' = BasicMessage
}

// Some safeVal implies sending M2A before completing reconfiguration
pred oneValueSafe[l: Leader] {
	some l.safeVal
	no m2a: M2A | m2a.bal = l.id
 
	some m2a: M2A' {
		m2a.bal' = l.id
	 	m2a.value' = l.safeVal
		send[m2a]
	}
	maxBal' = maxBal
	votes' = votes
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal	
}

// All quorum members from a current write quorum have sent a M2B
pred stateTransferCompleted[l: Leader] {
	some l.safeVal and no msgComp: MsgComplete | msgComp.bal = l.id
	some wq: WQuorum {
		wq.ballot = l.id
		all a: wq.acceptors {
			some m2b: M2B {
				m2b.bal = l.id
				m2b.acceptor = a
			}
		}	
	}
	sendComplete[l]
}

//Leader sends a complete reconfiguration message
pred sendComplete[l: Leader] {

	some msgComplete: MsgComplete' {
		msgComplete.bal' = l.id		
		send[msgComplete]
	}
	maxBal' = maxBal
	votes' = votes 
	safeVal' = safeVal
	lCompleteBal' = lCompleteBal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	nextBal' = nextBal
	mCompleteBal' = mCompleteBal
}


//Sending M2A when no one has voted
pred allValuesSafe[l: Leader]{
	no l.safeVal
	
	some m: MsgComplete {
		m.bal = l.id 	
		no m2a: M2A | m2a.bal = l.id
		some mClient: MsgClient {
			some m2a: M2A' {
				m2a.bal' = l.id
				m2a.value' = mClient.value
				send[m2a]
			}
		}
	}	
	maxBal' = maxBal
	votes' = votes
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	lCompleteBal' = lCompleteBal
	RcvdNewBal' = RcvdNewBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

/*************************RUNS*************************/

//Remind that we need one more ballot than leaders to have progress because
//of master's nexBallot

//One value was chosen in previous round
run scenario1 {
	some m: Master, disjoint l1, l2: Leader, 
		disjoint a1, a2: Acceptor, v: Value {
			newReconfig[m]; 
			leaderRcvdNewReconfig[l1]; 
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			clientRequest[v]; 
			allValuesSafe[l1]; 
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			leaderRcvdNewReconfig[l2]; 
			phase1A[l2]; 
			phase1B[a1]; 
			allValuesSafeOrOneValueSafe[l2]; 
			oneValueSafe[l2]; 
			phase2B[a1]; 
			phase2B[a2]; 
			stateTransferCompleted[l2]; 
			completeReconfig[m]
	}
} for exactly 10 Quorum, exactly 2 Leader, exactly 2 Acceptor,
 exactly 2 Value, 3 Ballot, 18 BasicMessage, 19..19 steps expect 1

//No previous active configuration
run scenario2{
    some m: Master, l1: Leader, 
        disjoint a1, a2: Acceptor, v: Value {
            	newReconfig[m]; 
		clientRequest[v]; 
		leaderRcvdNewReconfig[l1]; 
		allValuesSafeOrOneValueSafe[l1]; 
            	completeReconfig[m]; 
		allValuesSafe[l1];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 6 Quorum, exactly 1 Leader, 
    exactly 2 Acceptor, exactly 2 Ballot, exactly 1 Value, 
    8 BasicMessage, 9..9 steps expect 1


run scenario3{
    some m: Master, disjoint l1, l2: Leader, 
        disjoint a1, a2: Acceptor, v: Value {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1]; 
		allValuesSafeOrOneValueSafe[l1]; 
            	completeReconfig[m]; 
		clientRequest[v]; 
		newReconfig[m]; 
            	leaderRcvdNewReconfig[l2]; 
		phase1A[l2]; 
		phase1B[a1];
            	allValuesSafeOrOneValueSafe[l2]; 
		completeReconfig[m];
		allValuesSafe[l2];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    14 BasicMessage, 15..15 steps expect 1

run scenario4{
     eventually some m: Master, disjoint l1, l2: Leader,
	disjoint a1, a2: Acceptor, disjoint v1, v2: Value, 
	disjoint b1, b2, b3: Ballot {
		gt[b3, b2] and gt[b2, b1] and l1.id = b1 and l2.id = b2
		a1 + a2 in WQuorum.acceptors
        	once {
			newReconfig[m];
			clientRequest[v1];
			leaderRcvdNewReconfig[l1];
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
 			allValuesSafe[l1];
			phase2B[a2];
			newReconfig[m];
			leaderRcvdNewReconfig[l2];
			phase1A[l2];
			phase1B[a1];
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m];
			clientRequest[v2];
			allValuesSafe[l2];
			phase2B[a2]
     		}
		(a2.votes[l1.id] != a2.votes[l2.id])
	}
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    16 BasicMessage, 17..17 steps expect 1

/*
The message complete sent by l1 will never be activated because
curBallot of master is bigger than msgComplete.prevBal and the
condition msgComplete.prevBal = m.curBallot will never be satisfied.
However, this is a possible instance.
*/
run scenario5{ 
    some m: Master, disjoint l1, l2: Leader, v: Value,
       disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1];
		newReconfig[m];
		leaderRcvdNewReconfig[l2];
		phase1A[l2];
		phase1B[a1];
		clientRequest[v];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    13 BasicMessage, 14..14 steps expect 1


//activating configuration before it's completed
run scenario6 {
	some m: Master, l1: Leader, a2: Acceptor {
		newReconfig[m]; 
		completeReconfig[m]; 
 		allValuesSafe[l1];
		phase2B[a2]
	}
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 3 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    4 BasicMessage, 5..5 steps expect 0

//since a previousBal was voted it shoud be performed Prepare Phase
run scenario7{
	some m: Master, disjoint l1, l2: Leader, 
		disjoint a1, a2: Acceptor, v: Value {
			newReconfig[m]; 
			leaderRcvdNewReconfig[l1];
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			clientRequest[v]; 
			allValuesSafe[l1]; 
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			leaderRcvdNewReconfig[l2];
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m]
	}
} for exactly 7 Quorum, exactly 2 Leader, 
	exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	12 BasicMessage, 13..13 steps expect 0

//can't send a message M2A without a completeMsg  
run scenario8{ 
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, v: Value {
		newReconfig[m]; 
		newReconfig[m];
		clientRequest[v];
		leaderRcvdNewReconfig[l1];
		leaderRcvdNewReconfig[l2];
		allValuesSafeOrOneValueSafe[l2]; 
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2];
		allValuesSafe[l1]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    12 BasicMessage, 13..13 steps expect 0

/*
Leader2 can't propose any value because a previous value was chosen
*/
run scenario9{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, disjoint v1: Value {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
		clientRequest[v1];
		leaderRcvdNewReconfig[l1];
		allValuesSafeOrOneValueSafe[l1]; 
		newReconfig[m];
		completeReconfig[m]; 
		leaderRcvdNewReconfig[l2];
		allValuesSafe[l1];
		phase2B[a1]; 
		phase2B[a2];
		phase1A[l2];
		phase1B[a2];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
        }
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    17 BasicMessage, 18..18 steps expect 0

/*
Since a previous configuration is still active leader2 has to
perform phase1A before progressing
*/
run scenario10{ 
    some m: Master, disjoint l1, l2: Leader, v: Value,
       disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1];
		newReconfig[m];
		leaderRcvdNewReconfig[l2];
		clientRequest[v];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    11 BasicMessage, 12..12 steps expect 0



/*
Two active configurations, and leader2 performs phase1A and acceptor
a2 answers. When acceptors a1 and a2 are executing phase2B for leader1, 
who has the lower ballot, a2 can't accept the value because his maxBal
is greater than M2A's ballot sent by leader1.

Leader2 can't propose any value because a previous value was chosen
*/
run scenario11{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, disjoint v1: Value {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
		clientRequest[v1];
		leaderRcvdNewReconfig[l1];
		allValuesSafeOrOneValueSafe[l1]; 
		newReconfig[m];
		completeReconfig[m]; 
		leaderRcvdNewReconfig[l2];
		allValuesSafe[l1];
		phase1A[l2];
		phase1B[a2];
		phase2B[a1]
		phase2B[a2];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
        }
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    17 BasicMessage, 18..18 steps expect 0


/*******************CHECKS**************************/

//A quorum of acceptors from current view has voted for v in ballot b.
pred chosenAt[b: Ballot, v: Value] {
	some wq: WQuorum {
		wq.ballot = b
		all a: wq.acceptors | votedFor[a, b, v]
	}
}

//Choosing at most one value
fun chosenValues : set Value {
	{v: Value | some b: Ballot | chosenAt[b, v]}
}

assert ChosenValue {
	always lone chosenValues
}   

check ChosenValue for exactly 8 Quorum, 
	exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 18 BasicMessage, 19..19 steps expect 0


//An acceptor a has voted in v in ballot b
pred votedFor[a: Acceptor, b: Ballot, v: Value] {
	a.votes[b] = v
}

pred didNotVoteAt[a: Acceptor, b: Ballot] {
	all v: Value | not votedFor[a, b, v]
}

//All acceptor from a WQ voted in a b->v or some acceptor has not voted
pred safeQuorum[b: Ballot, v: Value] {
	some wq: WQuorum {
		wq.ballot = b
		((all a: wq.acceptors | votedFor[a, b, v]) or 
              (some a: wq.acceptors | didNotVoteAt[a, b]))
	}
}

/* Voting in a ballot implies that a WQ has previousVoted or
some acceptor from the WQ has not voted in that value,
therefore is not chosen and another value can be chosen in 
current round*/
pred safeAt[b: Ballot, v: Value] {
	all c: prevs[b] | safeQuorum[c, v]
}

assert VotesSafe {
	all a : Acceptor, b : Ballot, v : Value | always (votedFor[a, b, v] 
		implies safeAt[b, v])
}

check VotesSafe for exactly 8 Quorum, 
exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, exactly 2 Value, 
14 BasicMessage, 15..15 steps expect 0


//Only one vote per Ballot (the value is always the same at the ballot x)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] 
		and votedFor[a2, b, v2]) implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for exactly 7 Quorum, 
	exactly 2 Leader, exactly 2 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 18 BasicMessage, 19..19 steps expect 0




/**********************THEME*****************************/ 
//With theme translation capacity is often exceeded.


enum Event {Nop, NewReconfig, CompleteReconfig,
		Phase1B, Phase2B, LeaderRcvdNewReconfig,
		Phase1A, AllValuesSafeOrOneValueSafe, AllValuesSafe, 
		StateTransfer, OneValueSafe, ClientRequest} // event names

fun nop_happens : set Event {
  { e: Nop | nop }
}

fun newReconfig_happens : Event -> Master {
 	{ e: NewReconfig, m: Master | newReconfig[m] }
}

fun clientRequest_happens : Event -> Value {
 	{ e: ClientRequest, v: Value | clientRequest[v] }
}

fun completeReconfig_happens : Event -> Master {
 	{ e: CompleteReconfig, m: Master | completeReconfig[m] }
}

fun  leaderRcvdNewReconfig_happens : Event -> Leader {
 	{ e:  LeaderRcvdNewReconfig, l: Leader |  leaderRcvdNewReconfig[l] }
}

fun  allValuesSafeOrOneValueSafe_happens : Event -> Leader {
 	{ e:  AllValuesSafeOrOneValueSafe, l: Leader |  allValuesSafeOrOneValueSafe[l] }
}

fun  allValuesSafe_happens : Event -> Leader {
 	{ e:  AllValuesSafe, l: Leader |  allValuesSafe[l] }
}

fun  oneValueSafe_happens : Event -> Leader {
 	{ e:  OneValueSafe, l: Leader |  oneValueSafe[l] }
}

fun  stateTransfer_happens : Event -> Leader {
 	{ e:  StateTransfer, l: Leader |  stateTransferCompleted[l] }
}

fun phase1A_happens : Event -> Leader {
  { e: Phase1A, l: Leader | phase1A[l] }
}

fun phase1B_happens : Event -> Acceptor {
  { e: Phase1B, a: Acceptor | phase1B[a] }
}

fun phase2B_happens : Event -> Acceptor {
  { e: Phase2B, a: Acceptor | phase2B[a] }
}

fun events : set Event {
  	nop_happens + 
	phase1A_happens.Leader + 
	phase1B_happens.Acceptor + 
	phase2B_happens.Acceptor +
	stateTransfer_happens.Leader + 
	allValuesSafe_happens.Leader +
	allValuesSafeOrOneValueSafe_happens.Leader + 
	oneValueSafe_happens.Leader +
	leaderRcvdNewReconfig_happens.Leader +
	completeReconfig_happens.Master + 
	newReconfig_happens.Master +
	clientRequest_happens.Value
}

fun oneBallotChosen : one Ballot {
	{b: Ballot | some v: Value | chosenAt[b,v]}
}


fact trace {
  always some events
}


check singleEvent {
  always one events
} for 1..20 steps








