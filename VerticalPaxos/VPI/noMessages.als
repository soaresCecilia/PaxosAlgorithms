/********VERTICAL PAXOS I - NO MESSAGES**************/


/****************MODULES****************************/


open util/ordering[Ballot]

/****************SIGNATURES****************************/

abstract sig Role {
	var sent: Type -> Ballot -> Payload
}

sig Acceptor extends Role {
	var maxBal : lone Ballot,
	var maxVote: lone Vote
}

one sig None {}

abstract sig Type {}
one sig M1A, M1B, M2A, M2B, MsgNewBallot, MsgComplete extends Type {}

sig Vote {
	value : Value,
	ballot : Ballot
}

sig Payload = Ballot + Value + Vote + None {}

//leaders within this set are aware of reconfiguration
var sig RcvdNewBal in Leader {} 

abstract sig Leader extends Role {
	var safeVal: lone Value,
	var previousBal: lone Ballot, 
	var lCompleteBal: lone Ballot,
	var allPreviousBal: set Ballot,
	id: one Ballot 
}


/*There is reliable service that begins the reconfiguration protocol.
We represent that service as a single master.
It stores the current Ballot, which starts at 0 (lone), 
and the mCompleteBal, that starts at 1 (one)
*/
one sig Master extends Role {
	var mCompleteBal: lone Ballot,
	var nextBal: one Ballot,
}

sig Value {}

sig Ballot {}

//each quorum belongs to a round
abstract sig Quorum {
	ballot: one Ballot,
	acceptors : some Acceptor
}

//Write Quorum
sig WQuorum extends Quorum {}

//Read Quorum
sig RQuorum extends Quorum {}

/****************FACTS****************************/

fact Quorums {
	/*	All read and write quorums from the same ballot intersect.
		Each read quorum has a single acceptor.
		All write quorums have, at least, the acceptors from each read quorum associated
		with a ballot. For instance, RQ[b] = {{a1}, {a2}, {a3}}, WQ[b] = {{a1, a2, a3, a4}}		
	*/
	all b: Ballot {
		//WQuorum intersects with all RQuorum from the same round
		all wq: WQuorum, rq: RQuorum | (wq.ballot = b and rq.ballot = b) implies
					some (wq.acceptors & rq.acceptors)
		//one WQuorum for each round
		one wq: WQuorum |  wq.ballot = b
		//every round has a RQuorum
		some rq: RQuorum | rq.ballot = b
	}
	//Each RQuorum has a single acceptor.
	all rq: RQuorum | one rq.acceptors
	//All acceptors belong to a quorum
	all a: Acceptor | some q: Quorum | a in q.acceptors
}

fact AllPossibleVotesExist {
	all v : Value, b : Ballot | some x : Vote | x.value = v and x.ballot = b
}

fact SetBallotLeader {
	//all leaders have unique ids
	all disjoint l1, l2: Leader | no l1.id & l2.id
	//all leaders' id are set with the smaller Ballots
	all l : Leader | no b : Ballot | lt[b,l.id] and no id.b  
}

//Initial State
fact Init {
	no maxBal
	no maxVote
	no safeVal
	no previousBal
	no lCompleteBal
	no allPreviousBal
	no RcvdNewBal
	no mCompleteBal
	Master.nextBal = first
	no sent

}

//Next-state actions - All possible events
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
		oneValueSafe[l]
	)
}

/****************PREDICATES****************************/

//System stuttering
pred nop {
	maxBal' = maxBal
	maxVote' =  maxVote
	sent' = sent
	safeVal' = safeVal
	previousBal' = previousBal
	lCompleteBal' = lCompleteBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}


//Master starts a new reconfiguration 
pred newReconfig[m: Master] {
	no m.mCompleteBal implies { 
		sent' = sent + m->MsgNewBallot->(m.nextBal)->None
	} 
	else {
		sent' = sent + m->MsgNewBallot->(m.nextBal)->(m.mCompleteBal)
	}	
	nextBal' = next[nextBal]
	maxBal' = maxBal
	maxVote' = maxVote
	mCompleteBal' = mCompleteBal
	lCompleteBal' = lCompleteBal
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
}

/*Leader receives NewBallot Message */
pred leaderRcvdNewReconfig[l: Leader] {
	let msgNB = {Master.sent[MsgNewBallot]} | {
		some msgNB[l.id]
		msgNB[l.id] != None implies {
			 lCompleteBal' = lCompleteBal ++ ( l->msgNB[l.id])
		} else {
			lCompleteBal' = lCompleteBal
		}
		//note that prev[first] = {} (empty set) so it works fine
		previousBal' = previousBal ++ (l->prev[l.id])	
		//this is going to set allpB and this makes possible to send multipluous Msg1A with descending ballots
		let allpB = { b: Ballot | (msgNB[l.id] = None or (msgNB[l.id] != None 
					and gte[b, msgNB[l.id]])) and lt[b, l.id]} | {
			allPreviousBal' = allPreviousBal ++ (l ->(allpB))
		}
		
	}
	maxBal' = maxBal
	maxVote' = maxVote
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	RcvdNewBal' = RcvdNewBal + l
	sent' = sent	
}


//Leader sends a Prepare Request - PHASE 1A
pred phase1A[l: Leader] {
	l in RcvdNewBal

	/* if there is no l.safeVal and there is a previousBal the leader has to perform
	phase1A. Besides, if lCompleteBal is not empty the phase1A has to be done 
	until reaches the configuration with the ballot equals to lCompleteBal. 
	Remember that module ordering considers the empty set the greatest*/
	no l.safeVal and (some l.previousBal and 
                                                            (no l.lCompleteBal or 
                                                            (some l.lCompleteBal and gte[l.previousBal, l.lCompleteBal])))
	
	//optimisation - no repeated messages - leader can't send the same message. 
	//However, he will send several M1A with different previousBal
	no (l.sent[M1A][l.id] & l.previousBal) 
	
	sent' = sent + l->M1A->l.id->l.previousBal	
	
	maxBal' = maxBal
	maxVote' = maxVote
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
	safeVal' = safeVal
	previousBal' = previousBal ++ (l->prev[l.previousBal])
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
}

/*All acceptors from previous view must inform the leader 
what value each one had voted  */
pred phase1B[a: Acceptor] {
	some bal: Leader.sent[M1A].Payload {
		//acceptor has not yet reply to that M1A
		no a.maxBal or gt[bal, a.maxBal] 
		no a.maxVote implies {
			sent' = sent + (a->M1B->bal->None)
		} 
		else {
			sent' = sent + a->M1B->bal->(a.maxVote)
		}
		maxBal' = maxBal ++ a->bal
	}		
	maxVote' = maxVote
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

// PHASE 2A - Accept

//Phase Alternative - No Previous Value Chosen or Some Chosen Value
pred allValuesSafeOrOneValueSafe[l: Leader] {
	l in RcvdNewBal	
	no l.safeVal 
	no l.sent[MsgComplete][l.id]
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
	all b: l.allPreviousBal | some rq: RQuorum {
		rq.ballot = b
		((rq.acceptors).sent[M1B][l.id] = None)
	}
}


/*Some acceptors from one of readQuorums of previous round 
has voted in some value. Therefore, is stored in safeVal because
our model garantees that every read quorum has only a single acceptor
*/
pred someOneVoted[l: Leader] {
	 some b: l.allPreviousBal, rq: RQuorum {
		rq.ballot = b
 		(rq.acceptors).sent[M1B][l.id] != None //acceptor a has already casted a vote
		safeVal' = safeVal ++ l->((rq.acceptors).sent[M1B][l.id]).value
	}
	maxBal' = maxBal
	maxVote' = maxVote
	sent' = sent
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

//SEND MSG 2A - Some safeVal implies sending 2A
pred oneValueSafe[l: Leader] {
	some l.safeVal
	no l.sent[M2A][l.id]
	sent' = sent + l->M2A->l.id->l.safeVal
	
	maxBal' = maxBal
	maxVote' = maxVote
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	safeVal' = safeVal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

//PHASE 2B

//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some bal : Ballot,  m2aPayload: Leader.sent[M2A][bal], v : Vote {	
		no a.sent[M2B][bal]
		no a.maxBal or gte[bal, a.maxBal]
		v.ballot = bal and v.value = m2aPayload
		maxBal' = maxBal ++ a->bal
		maxVote' = maxVote ++ a->v
		sent' = sent + a->M2B->bal->m2aPayload
	}
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	safeVal' = safeVal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

// All quorum's members from a current write quorum have sent a M2B
pred stateTransferCompleted[l: Leader] {
	some l.safeVal and no l.sent[MsgComplete][l.id]
	some wq: WQuorum {
		wq.ballot = l.id
		all a: wq.acceptors {
			some a.sent[M2B][l.id]	
		}	
	}
	sendComplete[l]
}

//Leader sends a complete reconfiguration message
pred sendComplete[l: Leader] {
	no l.previousBal implies {
		sent' = sent + l->MsgComplete->l.id->None
	}	
	else {
		sent' = sent + l->MsgComplete->l.id->l.previousBal	
	}
	maxBal' = maxBal
	maxVote' = maxVote
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	mCompleteBal' = mCompleteBal
	nextBal' = nextBal
}

//Reconfiguration is completed when Master receives a MsgComplete and afterwards sends MsgActivated
pred completeReconfig[m: Master] {
	some bal: Ballot {
		some Leader.sent[MsgComplete][bal]
		no m.mCompleteBal or gt[bal, m.mCompleteBal]
		mCompleteBal' = mCompleteBal ++ (m->bal)
	}
	maxBal' = maxBal
	maxVote' = maxVote
	sent' = sent
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	nextBal' = nextBal
}

//Sending M2A if no one has voted
pred allValuesSafe[l: Leader]{
	no l.safeVal
	some l.sent[MsgComplete][l.id]
	no l.sent[M2A][l.id]
	//there is no msgClient so we pick some value
	some v: Value | sent' = sent + l->M2A->l.id->v
	
	maxBal' = maxBal
	maxVote' = maxVote
	safeVal' = safeVal
	previousBal' = previousBal
	allPreviousBal' = allPreviousBal
	RcvdNewBal' = RcvdNewBal
	lCompleteBal' = lCompleteBal
	nextBal' = nextBal
	mCompleteBal' = mCompleteBal
}


/******************************RUNS**********************/

//translation capacity exceeded
//One value was chosen in previous round
run scenario1 {
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1]; 
		allValuesSafeOrOneValueSafe[l1]; 
		completeReconfig[m]; 
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
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    3 Vote, 18..18 steps expect 1

//No previous active configuration
run scenario2{
   some m: Master, l1: Leader,
        disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1];
		allValuesSafeOrOneValueSafe[l1];
            	completeReconfig[m]; 
		allValuesSafe[l1];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 8..8 steps expect 1

//Some value chosen in current round
run scenario3 {
	some m: Master, disjoint l1, l2: Leader, 
        disjoint a1, a2: Acceptor {
		newReconfig[m];
		leaderRcvdNewReconfig[l1]; 
		allValuesSafeOrOneValueSafe[l1]; 
            	completeReconfig[m]; 
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
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    3 Vote, 14..14 steps expect 1

/*
An acceptor can vote even if he hasn't participated in Prepare Phase.
Besides, an acceptor only has to vote in the previous value if it
was chosen by a WQuorum. 

Translation capacity exceeded.
*/
run scenario4{
     eventually some m: Master, disjoint l1, l2: Leader,
	disjoint a1, a2: Acceptor, disjoint b1, b2, b3: Ballot {
		gt[b3, b2] and gt[b2, b1] and l1.id = b1 and l2.id = b2
		a1 + a2 in WQuorum.acceptors
        	once {
			newReconfig[m];
			leaderRcvdNewReconfig[l1]; 
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			leaderRcvdNewReconfig[l1]; 
 			allValuesSafe[l1];
			phase2B[a2];
			newReconfig[m];
			leaderRcvdNewReconfig[l2];
			phase1A[l2];
			phase1B[a1];
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m];
			allValuesSafe[l2];
			phase2B[a2]
       			 }
		no ((a2.sent[M2B][l1.id]).value & (a2.sent[M2B][l2.id]).value)
	}
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 16..16 steps expect 1


/*
The message complete sent by l1 will never be activated because
curBallot of master is bigger than msgComplete.prevBal and the
condition msgComplete.prevBal = m.curBallot will never be satisfied.
However, this is a possible instance.
*/
run scenario5{ 
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1];
		newReconfig[m];
		leaderRcvdNewReconfig[l2];
		phase1A[l2];
		phase1B[a1];
		allValuesSafeOrOneValueSafe[l2]; 
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
   	6 Vote, 13..13 steps expect 1


//activating configuration before it's completed
run scenario6 {
	some m: Master, l1: Leader, a2: Acceptor {
		newReconfig[m];
		leaderRcvdNewReconfig[l1];
		completeReconfig[m]; 
 		allValuesSafe[l1];
		phase2B[a2]
	}
} for exactly 10 Quorum, exactly 2 Leader, 
    exactly 3 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    6 Vote, 6..6 steps expect 0


//A value was chosen in previous round but no prepare phase is 
//done in future round
run scenario7{
	some m: Master, disjoint l1, l2: Leader, disjoint a1, a2: Acceptor {
			newReconfig[m]; 
			leaderRcvdNewReconfig[l1];
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			allValuesSafe[l1]; 
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			leaderRcvdNewReconfig[l2];
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m]
	}
} for exactly 8 Quorum, exactly 2 Leader, 
	exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 12..12 steps expect 0

/*
The message complete sent by l1 will never be activated because
curBallot of master is bigger than msgComplete.prevBal and the
condition msgComplete.prevBal = m.curBallot will never be satisfied.
However, this is a possible instance.
*/
run scenario8{ 
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		newReconfig[m];
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
    6 Vote, 12..12 steps expect 0

/*
Leader2 can't propose a random value (allValuesSafe[l2]) because a specific
value was chosen by a1 and a2 in previous round. So, qhen Leader2 performs
phase1A[l2] he must learn the safeVal to propose.

Translation capacity exceeded
*/
run scenario9{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
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
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    3 Vote, 17..17 steps expect 0

/*
Since a previous configuration is still active leader2 has to
perform phase1A before progressing
*/
run scenario10{ 
    some m: Master, disjoint l1, l2: Leader,
       disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		leaderRcvdNewReconfig[l1];
		newReconfig[m];
		leaderRcvdNewReconfig[l2];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
   exactly 6 Vote, 11..11 steps expect 0

/*
Two active configurations, and leader2 performs phase1A and acceptor
a2 answers. When acceptors a1 and a2 are executing phase2B for leader1, 
who has the lower ballot, a2 can't accept the value because his maxBal
is greater than M2A's ballot sent by leader1.

Leader2 can't propose any value because a previous value was chosen

Translation capacity exceeded
*/
run scenario11{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
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
    exactly 3 Vote, 17..17 steps expect 0


/******************* CHECKS ************************/

//An acceptor a has voted in v in ballot b
pred votedFor[a: Acceptor, b: Ballot, v: Value] {
	v in a.sent[M2B][b]
}

//A quorum of acceptors from current view has voted for v in ballot b.
pred chosenAt[b: Ballot, v: Value] {
	some wq: WQuorum {
		wq.ballot = b
		all a: wq.acceptors | votedFor[a, b, v]
	}
}

//Choosing at most one value
fun chosenValue : set Value {
	{v: Value | some b: Ballot | chosenAt[b, v]}
}

assert ChosenValue {
	always lone chosenValue
} 

check ChosenValue for exactly 6 Quorum, 
	exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 6 Vote, 10..10 steps expect 0

pred didNotVoteAt[a: Acceptor, b: Ballot] {
	all v: Value | not votedFor[a, b, v]
}

//An acceptor a has already voted in b->v or he will never cast a vote in ballot b
pred safeQuorum[b: Ballot, v: Value] {
	some wq: WQuorum {
		wq.ballot = b
		((all a: wq.acceptors | votedFor[a, b, v]) or 
              (some a: wq.acceptors | didNotVoteAt[a, b]))
	}
}

/* No other value than v has been or can ever be chosen in any
ballot less than b  
*/
pred safeAt[b: Ballot, v: Value] {
	all c: prevs[b] | safeQuorum[c, v]
}

assert VotesSafe {
	all a : Acceptor, b : Ballot, v : Value | always (votedFor[a, b, v] 
			implies safeAt[b, v])
}

check VotesSafe for exactly 7 Quorum, 
	exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 6 Vote, 20..20 steps expect 0

//Only one vote per Ballot (the value is always the same at the ballot b)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] and 
		votedFor[a2, b, v2]) implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for exactly 6 Quorum, 
	exactly 2 Leader, exactly 2 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 6 Vote, 20..20 steps expect 0


/**********************THEME*****************************/ 
//With theme translation capacity is often exceeded.


enum Event {Nop, NewReconfig, CompleteReconfig,
		Phase1B, Phase2B, LeaderRcvdNewReconfig,
		Phase1A, AllValuesSafeOrOneValueSafe, AllValuesSafe, 
		StateTransfer, OneValueSafe} // event names

fun nop_happens : set Event {
  { e: Nop | nop }
}

fun newReconfig_happens : Event -> Master {
 	{ e: NewReconfig, m: Master | newReconfig[m] }
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
	newReconfig_happens.Master
}

fun oneBallotChosen : one Ballot {
	{b: Ballot | some v: Value | chosenAt[b,v]}
}

fact trace {
  always some events
}

check singleEvent {
  always one events
}







