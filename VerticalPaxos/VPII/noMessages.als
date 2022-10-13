/************VERTICAL PAXOS II WITHOUT MESSAGES*********/

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
one sig M1A, M1B, M2A, M2B, MsgNewBallot, MsgComplete, MsgActivated extends Type {}

sig Vote {
	value : Value,
	ballot : Ballot
}

sig Payload = Ballot + Value + Vote + None {}

sig Leader extends Role {
	var safeVal: lone Value,
	var previousBal: lone Ballot, 
	id: one Ballot 
}

one sig Master extends Role {
	var curBallot: lone Ballot,
	var nextBallot: one Ballot
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
	no curBallot
	Master.nextBallot = first
	no safeVal
	no previousBal
	no sent
}

fact Next {
	always (nop or
		some m: Master | newReconfig[m] or
		completeReconfig[m] or
		some a: Acceptor | phase1B[a] or 
		phase2B[a] or
		some l: Leader | leaderNewReconfig[l] or
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
	maxVote' = maxVote
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal
	previousBal' = previousBal
	sent' = sent
}

//Master starts a new reconfiguration 
pred newReconfig[m: Master] {
	no m.curBallot implies { 
		sent' = sent +  m->MsgNewBallot->(m.nextBallot)->None
	} 
	else {
		sent' = sent + m->MsgNewBallot->(m.nextBallot)->(m.curBallot)
	}	
	nextBallot' = next[nextBallot]
	maxBal' = maxBal
	maxVote' = maxVote
	curBallot' = curBallot
	safeVal' = safeVal
	previousBal' = previousBal
}

/*Leader receives NewBallot Message */
pred leaderNewReconfig[l: Leader] {
	some Master.sent[MsgNewBallot][l.id] {
		Master.sent[MsgNewBallot][l.id] != None
		no l.sent[M1A][l.id]
		//sending M1A with prevBal and updating leader's info
		let prevBal = {Master.sent[MsgNewBallot][l.id]} | {
			sent' = sent + l->M1A->l.id->prevBal
			prevBal != None implies {
				previousBal' = previousBal ++ (l->prevBal)
			} else {
				previousBal' = previousBal
			}
		}
	}
	maxBal' = maxBal
	maxVote' = maxVote
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal	
}

/*All acceptors from previous view must inform the leader 
what value each one had voted  */
pred phase1B[a: Acceptor] {
	some bal: Leader.sent[M1A].Payload {
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
	curBallot' = curBallot
	nextBallot' = nextBallot	
}

//Alternative paths 
pred allValuesSafeOrOneValueSafe[l: Leader] {
	some (Master.sent[MsgNewBallot][l.id])

	// avoid computing unnecessary steps
	no l.safeVal and no l.sent[MsgComplete][l.id]
	noPreviousValueChosen[l] implies {
		sendComplete[l]
	}
 	else {
		someOneVoted[l]
	}
}

/*All acceptors from some read quorum of previous view had sent a M1B
and no one from that quorum voted.
If there isn't a previousBal verifications will not be necessary and
if there is no vote in payload nobody has voted yet
 */
pred noPreviousValueChosen[l: Leader] {
	no l.previousBal or some rq: RQuorum {	
		rq.ballot = l.previousBal 
		((rq.acceptors).sent[M1B][l.id] = None)
	}
}

/*Some acceptors from one of readQuorums of previous round 
has voted in some value. Therefore, is stored in safeVal because
our model garantees that every read quorum has only a single acceptor
*/
pred someOneVoted[l: Leader] {
	some l.previousBal		
	some rq: RQuorum {	
		rq.ballot = l.previousBal
 		(rq.acceptors).sent[M1B][l.id] != None
		safeVal' = safeVal ++ l->((rq.acceptors).sent[M1B][l.id]).value
	}
	maxBal' = maxBal
	maxVote' = maxVote
	sent' = sent
	curBallot' = curBallot
	nextBallot' = nextBallot
	previousBal' = previousBal
}

//Some safeVal implies doing Accept Phase
pred oneValueSafe[l: Leader] {
	some l.safeVal
	no l.sent[M2A][l.id]
	sent' = sent + l->M2A->l.id->l.safeVal
 
	maxBal' = maxBal
	maxVote' = maxVote
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal
	previousBal' = previousBal	
}

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
	safeVal' = safeVal
	previousBal' = previousBal
	curBallot' = curBallot
	nextBallot' = nextBallot
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
	nextBallot' = nextBallot
	curBallot' = curBallot
}

//Reconfiguration is completed when Master receives a MsgComplete and sends a MsgActivated
pred completeReconfig[m: Master] {
	some bal: Ballot {
		some Leader.sent[MsgComplete][bal] 
		no m.curBallot or (some Leader.sent[MsgComplete][bal] & m.curBallot) //msgCompl.prevBal = m.curBallot
		no m.sent[MsgActivated][bal]
		no m.curBallot implies {
			sent' = sent + m->MsgActivated->bal->None
		}
		else {
			sent' = sent + m->MsgActivated->bal->m.curBallot
		}
		curBallot' = curBallot ++ (m->bal) 
	}
	maxBal' = maxBal
	maxVote' = maxVote
	safeVal' = safeVal
	previousBal' = previousBal
	nextBallot' = nextBallot
}

//Sending M2A if no one has voted
pred allValuesSafe[l: Leader]{
	some (Master.sent[MsgActivated][l.id]) 
	no l.safeVal
	no l.sent[M2A][l.id]
	//there is no msgClient so we pick some value
	some v: Value | sent' = sent + l->M2A->l.id->v
	maxBal' = maxBal
	maxVote' = maxVote
	safeVal' = safeVal
	previousBal' = previousBal
	curBallot' = curBallot
	nextBallot' = nextBallot
}

run scenario1 {
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
		newReconfig[m];
		allValuesSafeOrOneValueSafe[l1];
		completeReconfig[m];
		newReconfig[m];
		leaderNewReconfig[l2];
		phase1B[a1];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m];
		allValuesSafe[l2];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    6 Vote, 12..12 steps expect 1

run scenario2{
	some m: Master, l1: Leader, disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
            	completeReconfig[m]; 
		allValuesSafe[l1];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 7..7 steps expect 1

run scenario3 {
    some m: Master, disjoint l1, l2: Leader, 
        disjoint a1, a2: Acceptor {
		newReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1]; 
            	completeReconfig[m]; 
		newReconfig[m]; 
            	leaderNewReconfig[l2]; 
		phase1B[a1];
            	allValuesSafeOrOneValueSafe[l2];  
		completeReconfig[m];
		allValuesSafe[l2];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    6 Vote, 12..12 steps expect 1

run scenario4{
     some m: Master, disjoint L1, L2: Leader,
	disjoint A1, A2: Acceptor {
		newReconfig[m];
		allValuesSafeOrOneValueSafe[L1]; 
		completeReconfig[m]; 
 		allValuesSafe[L1];
		phase2B[A2];
		newReconfig[m];
		leaderNewReconfig[L2];
		phase1B[A1];
		allValuesSafeOrOneValueSafe[L2];
		completeReconfig[m];
		allValuesSafe[L2];
		phase2B[A2]
   
		no ((A2.sent[M2B][L1.id]).value & (A2.sent[M2B][L2.id]).value)
	}
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 13..13 steps expect 1


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
		newReconfig[m];
		allValuesSafeOrOneValueSafe[l2]; 
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
   	6 Vote, 9..9 steps expect 1

//activating configuration before it's completed
run scenario6 {
	some m: Master, l1: Leader, a2: Acceptor {
		newReconfig[m]; 
		completeReconfig[m]; 
 		allValuesSafe[l1];
		phase2B[a2]
	}
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 3 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    6 Vote, 5..5 steps expect 0


//A value was chosen in previous round but no prepare phase is 
//done in future round
run scenario7{
	some m: Master, disjoint l1, l2: Leader, disjoint a1, a2: Acceptor {
			newReconfig[m]; 
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			allValuesSafe[l1]; 	
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m]
	}
} for exactly 7 Quorum, exactly 2 Leader, 
	exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	6 Vote, 10..10 steps expect 0

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
    6 Vote, 10..10 steps expect 0


run scenario9{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
		leaderNewReconfig[l1];
		allValuesSafeOrOneValueSafe[l1]; 
		newReconfig[m];
		completeReconfig[m]; 
		leaderNewReconfig[l2];
		allValuesSafe[l1];
		phase2B[a1]; 
		phase2B[a2];
		allValuesSafeOrOneValueSafe[l2];
		completeReconfig[m]; 
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
        }
    }
} for exactly 6 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 1 Value, 
    3 Vote, 15..15 steps expect 0

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
	exactly 2 Value, 6 Vote, 9..9 steps expect 0

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

check VotesSafe for exactly 9 Quorum, 
	exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 6 Vote, 25..25 steps expect 0

//Only one vote per Ballot (the value is always the same at the ballot b)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] 
		and votedFor[a2, b, v2]) implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for exactly 9 Quorum, 
	exactly 2 Leader, exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 6 Vote, 25..25 steps expect 0

/**********************THEME*****************************/ 
//With theme translation capacity is often exceeded.

enum Event {Nop, NewReconfig, CompleteReconfig,
		Phase1B, Phase2B, LeaderNewReconfig,
		AllValuesSafeOrOneValueSafe, AllValuesSafe, 
		StateTransfer, OneValueSafe}

fun nop_happens : set Event {
  { e: Nop | nop }
}

fun newReconfig_happens : Event -> Master {
 	{ e: NewReconfig, m: Master | newReconfig[m] }
}

fun completeReconfig_happens : Event -> Master {
 	{ e: CompleteReconfig, m: Master | completeReconfig[m] }
}

fun  leaderNewReconfig_happens : Event -> Leader {
 	{ e:  LeaderNewReconfig, l: Leader |  leaderNewReconfig[l] }
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

fun phase1B_happens : Event -> Acceptor {
  { e: Phase1B, a: Acceptor | phase1B[a] }
}

fun phase2B_happens : Event -> Acceptor {
  { e: Phase2B, a: Acceptor | phase2B[a] }
}

fun events : set Event {
  	nop_happens + 
	phase1B_happens.Acceptor + 
	phase2B_happens.Acceptor +
	stateTransfer_happens.Leader + 
	allValuesSafe_happens.Leader +
	allValuesSafeOrOneValueSafe_happens.Leader + 
	oneValueSafe_happens.Leader +
	leaderNewReconfig_happens.Leader +
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











