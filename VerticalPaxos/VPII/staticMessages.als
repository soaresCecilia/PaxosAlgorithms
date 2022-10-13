/**************VERTICAL PAXOS II WITH MSGBOX*******/

/****************MODULES****************************/

open util/ordering[Ballot]

/****************SIGNATURES****************************/

sig Acceptor {
	var maxBal : lone Ballot,
	var votes: Ballot -> lone Value
}

sig Leader {
	var safeVal: lone Value,
	var previousBal: lone Ballot, 
	id: one Ballot 
}

one sig Master {
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


abstract sig BasicMessage {}

//set of messages that have been sent
var sig MsgBox in BasicMessage{}

/*Messages that will be exchanged
all messages, except Client messages, have relation bal in common */
abstract sig Message extends BasicMessage  {
	bal: one Ballot	
}

/*
Client messages are a new type of messages
because they do not have ballot, only one value 
*/
sig MsgClient extends BasicMessage{
	value: one Value
}

//Different types of messages
sig MsgNewBallot extends Message {
	 prevBal: lone Ballot
}

sig M1A extends Message {
	prevBal: lone Ballot
}

sig M1B extends Message {
	acceptor: one Acceptor,
	mbal: lone Ballot,
	mval: lone Value
}

sig M2A extends Message {
	value: one Value
}

sig M2B extends Message {
	acceptor: one Acceptor,
	value: one Value
}

sig MsgComplete extends Message{
	prevBal: lone Ballot
}

sig MsgActivated extends Message {}


/****************FACTS****************************/

fact Quorums {
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

fact SetBallotLeader {
	//all leaders have unique ids
	all disjoint l1, l2: Leader | no l1.id & l2.id
	//all leaders' id are set with the smaller Ballots
	all l : Leader | no b : Ballot | lt[b,l.id] and no id.b  
}

//Initial State
fact Init {
	no maxBal
	no votes
	no curBallot
	Master.nextBallot = first
	no safeVal
	no previousBal
	no MsgBox
}

//Next-state actions
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
		oneValueSafe[l] or 
		some v: Value | clientRequest[v]
	)
}

/****************PREDICATES****************************/

//Sending a message
pred send[m: BasicMessage] {
	MsgBox' = MsgBox + m
}

//Master starts a new reconfiguration 
pred newReconfig[m: Master] {
	some msgNew: MsgNewBallot {  
		msgNew.bal = m.nextBallot
		msgNew.prevBal = m.curBallot
		send[msgNew]
	}
	nextBallot' = next[nextBallot] 
	maxBal' = maxBal
	votes'  = votes
	curBallot' = curBallot
	safeVal' = safeVal
	previousBal' = previousBal
}

// Leader receives NewBallot Message
pred leaderNewReconfig[l: Leader] {
	some msgNew: MsgNewBallot & MsgBox {
		msgNew.bal = l.id
		//msg 1A is not send when msgNewBallot.prevBal does not exists
		some msgNew.prevBal
		no msg1a: M1A & MsgBox | msg1a.bal = msgNew.bal 
		// Prepare Phase
		some m1a: M1A {
		 	m1a.bal= msgNew.bal
			m1a.prevBal = msgNew.prevBal
			send[m1a]
		}
		previousBal' = previousBal ++ (l-> msgNew.prevBal)
	}
	maxBal' = maxBal
	votes' = votes
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal	
}

/*All acceptors from current and previous view must inform the leader 
what was the last ballot and value that each one had voted  */
pred phase1B[a: Acceptor] {
	some m1a: MsgBox & M1A { 
		no a.maxBal or gt[m1a.bal, a.maxBal] 	
		some m1b: M1B {
			m1b.bal = m1a.bal
			m1b.mbal' = m1a.prevBal
			m1b.mval' = a.votes[m1a.prevBal]
			m1b.acceptor = a
			send[m1b]
		}
		maxBal' = maxBal ++ a->(m1a.bal)
	}	
	votes' = votes
	safeVal' = safeVal
	previousBal' = previousBal
	curBallot' = curBallot
	nextBallot' = nextBallot	
}

//Alternative paths
pred allValuesSafeOrOneValueSafe[l: Leader] {
	some msgNew: MsgNewBallot & MsgBox | msgNew.bal = l.id
	no l.safeVal and no msgComp: MsgComplete & MsgBox | msgComp.bal = l.id 
	noPreviousValueChosen[l] implies {
		sendComplete[l]
	}
 	else {
		someOneVoted[l]
	}
}

/*All acceptors from a quorum of previous view had sent a 1b message
and no one from that quorum voted in any previous ballot.
If there isn't a previousBal verifications will not be necessary
*/ 
pred noPreviousValueChosen[l: Leader] {
	no l.previousBal or some rq: RQuorum {	
		rq.ballot = l.previousBal
		some m1b: M1B & MsgBox {
			m1b.acceptor = rq.acceptors
			m1b.bal = l.id
			m1b.mbal = l.previousBal
			no m1b.mval	
		}
	}
}

pred someOneVoted[l: Leader] {
	some l.previousBal	
	some rq: RQuorum {	
		rq.ballot = l.previousBal
		some m1b: M1B & MsgBox {
			m1b.acceptor = rq.acceptors
			m1b.bal = l.id
			m1b.mbal= l.previousBal
			some m1b.mval
			
			safeVal' = safeVal ++ (l->m1b.mval)
		}
	}
	maxBal' = maxBal
	votes' = votes
	curBallot' = curBallot
	nextBallot' = nextBallot
	previousBal' = previousBal
	MsgBox' = MsgBox
}

//Sending M2A
pred oneValueSafe[l: Leader] {
	some l.safeVal
	no m2a: M2A & MsgBox | m2a.bal = l.id
 
	some msg2a: M2A {
		msg2a.bal = l.id
	 	msg2a.value = l.safeVal
		send[msg2a]
	}
	maxBal' = maxBal
	votes' = votes
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal
	previousBal' = previousBal	
}

//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some m2a: M2A & MsgBox {
		no a.maxBal or gte[m2a.bal, a.maxBal]
		no m2b: M2B & MsgBox | m2b.bal = m2a.bal and m2b.acceptor = a
		
		maxBal' = maxBal ++ a->(m2a.bal)		
		votes' = votes + (a->(m2a.bal)->(m2a.value))
	
		some msg2b: M2B {
			msg2b.bal = m2a.bal
			msg2b.value = m2a.value 
			msg2b.acceptor = a
			send[msg2b]
		}
	}
	safeVal' = safeVal
	previousBal' = previousBal
	curBallot' = curBallot
	nextBallot' = nextBallot
}

// All quorum's members from a current write quorum have sent a M2B
pred stateTransferCompleted[l: Leader] {
	some l.safeVal 
	no msgComp: MsgComplete & MsgBox | msgComp.bal = l.id
	some wq: WQuorum {
		wq.ballot = l.id
		all a: wq.acceptors {
			some m2b: M2B & MsgBox {
				m2b.bal = l.id
				m2b.acceptor = a
			}
		}	
	}
	sendComplete[l]
}

//Leader sends a complete reconfiguration message
pred sendComplete[l: Leader] {
	some msgComplete: MsgComplete {
		msgComplete.prevBal = l.previousBal
		msgComplete.bal = l.id		
		send[msgComplete]
	}
	maxBal' = maxBal
	votes' = votes
	safeVal' = safeVal
	previousBal' = previousBal
	nextBallot' = nextBallot
	curBallot' = curBallot
}

//Reconfiguration is completed when Master receives a MsgComplete then sends MsgActivated
pred completeReconfig[m: Master] {
	some msgComplete : MsgComplete & MsgBox {
		no m.curBallot or msgComplete.prevBal = m.curBallot
		no msgAct : MsgActivated & MsgBox | msgAct.bal = msgComplete.bal
		some msgAct : MsgActivated {
			msgAct.bal = msgComplete.bal
			send[msgAct]
		}
		curBallot' = curBallot ++ (m->msgComplete.bal)
	}
	maxBal' = maxBal
	votes' = votes 
	safeVal' = safeVal
	previousBal' = previousBal
	nextBallot' = nextBallot
}

//Accept Phase when no one voted
pred allValuesSafe[l: Leader]{
	some mActv: MsgActivated & MsgBox {
		mActv.bal = l.id
		no l.safeVal
		no m2a: M2A & MsgBox | m2a.bal = l.id 
		some msgClient: MsgClient & MsgBox {
			some m2a: M2A {
				m2a.bal = mActv.bal
				m2a.value = msgClient.value
				send[m2a]
			}
		}
	}
	maxBal' = maxBal
	votes' = votes
	safeVal' = safeVal
	previousBal' = previousBal
	curBallot' = curBallot
	nextBallot' = nextBallot
}

//Client sends a broadcast message
pred clientRequest[v: Value] {
	no msgClient: MsgClient & MsgBox | msgClient.value = v
	some msgClient: MsgClient {
		msgClient.value = v
		send[msgClient]
	}
	maxBal' = maxBal
	votes' = votes
	nextBallot' = nextBallot
	curBallot' = curBallot
	safeVal' = safeVal
	previousBal' = previousBal
}

//System stuttering
pred nop {
	maxBal' = maxBal
	votes' = votes
	curBallot' = curBallot
	nextBallot' = nextBallot
	safeVal' = safeVal
	previousBal' = previousBal
	MsgBox' = MsgBox
}


/******************************RUNS********************/


//We need one more ballot than leaders to have progress because of master's nexBallot
run scenario1{
	some m: Master, disjoint l1, l2: Leader, disjoint a1, a2: Acceptor, v: Value {
			newReconfig[m]; 
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			clientRequest[v]; 
			allValuesSafe[l1]; 
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			leaderNewReconfig[l2]; 
			phase1B[a1]; 
			allValuesSafeOrOneValueSafe[l2]; 
			oneValueSafe[l2]; 
			phase2B[a1]; 
			phase2B[a2]; 
			stateTransferCompleted[l2]; 
			completeReconfig[m]
	}
} for exactly 6 Quorum, exactly 2 Leader, 
	exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	16 BasicMessage, 17..17 steps expect 1

run scenario2{
    some m: Master, l1: Leader, 
        disjoint a1, a2: Acceptor, v: Value {
            	newReconfig[m]; 
		clientRequest[v]; 
		allValuesSafeOrOneValueSafe[l1]; 
            	completeReconfig[m]; 
		allValuesSafe[l1];
            	phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 6 Quorum, exactly 1 Leader, 
    exactly 2 Acceptor, exactly 2 Ballot, exactly 1 Value, 
    7 BasicMessage, 8..8 steps expect 1

run scenario3{
	some m: Master, disjoint l1, l2: Leader, 
        	disjoint a1, a2: Acceptor, v: Value {
		newReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1]; 
		completeReconfig[m]; 
		clientRequest[v]; 
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
    12 BasicMessage, 13..13 steps expect 1

run scenario4{
     eventually some m: Master, disjoint L1, L2: Leader,
	disjoint A1, A2: Acceptor, disjoint v1, v2: Value {
		once{
			newReconfig[m];
			clientRequest[v1];
			allValuesSafeOrOneValueSafe[L1]; 
			completeReconfig[m]; 
 			allValuesSafe[L1];
			phase2B[A2];
			newReconfig[m];
			leaderNewReconfig[L2];
			phase1B[A1];
			allValuesSafeOrOneValueSafe[L2];
			completeReconfig[m];
			clientRequest[v2];
			allValuesSafe[L2];
			phase2B[A2]
		}
		 	(A2.votes[L1.id] != A2.votes[L2.id])
	}
} for exactly 8 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    14 BasicMessage, 15..15 steps expect 1


/*
The message complete sent by l1 will never be activated because
curBallot of master is bigger than msgComplete.prevBal and the
condition msgComplete.prevBal = m.curBallot will never be satisfied.
However, this is a possible instance.
*/
run scenario5{ 
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, v: Value {
		newReconfig[m]; 
		newReconfig[m];
		clientRequest[v];
		allValuesSafeOrOneValueSafe[l2]; 
		completeReconfig[m]; 
		allValuesSafeOrOneValueSafe[l1];
		allValuesSafe[l2];
		phase2B[a1]; 
		phase2B[a2]
    }
} for exactly 7 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    9 BasicMessage, 10..10 steps expect 1


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


//A value was chosen in previous round but no prepare phase is 
//done in future round
run scenario7{
	some m: Master, disjoint l1, l2: Leader, 
		disjoint a1, a2: Acceptor, v: Value {
			newReconfig[m]; 
			allValuesSafeOrOneValueSafe[l1]; 
			completeReconfig[m]; 
			clientRequest[v]; 
			allValuesSafe[l1]; 
			phase2B[a1]; 
			phase2B[a2];
			newReconfig[m]; 
			allValuesSafeOrOneValueSafe[l2];
			completeReconfig[m]
	}
} for exactly 9 Quorum, exactly 2 Leader, 
	exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	10 BasicMessage, 11..11 steps expect 0

/*
The message complete sent by l1 will never be activated because
curBallot of master is bigger than msgComplete.prevBal and the
condition msgComplete.prevBal = m.curBallot will never be satisfied.
However, this is a possible instance.
*/
run scenario8{ 
    some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, v: Value {
		newReconfig[m]; 
		newReconfig[m];
		clientRequest[v];
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
    10 BasicMessage, 11..11 steps expect 0



run scenario9{ 
    eventually some m: Master, disjoint l1, l2: Leader,
        disjoint a1, a2: Acceptor, disjoint v1, v2: Value {
	some disjoint b1, b2, b3: Ballot | gt[b2, b1] and gt[b3, b2] and l1.id = b1 and l2.id = b2
	and a1 + a2 in WQuorum.acceptors and a1 in RQuorum.acceptors
        once {
		newReconfig[m]; 
		clientRequest[v1];
		leaderNewReconfig[l1];
		allValuesSafeOrOneValueSafe[l1]; 
		newReconfig[m];
		completeReconfig[m]; 
		leaderNewReconfig[l2];
		clientRequest[v2];
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
} for exactly 9 Quorum, exactly 2 Leader, 
    exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
    16 BasicMessage, 17..17 steps expect 0


/*****************CHECKS****************************/


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

check ChosenValue for exactly 9 Quorum, 
	exactly 2 Leader, exactly 2 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 18 BasicMessage, 19..19 steps

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

check VotesSafe for exactly 6 Quorum,
	exactly 2 Leader, exactly 2 Acceptor, exactly 3 Ballot, exactly 2 Value, 
	18 BasicMessage, 19..19 steps expect 0

//Only one vote per Ballot (the value is always the same at the ballot x)
pred oneVotePerBallot[b: Ballot]{
	all a1, a2: Acceptor, v1, v2: Value | (votedFor[a1, b, v1] and 
		votedFor[a2, b, v2]) implies v1 = v2
}

assert OneVote {
	always( all b: Ballot | oneVotePerBallot[b])
}

check OneVote for exactly 6 Quorum, 
	exactly 2 Leader, exactly 2 Acceptor, exactly 3 Ballot, 
	exactly 2 Value, 18 BasicMessage, 19..19 steps expect 0

/**********************THEME*****************************/ 
//With theme translation capacity is often exceeded.

enum Event {Nop, NewReconfig, CompleteReconfig,
		Phase1B, Phase2B, LeaderNewReconfig,
		AllValuesSafeOrOneValueSafe, AllValuesSafe, 
		StateTransfer, OneValueSafe, ClientRequest}

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
}


