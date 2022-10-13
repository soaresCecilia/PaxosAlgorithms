/***************MultiPaxos with Message Box******************/


/******************MODULE*********************/

open util/ordering[Ballot] as Bal
open util/ordering[Slot] as Slt
open util/ternary


abstract sig Role {}

sig Acceptor extends Role {
	var aBal : lone Ballot,
	var aVoted: Ballot -> Slot -> Value
}

sig Proposer extends Role {
	var pBal: one Ballot 
}

sig Quorum {
	acceptors : some Acceptor
}

sig Slot {}

sig Value {}

sig Ballot {}

//Messages that will be exchanged
abstract sig Message {
	bal: one Ballot,
	from: one Role
}

var sig MsgBox in Message {}

//Different types of messages
sig M1A extends Message{}

sig M1B extends Message{
	voted: Ballot -> Slot -> Value
}

sig M2A extends Message{ 
	propSV: Slot-> Value  
}

sig M2B extends Message{
	propSV: Slot-> Value 
}

sig Preempt extends Message{
	to: one Role
}

//no messages with repeated slot
fact noSlotRepeated {
	always (all s: Slot, m: M2B | lone  s.(m.propSV))
	always (all s: Slot, m:M2A | lone s.(m.propSV))
}

//Initial State
fact Init {
	no aBal
	no aVoted
	some Proposer.pBal
	no MsgBox 
}

//Disjoint Proposers have distinct set of ballots
fact SetBallotProposer {
	all disjoint p1, p2: Proposer | no p1.pBal & p2.pBal 
}


//Next-state actions
fact Next {
	always (nop or
		some p: Proposer | phase1A[p] or 
		phase2A[p] or preempt[p] or
		some a: Acceptor | phase1B[a] or phase2B[a]
	)
}

fact Quorums {
	all x,y : Quorum | some x.acceptors & y.acceptors
	all a: Acceptor | some q: Quorum | a in q.acceptors 
}

//Sending a message
pred send[m : Message] {
	MsgBox' = MsgBox + m
}

// PHASE 1 - Prepare 
pred phase1A[p: Proposer] {
		no m1a: M1A & MsgBox | m1a.bal = p.pBal
		some m1a: M1A { 
			m1a.bal = p.pBal
			m1a.from = p 
			send[m1a]
		}
		pBal' = pBal
		aBal' = aBal
		aVoted' = aVoted
}

pred phase1B[a: Acceptor] {
	some m1a: M1A & MsgBox {
		(no a.aBal or Bal/gt[m1a.bal, a.aBal]) implies {
			some m1b: M1B {
				m1b.bal = m1a.bal
				m1b.from = a
				m1b.voted = a.aVoted
				send[m1b]
			}
			aBal' = aBal ++ a->(m1a.bal)
			pBal' = pBal
			aVoted' = aVoted
		}
		else {
			no m: Preempt | m.bal = a.aBal and m.from = a and m.to = m1a.from
			some m: Preempt {
				m.bal = a.aBal
				m.from = a
				m.to = m1a.from
				send[m]
			}

			pBal' = pBal
			aBal' = aBal
			aVoted' = aVoted
		}
	}			
}


/* return the two smaller elements from a set*/
fun min2[s : set Slot] : set Slot {
	let m = min[s] | m + min[s-m]
}

/* return the previous slot of x
x.*prev is the relation that contains all
the predecessors of x and itself
*/
fun nth[s : set Slot, n : Int] : lone Slot {
	{ x : s | #(x.*prev & s) = n }
}

/* return the n smaller elements from a set*/
fun mins[s : set Slot, n : Int] : set Slot {
	{x : s | some i : Int | gte[i,0] and lte[i,n] and x = nth[s,i]}
}


// PHASE 2 - Accept
pred phase2A [p : Proposer] {
	//the same proposer can't send the same message twice
	no m2a: M2A & MsgBox | m2a.bal = p.pBal
	some q : Quorum {
		// M1B stores all 1B msgs with bal = pBal sent by all acceptors from q  
		let M1B = {m1b : M1B & MsgBox | m1b.from in q.acceptors and m1b.bal = p.pBal} | { 
		//maxSV gets from M1B all S->V pairs with the highest ballot
		let maxSV = {s : Slot, v : Value | some b : Ballot | b->s->v in M1B.voted and all b1 : Ballot, v1 : Value | b1->s->v1 in M1B.voted implies Bal/lte[b1,b] } | {
		//unused referres to the number of slots specified on second parameter, and gets the slots that aren't in maxSV
		let unused = mins[Slot - Ballot.(M1B.voted).Value, 1] | { 

			M1B.from = q.acceptors// all acceptor from quorum have to vote in a msg1B

			some m2a: M2A {
				m2a.from = p
				m2a.bal = p.pBal

				//building propSV - it has maxSV and unused slots. However unused slots have one value
				maxSV in m2a.propSV
				all s : Slot, v : Value | s->v in (m2a.propSV - maxSV) implies s in unused
				all s : unused | one s.(m2a.propSV’)			
				send[m2a]
			}
		}}}
	}
	aBal' = aBal 
	aVoted' = aVoted
	pBal' = pBal
}


//Voting in the proposed value
pred phase2B[a: Acceptor] { 
	some m2a: M2A & MsgBox {
		(no a.aBal or gte[m2a.bal, a.aBal]) implies{
		 	some m2b: M2B {
				m2b.from = a
				m2b.bal = m2a.bal
				m2b.propSV = m2a.propSV
				send[m2b]
			}
			aBal' = aBal ++ a->(m2a.bal)
			aVoted' = aVoted ++ a->(m2a.bal)->(m2a.propSV)	
			//aVoted' = (aVoted - (a->Ballot->(m2a.propSV.Value)->Value)) + a->(m2a.bal)->(m2a.propSV)			
			pBal' = pBal
		}		
		else {
			some m: Preempt {
				m.to = m2a.from
				m.bal = a.aBal
				m.from = a
				send[m]
			}
			pBal' = pBal
			aBal' = aBal
			aVoted' = aVoted
		}
	}
}


pred preempt[p: Proposer] {
	//get de highest ballot of all Proposers and than adds one
	let maximum = Bal/next[Bal/max[Proposer.pBal]] {
		some m: Preempt & MsgBox{ 
			m.to = p
			Bal/gt[m.bal, p.pBal]
			pBal' = pBal ++ p->maximum
		}	
	}
	aBal' = aBal
	aVoted' = aVoted
	MsgBox' = MsgBox
}

//System stuttering
pred nop {
	aBal' = aBal
	aVoted' = aVoted
	pBal' = pBal
	MsgBox' = MsgBox
}

/********************RUNS**************************/



//choosing values in two rounds - don't forget to set phase2A to one slot
run scenario1 {
	some q: Quorum | all a: Acceptor | a in q.acceptors
	all s: Slot | some v: Value | eventually chosen[s, v]
} for exactly 2 Value, exactly 1 Quorum, exactly 2 Acceptor, exactly 2 Ballot,
	exactly 2 Slot, exactly 2 Proposer, 11 Message, 12..12 steps expect 1 

//choosing values from two slots at same time - here phase2A selects two slot at once
run scenario2{
	some q: Quorum, disjoint a1, a2: q.acceptors, p1: Proposer {
			phase1A[p1]; 
			phase1B[a1];
			phase1B[a2];
			phase2A[p1];
			phase2B[a1];
			phase2B[a2]
	}
} for exactly 2 Value, exactly 1 Quorum, exactly 2 Acceptor, exactly 1 Ballot,
	 exactly 2 Slot, exactly 1 Proposer, 6 Message, 7..7 steps expect 1 

//some acceptor sends M2B withou receiving M1A
run scenario3{
	some disjoint a1, a2, a3: Acceptor, p1: Proposer {
		eventually some disjoint q1, q2: Quorum | a1 + a2 in q1.acceptors and
			a1 + a3 in q2.acceptors
		once {
			phase1A[p1]; 
			phase1B[a1];
			phase1B[a2];
			phase2A[p1];
			phase2B[a1];
			phase2B[a3]
		}
	}
} for exactly 2 Value, exactly 2 Quorum, exactly 3 Acceptor, exactly 1 Ballot,
	 exactly 2 Slot, exactly 1 Proposer, 6 Message, 7..7 steps expect 1 

//some acceptor preempt message
run scenario4 {
	eventually some q: Quorum, disjoint a1, a2: q.acceptors, disjoint p1, p2: Proposer,
		disjoint b1, b2, b3: Ballot {
			a1.aBal = b2 
			a2.aBal = b2 
			gt[b2,b1]
			gt[b3, b2]
			(p1.pBal = b1 and p2.pBal = b2)
			once {
				phase1A[p2];
				phase1B[a1];
				phase1B[a2];
				phase1A[p1];
				phase1B[a1];
				preempt[p1]
			}
	}		
} for  1 Value, 1 Quorum, 2 Acceptor, 3 Ballot,
		2 Slot, 2 Proposer, 6 Message, 7..7 steps expect 1 


run scenario5 {
	eventually some disjoint a1, a2: Acceptor, disjoint p1, p2: Proposer,
		disjoint  b1, b2: Ballot, disjoint q1, q2: Quorum {
			a1 in q1.acceptors
			a1 + a2 in q2.acceptors
			Bal/gt[b2, b1]
			p1.pBal = b1
			p2.pBal = b2
		once {
			phase1A[p1]; 
			phase1B[a1];
			phase2A[p1];
			phase2B[a1];
			phase1A[p2]; 
			phase1B[a2];
			phase1B[a1];
			phase2A[p2];
			phase2B[a2];
			phase2B[a1];
			a1.aVoted' = a2.aVoted'
		}
	}
} for exactly 2 Value, exactly 2 Quorum, exactly 2 Acceptor, exactly 2 Ballot,
	 exactly 2 Slot, exactly 2 Proposer, 10 Message, 11..11 steps expect 1


//some quorum choose different values expect 0
run scenario6{
	some q: Quorum, disjoint a1, a2: q.acceptors, p1: Proposer {
			phase1A[p1]; 
			phase1B[a1];
			phase1B[a2];
			phase2A[p1];
			phase2B[a1];
			phase2B[a2];
			a1.aVoted' !=  a2.aVoted' 
	}
} for exactly 2 Value, exactly 1 Quorum, exactly 2 Acceptor, exactly 1 Ballot,
	 exactly 2 Slot, exactly 1 Proposer, 6 Message, 8..8 steps expect 0


//no repeated M2A
run scenario7 {
	some q: Quorum, disjoint a1, a2: q.acceptors, p1: Proposer {
			phase1A[p1]; 
			phase1B[a1];
			phase1B[a2];
			phase2A[p1];
			phase2A[p1]
	}
} for exactly 1 Value, exactly 1 Quorum, exactly 2 Acceptor, exactly 2 Ballot,
	 exactly 2 Slot, exactly 1 Proposer, 5 Message, 6..6 steps expect 0


/***************************CHECKS***************************/


//Exists some ballot b such that ChosenIn holds.
pred chosen[s: Slot, v: Value] {
	some b: Ballot | chosenIn[b, s, v]
}

//Exists some quorum such that each acceptor VotedForIn holds
pred chosenIn[b: Ballot, s: Slot, v: Value] {
	some q: Quorum | all a: q.acceptors | votedForIn[a, b, s, v]
}

//VotedForIn holds if Acceptor a has voted value v for slot s in ballot b
pred votedForIn[a: Acceptor, b: Ballot, s: Slot, v: Value] {
	some m2b: M2B & MsgBox {
		m2b.from = a
		m2b.bal = b
		s->v in m2b.propSV
	}
}


assert Safe {
          always (all v1, v2: Value, s: Slot | (chosen[s, v1] and chosen[s, v2]) implies v1 = v2)
 }


assert VotedInv {
	always (all a: Acceptor, b: Ballot, s: Slot, v: Value | votedForIn[a,b,s,v]
			implies safeAt[b,s,v])
}

check Safe for exactly 2 Value, exactly 1																		s Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, exactly 2 Proposer, exactly 2 Slot, 14 Message, 
	15..15 steps expect 0


assert VotedOnce {
	always (all disjoint a1, a2: Acceptor, b: Ballot, s: Slot, v1,v2: Value | votedForIn[a1,b,s,v1] and 
		votedForIn[a2,b,s,v2] implies v1=v2)
}

check VotedOnce for exactly 2 Value, exactly 1 Quorum, 
	exactly 2 Acceptor, exactly 2 Ballot, exactly 2 Proposer,
 	exactly 2 Slot, 13 Message, 14..14 steps


/*
No value except possibly v has been or will be chosen 
in any ballot lower than b for slot s 
*/
pred safeAt[b: Ballot, s: Slot, v: Value] {
	all c: prevs[b] | some q: Quorum | all a: q.acceptors | 
		votedForIn[a, c, s, v] or wontVoteIn[a, c, s]
}


/*
An acceptor a has seen a higher ballot than b and did not and will not vote any value in b
for slot s
*/
pred wontVoteIn[a: Acceptor, b: Ballot, s: Slot] {
	some a.aBal and Bal/gt[a.aBal, b]
	all v: Value | not votedForIn[a, b, s, v]
}


/*
MaxBalInSlot selects among set of elements in a.aVoted 
(all acceptors' votes) with slot s, the highest ballot or none if no element has slot s.  
*/
fun maxBalInSlot[t: set (Ballot->Slot->Value), s: Slot]: lone Ballot {
	Bal/max[{b : Ballot | s in mid[t] and b in dom[t]}]
}



/*******Inv Acceptors*********/


//Invariants about acceptors
pred accInv[a: Acceptor] {
	no a.aBal implies no a.aVoted
		
	//a.aBal is higher than or equal to the ballot number of each triple in a.aVoted and a has voted each triple in a.aVoted
	all b: Ballot, s: Slot, v: Value | b->s->v in a.aVoted 
				implies (Bal/gte[a.aBal, b] and votedForIn[a, b, s, v])	

	/* if a has voted any value v for slot s in ballot b, then there is some triple in aVoted such that
	aVoted.bal >= b and aVoted.slot = s 
	*/
	all b: Ballot, s: Slot, v: Value {
		votedForIn[a, b, s, v] implies {		
			some b2: Ballot, s2: Slot, v2: Value {
				b2->s2->v2 in a.aVoted implies (Bal/gte[b2, b] and s2 = s)
			}
		}
	}

	//a has not voted for a value in any ballot higher than the highest it has seen per slot
	all b: Ballot, s: Slot, v: Value | (s in mid[a.aVoted] and Bal/gt[b, maxBalInSlot[a.aVoted, s]])
							implies not votedForIn[a, b, s, v]
}


assert  Acc {
	always(all a: Acceptor | always accInv[a])
}

check Acc for exactly 2 Value, 1 Quorum, exactly 2 Acceptor, 
	exactly 2 Ballot, exactly 2 Slot, exactly 2 Proposer, 
	exactly 10 Message, 11..11 steps


/*
The following invariante is for a 1B msg m, sent from an acceptor a, 
where m.bal is the bal number of 1a msg that m reply of, and 
m.Voted is the value of (m.from).aVoted when m was sent 
*/
pred invM1B[m: M1B]{ 
		//all m1B's ballots that were sent have to be lower or equal to acceptor's aBal 
		Bal/lte[m.bal, aBal[m.from]]

		//m.from has voted every triple in the set m.voted seen by m.from
		all b: Ballot, s: Slot, v: Value {
			b->s->v in m.voted implies votedForIn[m.from, b, s, v]
		}

		/*for each slot s and ballot b higher than the highest ballot that m.from
		has voted in for slot s, and lower than the ballot in m, m.from has not 
		voted any value v for slot s in ballot b 
		*/
		all b: Ballot, s: Slot, v: Value | (s in mid[m.voted] and Bal/gt[b, maxBalInSlot[m.voted, s]] and 
				Bal/lt[b, m.bal]) implies not votedForIn[m.from, b, s, v]
}


assert Msg1B {
	always (all m1b: M1B & MsgBox | invM1B[m1b])
}

check Msg1B for exactly 2 Value, 1 Quorum, exactly 2 Acceptor, exactly 2 Ballot, 
	exactly 2 Slot, exactly 1 Proposer, exactly 12 Message, 13..13 steps



pred invM2A[m: M2A] {
	//safety for each proposal 2A
	all s: Slot, v: Value | s->v in m.propSV implies safeAt[m.bal, s, v]

	//two proposals with the same slot must be the same proposal
	all s1, s2: Slot, v1, v2: Value | (s1->v1 in m.propSV and s2->v2 in m.propSV and s1 = s2) 
						implies s1->v1 = s2->v2 
	//for each slot there is at most one proposal
	all m2a: M2A & MsgBox | m2a.bal = m.bal implies m2a = m
}	

assert Msg2A {
	always (all m2a: M2A & MsgBox | invM2A[m2a])
}

check Msg2A for exactly 2 Value, 1 Quorum, exactly 2 Acceptor, exactly 2 Ballot, 
	exactly 2 Slot, exactly 2 Proposer, exactly 12 Message, 13..13 steps


pred invM2B[m: M2B] {
	//there exists a 2a msg with the same ballot and same set of proposals as m
	some m2a: M2A | m2a.bal = m.bal and m2a.propSV = m.propSV
	//ballot of m msg 2B is no higher than the highest ballot seen by m.from
	Bal/lte[m.bal, aBal[m.from]]  
}

assert Msg2B {
	always (all m2b: M2B & MsgBox | invM2B[m2b])
}

check Msg2B for 3 Value, 1 Quorum, exactly 2 Acceptor, exactly 3 Ballot, 
	exactly 3 Slot, exactly 2 Proposer, exactly 13 Message, 14..14 steps



/***************************THEME******************************/



enum Event {Nop, Phase1A, Phase1B, Phase2A, Phase2B, Preemption} // event names

/*auxiliary relation, which should be populated 
when the nop event happens
a subset of Event that will be populated 
(by the name Stutter) if the stutter predicate 
is true, and empty otherwise.*/
fun nop_happens : set Event {
  { e: Nop | nop }
}


/*
This event takes a proposer as a parameter. In this case, 
the auxiliary relation has to take that into account and
return the proposer that was taken.
*/
fun phase1A_happens : Event -> Proposer {
  { e: Phase1A, p: Proposer | phase1A[p] }
}

/*
Phase 1B is referred to an acceptor.
*/
fun phase1B_happens : Event -> Acceptor {
  { e: Phase1B, a: Acceptor | phase1B[a] }
}

/*
This event takes a Proposer as parameter.
*/
fun phase2A_happens : Event -> Proposer {
  { e: Phase2A, p: Proposer | phase2A[p] }
}

/*
Last phase takes an Acceptor as parameter.
*/
fun phase2B_happens : Event -> Acceptor {
  { e: Phase2B, a: Acceptor | phase2B[a] }
}

/*
Preempt phase takes a proposer as paramenter.
*/
fun preempt_happens : Event -> Proposer {
  { e: Preemption, p: Proposer | preempt[p] }
}

/*Enhancement to show event parameters as labels.*/
fun events : set Event {
  nop_happens + phase1A_happens.Proposer + phase1B_happens.Acceptor 
	+ phase2B_happens.Acceptor + phase2A_happens.Proposer
	+ preempt_happens.Proposer
}



//Verification of theme - only one event in each state
fact trace {
  always some events
}


check singleEvent {
  always one events
} for 1..20 steps


	


