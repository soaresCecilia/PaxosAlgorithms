/*************************Paxos Abstract****************/
/*MODULES*/
open util/ordering[Ballot]


/*SIGNATURES*/
sig Acceptor {
	var votes : Ballot -> lone Value,
	var maxBal : lone Ballot
}

sig Quorum {
	quorum : some Acceptor
}

sig Value {}

sig Ballot {}



/*FACTS*/
fact Quorums {
	all disj q1, q2 : Quorum | some q1.quorum & q2.quorum
}

fact Init {
	no votes
	no maxBal
}

fact Next {
	always (some a: Acceptor, b: Ballot, v:Value {
		increaseMaxBal[a,b] or voteFor[a, b, v] or nop
	})
}

/*PREDICATES*/
pred nop {
	votes' = votes
	maxBal' = maxBal
}

pred increaseMaxBal[a: Acceptor, b: Ballot] {
	no a.maxBal or gt[b, a.maxBal]
	maxBal' = maxBal ++ a->b
	votes' = votes
}


pred showsSafeAt[q: Quorum, b: Ballot, v: Value]{
	all a: q.quorum | gte[a.maxBal, b] and some a.maxBal

	b = first or some c : prevs[b] {
		some a : q.quorum | a.votes[c] = v
		all d : c.nexts & b.prevs, a : q.quorum | no a.votes[d]
	}
}


pred voteFor(a: Acceptor, b: Ballot, v: Value){
	no a.maxBal or lte[a.maxBal,b]
	no a.votes[b]
	all c: Acceptor - a | no c.votes[b] - v
	some q: Quorum | showsSafeAt[q,b,v]
	votes' = votes + a->b->v
	maxBal' = maxBal ++ a->b
}


/*********************************************/
//SAFETY PROPERTIES


//Only one vote per Ballot
pred oneVotePerBallot{
	all a: Acceptor, b: Ballot, v: Value | lone (b->v & a.votes)
}


assert ConsistencyInVotes {
	always oneVotePerBallot
}

check ConsistencyInVotes

/* No other value than v has been or can ever be chosen in any
ballot less than b  
*/
pred safeAt[b: Ballot, v: Value] {
	all c: prevs[b] | some q: Quorum | all a: q.quorum { 
		c->v in a.votes or (some a.maxBal and gt[a.maxBal,c] and no a.votes[c])
	}
}

assert SafeAt {
	all a : Acceptor, b : Ballot, v : Value | always (b->v in a.votes implies safeAt[b,v])
}

check SafeAt


//A quorum of acceptors have all voted for v in ballot b.
pred chosenAt[b: Ballot, v: Value] {
	some q: Quorum | all a: q.quorum |  b->v in a.votes
}

//Choosing at most one value
fun chosenValue : lone Value {
	{v:Value | some b:Ballot | chosenAt[b,v]}
}


assert ChosenValue {
	always lone chosenValue
}   

/*CHECK*/
check ChosenValue

/*RUNS*/
run Chosen {
	all q : Quorum | some disj a1, a2 : Acceptor | 
	    a1 + a2 in q.quorum
	eventually some chosenValue
}

run scenario {
	all q : Quorum | some disj a1, a2 : Acceptor | a1 + a2 in q.quorum
	all a: Acceptor | some q: Quorum | a in q.quorum
	eventually some chosenValue
} for 2 but exactly 5 Acceptor, exactly 3 Quorum



/*THEME FUNCTIONS*/
fun voters : set Acceptor{
	votes.Value.Ballot
}


fun chosenQuorum : lone Quorum{
	{q:Quorum | all a : q.quorum | some b:Ballot, v:Value | 
		b->v in a.votes}
}

fun chosenVotes : Acceptor -> Value {
	{a : Acceptor , v:Value | some q:Quorum, b:Ballot | 
		a in q.quorum and chosenAt[b,v] and q in chosenQuorum}
}






