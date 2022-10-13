/****************TESTING DIFFERENT SCOPES PAXOS : ACCEPTORS : 3-4 : ********************/
open noMessages

check ChosenValue for 0 Int, exactly 3 Value, 2 Quorum,
	exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 9 Vote, 1.. steps

check ChosenValue for 0 Int, exactly 3 Value, 2 Quorum, 
	exactly 3 Acceptor, exactly 4 Ballot, 
	exactly 12 Vote, 1.. steps

check ChosenValue for 0 Int, exactly 4 Value, 2 Quorum, 
	exactly 3 Acceptor, exactly 3 Ballot, 
	exactly 12 Vote, 1.. steps

check ChosenValue for 0 Int, exactly 3 Value, 3 Quorum, 
	exactly 4 Acceptor, exactly 3 Ballot, 
	exactly 9 Vote, 1.. steps
