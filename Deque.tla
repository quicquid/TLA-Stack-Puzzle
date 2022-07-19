------------------------------ MODULE Deque ------------------------------
\* This formalizes an exercise from a programming course. We are given a deque
\* that has been initialized with the letters a to f. We track the sequence of
\* values generated by the remove first / remove last operations.
\* The question is if the sequences P1 - P4 can be generated this way.  
\* To find such a the sequence, check if ~PN is an invariant of the specification.
\* If it is invalidated, the history contains the sequence we are looking for.
\* Otherwise, the sequence is impossible to create.     

EXTENDS Sequences, Naturals, TLAPS

Last(s) == s[Len(s)]
AllButLast(s) == CASE s # << >> -> [i \in 1..(Len(s)-1) |-> s[i]]


VARIABLE deque, history, output


Init == /\ deque =  <<1, 2, 3, 4, 5, 6>>  \* the current state of the deque
        /\ output = <<>> \* the output of the values removed by pop
        /\ history = <<>> \* the sequence of remove first / last taken

Next == \* remove first
        \/ /\ deque # <<>>         
           /\ deque' = Tail(deque)
           /\ output' = output \o <<Head(deque)>>
           /\ history' = history \o <<<<"remove first", Head(deque)>>>>
        \* remove last
        \/ /\ deque # <<>>
           /\ deque'= AllButLast(deque)
           /\ output' = output \o <<Last(deque)>>
           /\ history' = history \o <<<<"remove last", Last(deque)>>>>
        \/ deque = <<>> /\ UNCHANGED <<deque, output, history>>
 

Spec == Init /\ [][Next]_<<deque,history,output>>

P1 == (output = <<1, 6, 5, 2, 4, 3>>) \* possible sequence
P2 == (output = <<2, 1, 3, 4, 6, 5>>) \* impossible sequence
P3 == (output = <<1, 2, 6, 4, 5, 3>>) \* possible sequence
P4 == (output = <<6, 5, 1, 4, 3, 2>>) \* possible sequence



=============================================================================
\* Modification History
\* Last modified Tue Jul 19 21:59:50 CEST 2022 by marty
\* Created Fri Jun 03 17:11:03 CEST 2022 by marty