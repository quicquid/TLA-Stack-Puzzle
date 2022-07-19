------------------------------ MODULE PushPop ------------------------------
\* This formalizes an exercise from a programming course. We are given a stack
\* onto which the letters a to f are pushed in that order. Pop operations may
\* occur anywhere in between the push operations and output the element removed
\* from the top.
\* For some given outputs (P1 - P4) we are looking if there exists a sequence of
\* such push/pop operations that produces this output. In case such a sequence
\* exists we would also like to know how it looks like.
\* 
\* To find the sequence, check if ~P1 is an invariant of the specification. If it is
\* invalidated, the history contains the sequence we are looking for.     

EXTENDS Sequences, TLAPS

VARIABLE stack, history, output, values


Init == /\ stack = <<>>  \* the current state of the stack
        /\ output = <<>> \* the output of the values removed by pop
        /\ history = <<>> \* the sequence of push / pops taken
        /\ values = <<"a", "b", "c", "d", "e", "f">> \* values put on the stack are taken from this sequence

Next == \* push
        \/ /\ values # <<>>         
           /\ history' = history \o <<<<"push", Head(values)>>>>
           /\ values' = Tail(values)
           /\ stack' = <<Head(values)>> \o stack
           /\ UNCHANGED output
        \* pop
        \/ /\ stack # <<>>
           /\ output' = output \o <<Head(stack)>>
           /\ stack'= Tail(stack)
           /\ history' = history \o <<<<"pop", Head(stack)>>>>
           /\ UNCHANGED values
 

Spec == Init /\ [][Next]_<<stack,history,output,values>>

P1 == (output = <<"a", "b", "c", "d", "e", "f">>)
P2 == (output = <<"b", "a", "c", "f", "d", "e">>)
P3 == (output = <<"b", "a", "c", "f", "e", "d">>)
P4 == (output = <<"a", "c", "d", "b", "e", "f">>)


\* Unfinished termination proof -- probably easier to prove <>[] stack = <<>> + action for stack = <<>> instead of deadlock 
Termination == []<>~ENABLED(Next)


LEMMA Spec => Termination
<1> SUFFICES ASSUME Spec PROVE Termination OBVIOUS
<1> values = <<>> /\ stack = <<>> => ~ENABLED(Next) BY PTL DEF Next 
<1> QED
 


\* To produce non-trivial traces: TLCGet("level") < 15


=============================================================================
\* Modification History
\* Last modified Tue Jul 19 22:02:10 CEST 2022 by marty
\* Created Fri Jun 03 17:11:03 CEST 2022 by marty
