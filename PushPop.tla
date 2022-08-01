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

EXTENDS Integers, Sequences, WellFoundedInduction, TLAPS

VARIABLE stack, history, output, values

vars == <<stack, history, output, values>>

Values == {"a", "b", "c", "d", "e", "f"}

TypeOK ==
  /\ stack \in Seq(Values)
  /\ output \in Seq(Values)
  /\ values \in Seq(Values)
  /\ history \in Seq({"push", "pop"} \X Values)
\*  /\ Len(stack) + Len(values) <= 6

Init == /\ stack = <<>>  \* the current state of the stack
        /\ output = <<>> \* the output of the values removed by pop
        /\ history = <<>> \* the sequence of push / pops taken
        /\ values = <<"a", "b", "c", "d", "e", "f">> \* values put on the stack are taken from this sequence

Push ==
  /\ values # <<>>         
  /\ history' = history \o <<<<"push", Head(values)>>>>
  /\ values' = Tail(values)
  /\ stack' = <<Head(values)>> \o stack
  /\ output' = output

Pop ==
  /\ stack # <<>>
  /\ output' = output \o <<Head(stack)>>
  /\ stack'= Tail(stack)
  /\ history' = history \o <<<<"pop", Head(stack)>>>>
  /\ values' = values

Next == Push \/ Pop
 

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

P1 == (output = <<"a", "b", "c", "d", "e", "f">>)
P2 == (output = <<"b", "a", "c", "f", "d", "e">>)
P3 == (output = <<"b", "a", "c", "f", "e", "d">>)
P4 == (output = <<"a", "c", "d", "b", "e", "f">>)

LEMMA Typing == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Values
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>1. CASE Push
    BY <2>1 DEF Push, TypeOK, Values
  <2>2. CASE Pop
    BY <2>2 DEF Pop, TypeOK, Values
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, TypeOK
  <2>4. QED
    BY <2>1, <2>2, <2>3, Zenon DEF Next
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Our objective now is to prove that the algorithm terminates, i.e. that  *)
(* from some time onward no step can be taken anymore.                     *)
(*                                                                         *)
(* The core of the proof is to define a measure function whose value       *)
(* decreases with every step. When a minimal value is reached, no step is  *)
(* possible anymore. A suitable measure is the pair of the lengths of the  *)
(* sequences `values' and `stack', ordered lexicographically. The          *)
(* following definitions use operators defined in the standard module      *)
(* WellFoundedInduction.                                                   *)
(***************************************************************************)

Termination == <>[]~ENABLED(<<Next>>_vars)
terminationMeasure == << Len(values), Len(stack) >>

NatPairOrdering == LexPairOrdering(OpToRel(<,Nat), OpToRel(<,Nat), Nat, Nat)

LEMMA WFNatPairOrdering == IsWellFoundedOn(NatPairOrdering, Nat \X Nat)
BY WFLexPairOrdering, NatLessThanWellFounded, Zenon DEF NatPairOrdering

LEMMA TerminationMeasureDecreases ==
  ASSUME TypeOK, Next
  PROVE  /\ terminationMeasure \in Nat \X Nat
         /\ terminationMeasure' \in Nat \X Nat
         /\ <<terminationMeasure', terminationMeasure>> \in NatPairOrdering
BY DEF Next, Push, Pop, TypeOK,
       terminationMeasure, NatPairOrdering, LexPairOrdering, OpToRel

LEMMA EnabledNext == 
  ASSUME TypeOK
  PROVE  (ENABLED <<Next>>_vars) <=> values # << >> \/ stack # << >>
<1>1. <<Next>>_vars <=> Next
  <2>1. <<Next>>_vars => Next
    OBVIOUS
  <2>2. Push => <<Push>>_vars
    BY DEF TypeOK, Push, vars
  <2>3. Pop => <<Pop>>_vars
    BY DEF TypeOK, Pop, vars
  <2>. QED  BY <2>1, <2>2, <2>3 DEF Next
<1>2. (ENABLED <<Next>>_vars) <=> ENABLED Next
  BY <1>1, ENABLEDrules
<1>. QED  BY <1>2, ENABLEDrewrites DEF Next, Push, Pop


THEOREM Spec => Termination
<1>1. Spec => <>~ENABLED <<Next>>_vars
  <2>. DEFINE TSpec == []TypeOK /\ [][Next]_vars /\ WF_vars(Next)
              P(x) == terminationMeasure = x => <>~ENABLED <<Next>>_vars
              Q(x) == [](TSpec => P(x))
  <2>1. \A x \in Nat \X Nat : (\A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : Q(y)) => Q(x)
    <3>. SUFFICES ASSUME NEW x \in Nat \X Nat
                  PROVE  (\A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : Q(y)) => Q(x)
      OBVIOUS
    <3>1. CASE x = <<0,0>>
      <4>1. TypeOK /\ terminationMeasure = x => values = << >> /\ stack = << >>
        BY <3>1 DEF TypeOK, terminationMeasure
      <4>2. TypeOK /\ terminationMeasure = x => ~ENABLED <<Next>>_vars
        BY <4>1, EnabledNext
      <4>. QED  BY <4>2, PTL
    <3>2. CASE x \in (Nat \X Nat) \ {<<0,0>>}
      <4>1. TypeOK /\ terminationMeasure = x /\ [Next]_vars => 
                 \/ (terminationMeasure = x)' 
                 \/ (\E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y)'
        <5>1. TypeOK /\ terminationMeasure = x /\ Next =>
                 (\E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y)'
          BY TerminationMeasureDecreases DEF SetLessThan
        <5>2. terminationMeasure = x /\ UNCHANGED vars => UNCHANGED terminationMeasure
          BY DEF vars, terminationMeasure
        <5>. QED  BY <5>1, <5>2
      <4>2. TypeOK /\ terminationMeasure = x /\ <<Next>>_vars =>
                (\E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y)'
        BY TerminationMeasureDecreases DEF SetLessThan
      <4>3. TypeOK /\ terminationMeasure = x => ENABLED <<Next>>_vars
        BY <3>2, EnabledNext DEF TypeOK, terminationMeasure
      <4>4. [](TSpec => (terminationMeasure = x => <>(TSpec /\ \E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y)))
        BY <4>1, <4>2, <4>3, PTL
      <4>5. (\A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : Q(y))
            => []((TSpec /\ \E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y)
                      => <>~ENABLED <<Next>>_vars)
        <5>1. ((TSpec /\ \E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y) => <>~ENABLED <<Next>>_vars)
              <=> \A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : TSpec => (terminationMeasure = y => <>~ENABLED <<Next>>_vars)
          BY Isa
        <5>2. []((TSpec /\ \E y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : terminationMeasure = y) => <>~ENABLED <<Next>>_vars)
              <=> [](\A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : TSpec => (terminationMeasure = y => <>~ENABLED <<Next>>_vars))
          BY <5>1, PTL
        <5>3. [](\A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : TSpec => (terminationMeasure = y => <>~ENABLED <<Next>>_vars))
              <=> \A y \in SetLessThan(x, NatPairOrdering, Nat \X Nat) : Q(y)
          OBVIOUS
        <5>. QED  BY <5>2, <5>3
      <4>. QED  BY <4>4, <4>5, PTL
    <3>. QED  BY <3>1, <3>2
  <2>2. \A x \in Nat \X Nat : Q(x)
    <3>. HIDE DEF Q
    <3>. QED  BY <2>1, WFInduction, WFNatPairOrdering, IsaM("blast")
  <2>3. ASSUME NEW x \in Nat \X Nat 
        PROVE  TSpec /\ terminationMeasure = x => <>~ENABLED <<Next>>_vars
    <3>1. Q(x)      BY <2>2
    <3>. QED        BY <3>1, PTL
  <2>4. Spec => \E x \in Nat \X Nat : TSpec /\ terminationMeasure = x
    <3>1. Spec => TSpec
      BY Typing, Isa DEF Spec
    <3>2. Init => terminationMeasure \in Nat \X Nat
      BY DEF Init, terminationMeasure
    <3>. QED  BY <3>1, <3>2, Isa DEF Spec
  <2>. QED  BY <2>3, <2>4, Isa
<1>2. Spec => []((~ENABLED <<Next>>_vars) => []~ENABLED <<Next>>_vars)
  <2>1. ~(values # << >> \/ stack # << >>) /\ [Next]_vars => ~(values # << >> \/ stack # << >>)'
    BY DEF Next, Push, Pop, vars
  <2>. QED  BY <2>1, EnabledNext, Typing, PTL DEF Spec
<1>. QED  BY <1>1, <1>2, PTL DEF Termination


\* To produce non-trivial traces: TLCGet("level") < 15


=============================================================================
