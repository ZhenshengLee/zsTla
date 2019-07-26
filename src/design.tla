





------------------------------- MODULE design -------------------------------

EXTENDS TLC, Sequences, Integers, FiniteSets

CONSTANTS Dispatcher, Executors, FaultDetector



Inputs == <<1,2,3>>

ExpectedResult == 14



PermSeqs(S) ==

    {f \in [1..Cardinality(S) -> S]:

        \A y \in S: \E x \in 1..Cardinality(S): f[x]=y

    }



Index(seq, elem) == CHOOSE i \in 1..Len(seq): seq[i] = elem



AlwaysGood == CHOOSE e \in SUBSET Executors: Cardinality(e) = 1

MaybeFault == Executors \ AlwaysGood



(*

--algorithm par_executor

{

    variables

        wqueue = [w \in Executors |-> <<>>],

        dqueue = <<>>;

    procedure do_calc()

    {

    Do:

        await wqueue[self] /= <<>>;

        with(value = Head(wqueue[self]))

        {

            wqueue[self] := Tail(wqueue[self]);

            dqueue := Append(dqueue, [cmd |-> "result", value |-> value*value]);

        };

        goto Do;

\*        return;

    };



    fair process(fault_detector = FaultDetector)

    variable faults = {};

    {

    Detect:

        with(e \in MaybeFault \ faults)

        {

            dqueue := Append(dqueue, [cmd |-> "fault", worker |-> e]);

            faults := faults \union {e};

        };

        goto Detect;

    }



    fair process(dispatcher = Dispatcher)

    variable

        task_num = Len(Inputs),

        assignments = [e \in Executors |-> <<>>];

        final = 0;

    {

    Scatter:

\*        取出来的是一个排列

        with(sched = CHOOSE  s \in PermSeqs(Executors):TRUE)

        {

            wqueue := [e \in Executors |-> <<Inputs[Index(sched, e)]>>];

            assignments := wqueue;

        };

    Gather:

        await dqueue /= <<>>;

\*        final := final + Head(dqueue);

\*        dqueue := Tail(dqueue);

\*        task_num := task_num - 1;

\*        if(task_num > 0)

\*        {

\*            goto Gather;

\*        };

        with(msg = Head(dqueue))

        {

            dqueue := Tail(dqueue);

            if(msg.cmd = "result")

            {

                final := final + msg.value;

                task_num := task_num - 1;

                if(task_num = 0)

                {

                    goto Finish;

                }

            }

            else if(msg.cmd = "fault")

            {

                with(to \in AlwaysGood)

                {

\*                    wqueue[to] := wqueue[to] \o <<2>>;

                    wqueue[to] := wqueue[to] \o assignments[msg.worker];

                }

            }

        };

    Again:

        goto Gather;

    Finish:

        assert final = ExpectedResult;

    };



    fair process(always_good \in AlwaysGood)

    {

    AGStart:

        call do_calc();

    };

    process(maybe_fault \in MaybeFault)

    {

    MBFStart:

        call do_calc();

    };



\*    fair process(executor \in Executors)

\*    {

\*    variable value = 0;

\*    Do:

\*        value = 0;

\*        await wqueue[self] /= <<>>;

\*        value := Head(wqueue[self]);

\*        wqueue[self] := Tail(wqueue[self]);

\*        dqueue := Append(dqueue, value*value);

\*    }



}

*)

\* BEGIN TRANSLATION

VARIABLES wqueue, dqueue, pc, stack, faults, task_num, assignments, final



vars == << wqueue, dqueue, pc, stack, faults, task_num, assignments, final >>



ProcSet == {FaultDetector} \cup {Dispatcher} \cup (AlwaysGood) \cup (MaybeFault)



Init == (* Global variables *)

        /\ wqueue = [w \in Executors |-> <<>>]

        /\ dqueue = <<>>

        (* Process fault_detector *)

        /\ faults = {}

        (* Process dispatcher *)

        /\ task_num = Len(Inputs)

        /\ assignments = [e \in Executors |-> <<>>]

        /\ final = 0

        /\ stack = [self \in ProcSet |-> << >>]

        /\ pc = [self \in ProcSet |-> CASE self = FaultDetector -> "Detect"

                                        [] self = Dispatcher -> "Scatter"

                                        [] self \in AlwaysGood -> "AGStart"

                                        [] self \in MaybeFault -> "MBFStart"]



Do(self) == /\ pc[self] = "Do"

            /\ wqueue[self] /= <<>>

            /\ LET value == Head(wqueue[self]) IN

                 /\ wqueue' = [wqueue EXCEPT ![self] = Tail(wqueue[self])]

                 /\ dqueue' = Append(dqueue, [cmd |-> "result", value |-> value*value])

            /\ pc' = [pc EXCEPT ![self] = "Do"]

            /\ UNCHANGED << stack, faults, task_num, assignments, final >>



do_calc(self) == Do(self)



Detect == /\ pc[FaultDetector] = "Detect"

          /\ \E e \in MaybeFault \ faults:

               /\ dqueue' = Append(dqueue, [cmd |-> "fault", worker |-> e])

               /\ faults' = (faults \union {e})

          /\ pc' = [pc EXCEPT ![FaultDetector] = "Detect"]

          /\ UNCHANGED << wqueue, stack, task_num, assignments, final >>



fault_detector == Detect



Scatter == /\ pc[Dispatcher] = "Scatter"

           /\ LET sched == CHOOSE  s \in PermSeqs(Executors):TRUE IN

                /\ wqueue' = [e \in Executors |-> <<Inputs[Index(sched, e)]>>]

                /\ assignments' = wqueue'

           /\ pc' = [pc EXCEPT ![Dispatcher] = "Gather"]

           /\ UNCHANGED << dqueue, stack, faults, task_num, final >>



Gather == /\ pc[Dispatcher] = "Gather"

          /\ dqueue /= <<>>

          /\ LET msg == Head(dqueue) IN

               /\ dqueue' = Tail(dqueue)

               /\ IF msg.cmd = "result"

                     THEN /\ final' = final + msg.value

                          /\ task_num' = task_num - 1

                          /\ IF task_num' = 0

                                THEN /\ pc' = [pc EXCEPT ![Dispatcher] = "Finish"]

                                ELSE /\ pc' = [pc EXCEPT ![Dispatcher] = "Again"]

                          /\ UNCHANGED wqueue

                     ELSE /\ IF msg.cmd = "fault"

                                THEN /\ \E to \in AlwaysGood:

                                          wqueue' = [wqueue EXCEPT ![to] = wqueue[to] \o assignments[msg.worker]]

                                ELSE /\ TRUE

                                     /\ UNCHANGED wqueue

                          /\ pc' = [pc EXCEPT ![Dispatcher] = "Again"]

                          /\ UNCHANGED << task_num, final >>

          /\ UNCHANGED << stack, faults, assignments >>



Again == /\ pc[Dispatcher] = "Again"

         /\ pc' = [pc EXCEPT ![Dispatcher] = "Gather"]

         /\ UNCHANGED << wqueue, dqueue, stack, faults, task_num, assignments,

                         final >>



Finish == /\ pc[Dispatcher] = "Finish"

          /\ Assert(final = ExpectedResult,

                    "Failure of assertion at line 95, column 9.")

          /\ pc' = [pc EXCEPT ![Dispatcher] = "Done"]

          /\ UNCHANGED << wqueue, dqueue, stack, faults, task_num, assignments,

                          final >>



dispatcher == Scatter \/ Gather \/ Again \/ Finish



AGStart(self) == /\ pc[self] = "AGStart"

                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_calc",

                                                          pc        |->  "Done" ] >>

                                                      \o stack[self]]

                 /\ pc' = [pc EXCEPT ![self] = "Do"]

                 /\ UNCHANGED << wqueue, dqueue, faults, task_num, assignments,

                                 final >>



always_good(self) == AGStart(self)



MBFStart(self) == /\ pc[self] = "MBFStart"

                  /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "do_calc",

                                                           pc        |->  "Done" ] >>

                                                       \o stack[self]]

                  /\ pc' = [pc EXCEPT ![self] = "Do"]

                  /\ UNCHANGED << wqueue, dqueue, faults, task_num,

                                  assignments, final >>



maybe_fault(self) == MBFStart(self)



Next == fault_detector \/ dispatcher

           \/ (\E self \in ProcSet: do_calc(self))

           \/ (\E self \in AlwaysGood: always_good(self))

           \/ (\E self \in MaybeFault: maybe_fault(self))

           \/ (* Disjunct to prevent deadlock on termination *)

              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)



Spec == /\ Init /\ [][Next]_vars

        /\ WF_vars(fault_detector)

        /\ WF_vars(dispatcher)

        /\ \A self \in AlwaysGood : WF_vars(always_good(self)) /\ WF_vars(do_calc(self))



Termination == <>(\A self \in ProcSet: pc[self] = "Done")



\* END TRANSLATION



Liveness == <>[](final = ExpectedResult)



=============================================================================

\* Modification History

\* Last modified Sat May 25 16:36:49 CST 2019 by 10222446

\* Created Sat May 25 13:44:34 CST 2019 by 10222446

