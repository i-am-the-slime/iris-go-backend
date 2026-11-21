----------------------------- MODULE EventLoop -----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Mutation

Main == "main"
Fiber == "fiber"
Resolver == "resolver"
Workers == {"worker1", "worker2"}
Nobody == "nobody"

Processes == {Main, Fiber, Resolver} \cup Workers

VARIABLES held, holder, queue, drainer, postponed, signalled, pending, running, pc, done, waiting

variables == <<held, holder, queue, drainer, postponed, signalled, pending, running, pc, done,
    waiting>>

Init ==
    /\ held = TRUE
    /\ holder = Main
    /\ queue = <<>>
    /\ drainer = Nobody
    /\ postponed = <<>>
    /\ signalled = {}
    /\ pending = Cardinality(Workers)
    /\ running = [process \in Processes |-> process = Main]
    /\ pc = [process \in Processes |->
                CASE process = Main -> "launch"
                  [] process = Fiber -> "start"
                  [] process = Resolver -> "idle"
                  [] OTHER -> "schedule"]
    /\ done = FALSE
    /\ waiting = FALSE

Goto(process, label) == pc' = [pc EXCEPT ![process] = label]

Runs(process, inPureScript) == running' = [running EXCEPT ![process] = inPureScript]

Release ==
    IF queue # <<>>
    THEN /\ holder' = Head(queue)
         /\ queue' = Tail(queue)
         /\ signalled' = signalled \cup {Head(queue)}
         /\ UNCHANGED <<held, drainer, postponed>>
    ELSE IF drainer # Nobody
    THEN /\ holder' = drainer
         /\ drainer' = Nobody
         /\ queue' = postponed
         /\ postponed' = <<>>
         /\ signalled' = signalled \cup {drainer}
         /\ UNCHANGED held
    ELSE /\ held' = FALSE
         /\ holder' = Nobody
         /\ UNCHANGED <<queue, drainer, postponed, signalled>>

Schedule(process) ==
    IF ~held
    THEN /\ held' = TRUE
         /\ holder' = process
         /\ signalled' = signalled \cup {process}
         /\ UNCHANGED queue
    ELSE /\ queue' = Append(queue, process)
         /\ UNCHANGED <<held, holder, signalled>>

Woken(process) ==
    /\ process \in signalled
    /\ signalled' = signalled \ {process}

Launch ==
    /\ pc[Main] = "launch"
    /\ drainer' = Main
    /\ postponed' = queue
    /\ queue' = <<>>
    /\ holder' = Fiber
    /\ signalled' = signalled \cup {Fiber}
    /\ Runs(Main, FALSE)
    /\ Goto(Main, "drained")
    /\ UNCHANGED <<held, pending, done, waiting>>

Drained ==
    /\ pc[Main] = "drained"
    /\ Woken(Main)
    /\ Runs(Main, TRUE)
    /\ Goto(Main, "await")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, pending, done, waiting>>

AwaitRelease ==
    /\ pc[Main] = "await"
    /\ Release
    /\ Runs(Main, FALSE)
    /\ Goto(Main, "idle")
    /\ UNCHANGED <<pending, done, waiting>>

AwaitIdle ==
    /\ pc[Main] = "idle"
    /\ ~held
    /\ queue = <<>>
    /\ pending = 0
    /\ held' = TRUE
    /\ holder' = Main
    /\ Runs(Main, TRUE)
    /\ Goto(Main, "exited")
    /\ UNCHANGED <<queue, drainer, postponed, signalled, pending, done, waiting>>

FiberStarts ==
    /\ pc[Fiber] = "start"
    /\ Woken(Fiber)
    /\ Runs(Fiber, TRUE)
    /\ Goto(Fiber, "register")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, pending, done, waiting>>

Register ==
    /\ pc[Fiber] = "register"
    /\ pending' = IF Mutation = "NoHold" THEN pending ELSE pending + 1
    /\ pc' = [pc EXCEPT ![Fiber] = "check", ![Resolver] = "complete"]
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, signalled, running, done, waiting>>

Check ==
    /\ pc[Fiber] = "check"
    /\ IF done
       THEN /\ queue' = Append(queue, Fiber)
            /\ Goto(Fiber, "suspend")
            /\ UNCHANGED waiting
       ELSE IF Mutation = "LostWakeup"
       THEN /\ Goto(Fiber, "wait")
            /\ UNCHANGED <<queue, waiting>>
       ELSE /\ waiting' = TRUE
            /\ Goto(Fiber, "suspend")
            /\ UNCHANGED queue
    /\ UNCHANGED <<held, holder, drainer, postponed, signalled, pending, running, done>>

Wait ==
    /\ pc[Fiber] = "wait"
    /\ waiting' = TRUE
    /\ Goto(Fiber, "suspend")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, signalled, pending, running, done>>

Suspend ==
    /\ pc[Fiber] = "suspend"
    /\ Release
    /\ Runs(Fiber, FALSE)
    /\ Goto(Fiber, "resume")
    /\ UNCHANGED <<pending, done, waiting>>

Resume ==
    /\ pc[Fiber] = "resume"
    /\ Woken(Fiber)
    /\ Runs(Fiber, TRUE)
    /\ Goto(Fiber, "finish")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, pending, done, waiting>>

FiberFinishes ==
    /\ pc[Fiber] = "finish"
    /\ Release
    /\ Runs(Fiber, FALSE)
    /\ Goto(Fiber, "done")
    /\ UNCHANGED <<pending, done, waiting>>

Complete ==
    /\ pc[Resolver] = "complete"
    /\ done' = TRUE
    /\ Goto(Resolver, IF waiting THEN "schedule" ELSE "retire")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, signalled, pending, running, waiting>>

ScheduleFiber ==
    /\ pc[Resolver] = "schedule"
    /\ IF Mutation = "ResolverRunsFiber"
       THEN /\ signalled' = signalled \cup {Fiber}
            /\ UNCHANGED <<held, holder, queue>>
       ELSE Schedule(Fiber)
    /\ Goto(Resolver, "retire")
    /\ UNCHANGED <<drainer, postponed, pending, running, done, waiting>>

Retire ==
    /\ pc[Resolver] = "retire"
    /\ pending' = IF Mutation = "NoHold" THEN pending ELSE pending - 1
    /\ Goto(Resolver, "done")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, signalled, running, done, waiting>>

TurnSchedules(worker) ==
    /\ pc[worker] = "schedule"
    /\ IF Mutation = "TurnSkipsBaton"
       THEN /\ signalled' = signalled \cup {worker}
            /\ UNCHANGED <<held, holder, queue>>
       ELSE Schedule(worker)
    /\ Goto(worker, "take")
    /\ UNCHANGED <<drainer, postponed, pending, running, done, waiting>>

TurnRuns(worker) ==
    /\ pc[worker] = "take"
    /\ Woken(worker)
    /\ Runs(worker, TRUE)
    /\ Goto(worker, "release")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, pending, done, waiting>>

TurnReleases(worker) ==
    /\ pc[worker] = "release"
    /\ IF Mutation = "TurnSkipsBaton"
       THEN UNCHANGED <<held, holder, queue, drainer, postponed, signalled>>
       ELSE Release
    /\ Runs(worker, FALSE)
    /\ Goto(worker, "retire")
    /\ UNCHANGED <<pending, done, waiting>>

TurnRetires(worker) ==
    /\ pc[worker] = "retire"
    /\ pending' = pending - 1
    /\ Goto(worker, "done")
    /\ UNCHANGED <<held, holder, queue, drainer, postponed, signalled, running, done, waiting>>

Finished ==
    /\ pc[Main] = "exited"
    /\ UNCHANGED variables

Next ==
    \/ Launch \/ Drained \/ AwaitRelease \/ AwaitIdle
    \/ FiberStarts \/ Register \/ Check \/ Wait \/ Suspend \/ Resume \/ FiberFinishes
    \/ Complete \/ ScheduleFiber \/ Retire
    \/ \E worker \in Workers :
        TurnSchedules(worker) \/ TurnRuns(worker) \/ TurnReleases(worker) \/ TurnRetires(worker)
    \/ Finished

Spec == Init /\ [][Next]_variables

OnePureScriptRunner == Cardinality({process \in Processes : running[process]}) <= 1

BatonHolderIsKnown == held <=> holder # Nobody

AwaitWaitsForEveryone ==
    pc[Main] = "exited" => \A process \in Processes \ {Main} : pc[process] = "done"

=============================================================================
