----------------------------- MODULE 2_phase_commit_protocol ------------------------------
    EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS RN, RMMAYFAIL, TMMAYFAIL, BACKUPENABLED
RM == 1..RN
\* The set of participating resource managers

(***************************************************************************
The following is a specification of transaction commit that is written
in what is perhaps a more natural PlusCal style than that in module
PTCommit because processes "terminate" rather than "deadlocking".  It
is identical to the algorithm in that module except for two changes:

1. The predicate of the `while' loop has been changed so an RM exists
the loop when it terminates.

2. The RManager process is made a `fair' process, meaning that weak
fairness of is assumed.  Weak fairness means that each RM that is
continuously able to take a step must eventually do so.

 
--algorithm TransactionCommit {
  variable  rmState = [rm \in RM |-> "working"], 
            tmState = "init";
            hasPrimaryFailed = FALSE;
  define {
    canCommit == /\  \A rm \in RM : rmState[rm] \in {"prepared", "failed", "committed"}
    canAbort ==  /\  \A rm \in RM : rmState[rm] # "committed"
  }

  macro Prepare(p) {
    when rmState[p] = "working";
    rmState[p] := "prepared" ;    
   }

  macro Decide(p) {
    either { when   /\ tmState = "commit"
                    /\ rmState[p] = "prepared";
             rmState[p] := "committed";
           };
    or     { when   /\ tmState = "abort"
                    /\ rmState[p] # "committed";
             rmState[p] := "aborted";
           };
    or     { when   /\ rmState[p] = "working";
             rmState[p] := "aborted";
           };
   }

  macro Fail(p) {
         if(RMMAYFAIL) rmState[p] := "failed";
  } 

  fair process (RManager \in RM) {
    RS: while (rmState[self] \in {"working", "prepared"}) { 
      either Prepare(self) or Decide(self) or Fail(self) };
  }
  
  fair process (TManager=0) {
    TS:  either { await /\ canCommit
                        /\ ~hasPrimaryFailed;
                TC: tmState :="commit";
                F1: if(TMMAYFAIL) {tmState := "hidden"; 
                                  hasPrimaryFailed := TRUE}};
                
         or     { await /\ canAbort
                        /\ ~hasPrimaryFailed;
                TA: tmState := "abort"; 
                F2: if(TMMAYFAIL) {tmState := "hidden";
                                  hasPrimaryFailed := TRUE}};
  }
  
  fair process (BTManager=10) {
    BTS:  await /\ BACKUPENABLED 
                /\ hasPrimaryFailed;

         either { await canCommit;
                BTC: tmState :="commit"};
                
         or     { await canAbort;
                BTA: tmState := "abort"}; 
   }
   
}
 
 
*)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, hasPrimaryFailed, pc

(* define statement *)
canCommit == /\  \A rm \in RM : rmState[rm] \in {"prepared", "failed", "committed"}
canAbort ==  /\  \A rm \in RM : rmState[rm] # "committed"


vars == << rmState, tmState, hasPrimaryFailed, pc >>

ProcSet == (RM) \cup {0} \cup {10}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        /\ hasPrimaryFailed = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"
                                        [] self = 10 -> "BTS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ /\ tmState = "commit"
                                      /\ rmState[self] = "prepared"
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ /\ tmState = "abort"
                                      /\ rmState[self] # "committed"
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                \/ /\ /\ rmState[self] = "working"
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                          \/ /\ IF RMMAYFAIL
                                   THEN /\ rmState' = [rmState EXCEPT ![self] = "failed"]
                                   ELSE /\ TRUE
                                        /\ UNCHANGED rmState
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED << tmState, hasPrimaryFailed >>

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ /\ canCommit
               /\ ~hasPrimaryFailed
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ /\ canAbort
               /\ ~hasPrimaryFailed
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState, hasPrimaryFailed >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "F1"]
      /\ UNCHANGED << rmState, hasPrimaryFailed >>

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
                 /\ hasPrimaryFailed' = TRUE
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, hasPrimaryFailed >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED << rmState, hasPrimaryFailed >>

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "hidden"
                 /\ hasPrimaryFailed' = TRUE
            ELSE /\ TRUE
                 /\ UNCHANGED << tmState, hasPrimaryFailed >>
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ F1 \/ TA \/ F2

BTS == /\ pc[10] = "BTS"
       /\ /\ BACKUPENABLED
          /\ hasPrimaryFailed
       /\ \/ /\ canCommit
             /\ pc' = [pc EXCEPT ![10] = "BTC"]
          \/ /\ canAbort
             /\ pc' = [pc EXCEPT ![10] = "BTA"]
       /\ UNCHANGED << rmState, tmState, hasPrimaryFailed >>

BTC == /\ pc[10] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, hasPrimaryFailed >>

BTA == /\ pc[10] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, hasPrimaryFailed >>

BTManager == BTS \/ BTC \/ BTA

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

_Termination == <>(\/ \A rm \in RM : rmState[rm] \in {"failed", "committed","aborted"}
                   \/ \A rm \in RM : rmState[rm] \in {"failed", "aborted"})

_Consistency == \A rm1, rm2 \in RM : ~(/\ rmState[rm1]="aborted"
                                       /\ rmState[rm2]="committed")


=============================================================================
