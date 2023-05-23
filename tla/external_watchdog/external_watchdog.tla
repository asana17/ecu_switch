---- MODULE external_watchdog ----

EXTENDS Sequences, TLC, Integers

CONSTANT ECUs

(*--fair algorithm external_watchdog
variables
  fault_ecu = "sub",
  detected_ecu = "none",
  efaults = [fault_ecu_name : {fault_ecu}],
  external_faults \in efaults \X efaults,
  mistake_fault = << [fault_ecu_name |-> "sub"] >>;
  external_fault_queue = [ecu \in ECUs |-> IF ecu /= fault_ecu THEN external_faults ELSE mistake_fault],
  ExternalWatchdogs = {"main_external_watchdog", "sub_external_watchdog", "supervisor_external_watchdog"},
  external_fault_detector_queue = <<>>,
  voter_watchdog_status = [ecu \in ECUs |-> "none"];

define
  ExternalFaultDetected == <>(detected_ecu = fault_ecu)
end define;

macro check_external_fault_ecu(external_fault_ecu)
begin
  if voter_watchdog_status["main"] = voter_watchdog_status["sub"] then
    external_fault_ecu := voter_watchdog_status["main"];
  elsif voter_watchdog_status["main"] = voter_watchdog_status["supervisor"] then
    external_fault_ecu := voter_watchdog_status["main"];
  elsif voter_watchdog_status["sub"] = voter_watchdog_status["supervisor"] then
    external_fault_ecu := voter_watchdog_status["sub"];
  else
    external_fault_ecu := "none";
  end if;
end macro;

macro reset_voter_watchdog_status()
begin
  voter_watchdog_status := [ecu \in ECUs |-> "none"];
end macro;


process external_watchdog \in ExternalWatchdogs
variables
  fault,
  external_watchdog_ecu =
    IF self = "main_external_watchdog"
    THEN "main"
    ELSE IF self = "sub_external_watchdog"
    THEN "sub"
    ELSE "supervisor";
begin
  ExternalWatchdog:
    while external_fault_queue[external_watchdog_ecu] /= <<>> do
      fault := Head(external_fault_queue[external_watchdog_ecu]);
      external_fault_queue[external_watchdog_ecu] := Tail(external_fault_queue[external_watchdog_ecu]);
      \* other params are not used in external fault detection
      voter_watchdog_status[external_watchdog_ecu] := fault.fault_ecu_name;
      external_fault_detector_queue := Append(external_fault_detector_queue, "");
    end while;
end process;

process external_fault_detector = "external_fault_detector"
variables
  external_fault_ecu,
  fault;
begin
  ExternalFaultDetector:
    while TRUE do
      await external_fault_detector_queue /= <<>>;
      external_fault_detector_queue := Tail(external_fault_detector_queue);
      \* check external_fault_ecu when voter_watchdog_status is updated
      check_external_fault_ecu(external_fault_ecu);
      if external_fault_ecu /= "none" then
        detected_ecu := external_fault_ecu;
      end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "e2962166" /\ chksum(tla) = "556afc7a")
\* Process variable fault of process external_watchdog at line 44 col 3 changed to fault_
CONSTANT defaultInitValue
VARIABLES fault_ecu, detected_ecu, efaults, external_faults, mistake_fault,
          external_fault_queue, ExternalWatchdogs,
          external_fault_detector_queue, voter_watchdog_status, pc

(* define statement *)
ExternalFaultDetected == <>(detected_ecu = fault_ecu)

VARIABLES fault_, external_watchdog_ecu, external_fault_ecu, fault

vars == << fault_ecu, detected_ecu, efaults, external_faults, mistake_fault,
           external_fault_queue, ExternalWatchdogs,
           external_fault_detector_queue, voter_watchdog_status, pc, fault_,
           external_watchdog_ecu, external_fault_ecu, fault >>

ProcSet == (ExternalWatchdogs) \cup {"external_fault_detector"}

Init == (* Global variables *)
        /\ fault_ecu = "sub"
        /\ detected_ecu = "none"
        /\ efaults = [fault_ecu_name : {fault_ecu}]
        /\ external_faults \in efaults \X efaults
        /\ mistake_fault = << [fault_ecu_name |-> "sub"] >>
        /\ external_fault_queue = [ecu \in ECUs |-> IF ecu /= fault_ecu THEN external_faults ELSE mistake_fault]
        /\ ExternalWatchdogs = {"main_external_watchdog", "sub_external_watchdog", "supervisor_external_watchdog"}
        /\ external_fault_detector_queue = <<>>
        /\ voter_watchdog_status = [ecu \in ECUs |-> "none"]
        (* Process external_watchdog *)
        /\ fault_ = [self \in ExternalWatchdogs |-> defaultInitValue]
        /\ external_watchdog_ecu = [self \in ExternalWatchdogs |-> IF self = "main_external_watchdog"
                                                                   THEN "main"
                                                                   ELSE IF self = "sub_external_watchdog"
                                                                   THEN "sub"
                                                                   ELSE "supervisor"]
        (* Process external_fault_detector *)
        /\ external_fault_ecu = defaultInitValue
        /\ fault = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in ExternalWatchdogs -> "ExternalWatchdog"
                                        [] self = "external_fault_detector" -> "ExternalFaultDetector"]

ExternalWatchdog(self) == /\ pc[self] = "ExternalWatchdog"
                          /\ IF external_fault_queue[external_watchdog_ecu[self]] /= <<>>
                                THEN /\ fault_' = [fault_ EXCEPT ![self] = Head(external_fault_queue[external_watchdog_ecu[self]])]
                                     /\ external_fault_queue' = [external_fault_queue EXCEPT ![external_watchdog_ecu[self]] = Tail(external_fault_queue[external_watchdog_ecu[self]])]
                                     /\ voter_watchdog_status' = [voter_watchdog_status EXCEPT ![external_watchdog_ecu[self]] = fault_'[self].fault_ecu_name]
                                     /\ external_fault_detector_queue' = Append(external_fault_detector_queue, "")
                                     /\ pc' = [pc EXCEPT ![self] = "ExternalWatchdog"]
                                ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                     /\ UNCHANGED << external_fault_queue,
                                                     external_fault_detector_queue,
                                                     voter_watchdog_status,
                                                     fault_ >>
                          /\ UNCHANGED << fault_ecu, detected_ecu, efaults,
                                          external_faults, mistake_fault,
                                          ExternalWatchdogs,
                                          external_watchdog_ecu,
                                          external_fault_ecu, fault >>

external_watchdog(self) == ExternalWatchdog(self)

ExternalFaultDetector == /\ pc["external_fault_detector"] = "ExternalFaultDetector"
                         /\ external_fault_detector_queue /= <<>>
                         /\ external_fault_detector_queue' = Tail(external_fault_detector_queue)
                         /\ IF voter_watchdog_status["main"] = voter_watchdog_status["sub"]
                               THEN /\ external_fault_ecu' = voter_watchdog_status["main"]
                               ELSE /\ IF voter_watchdog_status["main"] = voter_watchdog_status["supervisor"]
                                          THEN /\ external_fault_ecu' = voter_watchdog_status["main"]
                                          ELSE /\ IF voter_watchdog_status["sub"] = voter_watchdog_status["supervisor"]
                                                     THEN /\ external_fault_ecu' = voter_watchdog_status["sub"]
                                                     ELSE /\ external_fault_ecu' = "none"
                         /\ IF external_fault_ecu' /= "none"
                               THEN /\ detected_ecu' = external_fault_ecu'
                               ELSE /\ TRUE
                                    /\ UNCHANGED detected_ecu
                         /\ pc' = [pc EXCEPT !["external_fault_detector"] = "ExternalFaultDetector"]
                         /\ UNCHANGED << fault_ecu, efaults, external_faults,
                                         mistake_fault, external_fault_queue,
                                         ExternalWatchdogs,
                                         voter_watchdog_status, fault_,
                                         external_watchdog_ecu, fault >>

external_fault_detector == ExternalFaultDetector

Next == external_fault_detector
           \/ (\E self \in ExternalWatchdogs: external_watchdog(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

====
