---- MODULE ecu_switch ----

EXTENDS Sequences, TLC, Integers

CONSTANT ECUs, FaultTypes, FaultBehaviors, MonitoringTypes, S


(*--fair algorithm ecuswitch
variables
  fault_ecu = "main",
  faults = [fault_ecu_name : {fault_ecu}, fault_type : FaultTypes, fault_behavior : FaultBehaviors, fault_monitoring : {"self_monitoring"}],
  self_faults \in faults \X faults,
  \*self_faults = << [fault_ecu_name |-> fault_ecu, fault_type |-> "non_self_recoverable", fault_behavior |-> "emergency_stop"], [fault_ecu_name |-> fault_ecu, fault_type |-> "non_self_recoverable", fault_behavior |-> "emergency_stop"]>>,
  self_fault_queue = [ecu \in ECUs |-> IF ecu = fault_ecu THEN self_faults ELSE <<>>],
  voter_queue = <<>>,
  StopOperators = [ecu : ECUs, behavior : FaultBehaviors],
  emergency_stop_operator_queue = [ecu \in ECUs |-> <<>>],
  EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"},
  comfortable_stop_operator_queue = [ecu \in ECUs |-> <<>>],
  ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"},
  MRMs = {"main_mrm", "sub_mrm", "supervisor_mrm"},
  mrm_queue = [ecu \in ECUs |-> <<>>],
  SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"},
  voter_status = "none",
  vehicle_queue = <<>>,
  vehicle_status = "running",
  switch = [state |-> "main"];
  stop_operator_status;

define
  VehicleStopped == <>(vehicle_status = "succeeded")
end define;

\* operate emergency_stop or comfortable_stop in each ECU
process emergency_stop_operator \in EmergencyStopOperators
variables
  fault,
  emergency_stop_operator_ecu =
    IF self = "main_emergency_stop_operator"
    THEN "main"
    ELSE IF self = "sub_emergency_stop_operator"
    THEN "sub"
    ELSE "supervisor";
begin
  OPERATE_STOP:
    while TRUE do
      await emergency_stop_operator_queue[emergency_stop_operator_ecu] /= <<>>;
      fault := Head(emergency_stop_operator_queue[emergency_stop_operator_ecu]);
      emergency_stop_operator_queue[emergency_stop_operator_ecu]:= Tail(emergency_stop_operator_queue[emergency_stop_operator_ecu]);
      \* Execute emergency_stop function for the ECU
      \* The details of emergency_stop function for the ECU is omitted here
      if switch.state = emergency_stop_operator_ecu then
        vehicle_queue := Append(vehicle_queue, fault);
        \*await vehicle_status = "stopped";
        \*stop_operator_status := "succeeded";
        if emergency_stop_operator_ecu = "supervisor" then
          voter_queue := Append(voter_queue, fault);
        end if;
      end if;
    end while;
end process;

process comfortable_stop_operator \in ComfortableStopOperators
variables
  fault,
  comfortable_stop_operator_ecu =
    IF self = "main_comfortable_stop_operator"
    THEN "main"
    ELSE "sub";
begin
  OPERATE_STOP:
    while TRUE do
      await comfortable_stop_operator_queue[comfortable_stop_operator_ecu] /= <<>>;
      fault := Head(comfortable_stop_operator_queue[comfortable_stop_operator_ecu]);
      comfortable_stop_operator_queue[comfortable_stop_operator_ecu]:= Tail(comfortable_stop_operator_queue[comfortable_stop_operator_ecu]);
      \* Execute emergency_stop function for the ECU
      \* The details of emergency_stop function for the ECU is omitted here
      if switch.state = comfortable_stop_operator_ecu then
        vehicle_queue := Append(vehicle_queue, fault);
        \*await vehicle_status = "stopped";
        \*stop_operator_status := "succeeded";
      end if;
    end while;
end process;


\* decide stop behavior in each ECU
process mrm \in MRMs
variables
  fault,
  emergency_stop_exists = FALSE,
  comfortable_stop_exists = FALSE,
  mrm_ecu =
    IF self = "main_mrm"
    THEN "main"
    ELSE IF self = "sub_mrm"
    THEN "sub"
    ELSE "supervisor";

begin
  MRM:
    while TRUE do
      await mrm_queue[mrm_ecu] /= <<>>;
      fault := Head(mrm_queue[mrm_ecu]);
      mrm_queue[mrm_ecu] := Tail(mrm_queue[mrm_ecu]);

      if mrm_ecu = "supervisor" then
        if ~emergency_stop_exists then
          emergency_stop_exists := TRUE;
          emergency_stop_operator_queue[mrm_ecu] := Append(emergency_stop_operator_queue[mrm_ecu], fault);
        end if;
      else
        if fault.fault_behavior = "emergency_stop" /\ ~emergency_stop_exists then
          emergency_stop_exists := TRUE;
          emergency_stop_operator_queue[mrm_ecu] := Append(emergency_stop_operator_queue[mrm_ecu], fault);
        elsif fault.fault_behavior = "comfortable_stop" /\ ~comfortable_stop_exists /\ ~emergency_stop_exists then
          comfortable_stop_exists := TRUE;
          comfortable_stop_operator_queue[mrm_ecu] := Append(comfortable_stop_operator_queue[mrm_ecu], fault);
        end if;
      end if;
    end while;
end process;

process self_monitoring \in SelfMonitorings
variables
  self_fault,
  self_monitoring_ecu =
    IF self = "main_self_monitoring"
    THEN "main"
    ELSE IF self = "sub_self_monitoring"
    THEN "sub"
    ELSE "supervisor";
begin
  SelfMonitoring:
    while self_fault_queue[self_monitoring_ecu] /= <<>> do
      self_fault := Head(self_fault_queue[self_monitoring_ecu]);
      self_fault_queue[self_monitoring_ecu] := Tail(self_fault_queue[self_monitoring_ecu]);
        if self_fault.fault_type = "self_recoverable" then
          \* Queue the fault for MRM function
          mrm_queue[self_monitoring_ecu] := Append(mrm_queue[self_monitoring_ecu], self_fault);
          \* Pass the fault to Voter's queue
        end if;
        voter_queue := Append(voter_queue, self_fault);
    end while;
end process;


\* decide which ECU to operate MRM
process voter = "voter"
variables
  fault;
  is_switch_needed = FALSE;
begin
  Voter:
    while
      vehicle_status /= "succeeded" \/ is_switch_needed do

      await voter_queue /= <<>> \/ vehicle_status = "succeeded";
      if voter_queue = <<>> then
        \* Do nothing
      else
        fault := Head(voter_queue);
        voter_queue := Tail(voter_queue);
        if is_switch_needed then
          switch.state := IF fault.fault_ecu_name = "main" THEN "sub" ELSE "main";
          is_switch_needed := FALSE;
          mrm_queue[switch.state] := Append(mrm_queue[switch.state], fault);
        else
          if fault.fault_ecu_name = switch.state then
            if fault.fault_type = "self_recoverable" then
              (* Do nothing *)
            elsif fault.fault_type = "non_self_recoverable" then
              switch.state := "supervisor";
              mrm_queue[switch.state] := Append(mrm_queue[switch.state], fault);
              if fault.fault_behavior = "comfortable_stop" then
                is_switch_needed := TRUE;
              end if;
            end if;
          elsif fault.fault_ecu_name /= switch.state then
            mrm_queue[switch.state] := Append(mrm_queue[switch.state], fault);
          end if;
        end if;
      end if;
    end while;
end process;

process vehicle = "vehicle"
variables
  fault;
begin
  Vehicle:
    while TRUE do
      await vehicle_queue /= <<>>;
      fault := Head(vehicle_queue);
      vehicle_queue := Tail(vehicle_queue);
      vehicle_status := "succeeded";
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "359cc10b" /\ chksum(tla) = "bded1d99")
\* Label OPERATE_STOP of process emergency_stop_operator at line 46 col 5 changed to OPERATE_STOP_
\* Process variable fault of process emergency_stop_operator at line 37 col 3 changed to fault_
\* Process variable fault of process comfortable_stop_operator at line 65 col 3 changed to fault_c
\* Process variable fault of process mrm at line 90 col 3 changed to fault_m
\* Process variable fault of process voter at line 151 col 3 changed to fault_v
CONSTANT defaultInitValue
VARIABLES fault_ecu, faults, self_faults, self_fault_queue, voter_queue,
          StopOperators, emergency_stop_operator_queue,
          EmergencyStopOperators, comfortable_stop_operator_queue,
          ComfortableStopOperators, MRMs, mrm_queue, SelfMonitorings,
          voter_status, vehicle_queue, vehicle_status, switch,
          stop_operator_status, pc

(* define statement *)
VehicleStopped == <>(vehicle_status = "succeeded")

VARIABLES fault_, emergency_stop_operator_ecu, fault_c,
          comfortable_stop_operator_ecu, fault_m, emergency_stop_exists,
          comfortable_stop_exists, mrm_ecu, self_fault, self_monitoring_ecu,
          fault_v, is_switch_needed, fault

vars == << fault_ecu, faults, self_faults, self_fault_queue, voter_queue,
           StopOperators, emergency_stop_operator_queue,
           EmergencyStopOperators, comfortable_stop_operator_queue,
           ComfortableStopOperators, MRMs, mrm_queue, SelfMonitorings,
           voter_status, vehicle_queue, vehicle_status, switch,
           stop_operator_status, pc, fault_, emergency_stop_operator_ecu,
           fault_c, comfortable_stop_operator_ecu, fault_m,
           emergency_stop_exists, comfortable_stop_exists, mrm_ecu,
           self_fault, self_monitoring_ecu, fault_v, is_switch_needed, fault
        >>

ProcSet == (EmergencyStopOperators) \cup (ComfortableStopOperators) \cup (MRMs) \cup (SelfMonitorings) \cup {"voter"} \cup {"vehicle"}

Init == (* Global variables *)
        /\ fault_ecu = "main"
        /\ faults = [fault_ecu_name : {fault_ecu}, fault_type : FaultTypes, fault_behavior : FaultBehaviors, fault_monitoring : {"self_monitoring"}]
        /\ self_faults \in faults \X faults
        /\ self_fault_queue = [ecu \in ECUs |-> IF ecu = fault_ecu THEN self_faults ELSE <<>>]
        /\ voter_queue = <<>>
        /\ StopOperators = [ecu : ECUs, behavior : FaultBehaviors]
        /\ emergency_stop_operator_queue = [ecu \in ECUs |-> <<>>]
        /\ EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"}
        /\ comfortable_stop_operator_queue = [ecu \in ECUs |-> <<>>]
        /\ ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"}
        /\ MRMs = {"main_mrm", "sub_mrm", "supervisor_mrm"}
        /\ mrm_queue = [ecu \in ECUs |-> <<>>]
        /\ SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"}
        /\ voter_status = "none"
        /\ vehicle_queue = <<>>
        /\ vehicle_status = "running"
        /\ switch = [state |-> "main"]
        /\ stop_operator_status = defaultInitValue
        (* Process emergency_stop_operator *)
        /\ fault_ = [self \in EmergencyStopOperators |-> defaultInitValue]
        /\ emergency_stop_operator_ecu = [self \in EmergencyStopOperators |-> IF self = "main_emergency_stop_operator"
                                                                              THEN "main"
                                                                              ELSE IF self = "sub_emergency_stop_operator"
                                                                              THEN "sub"
                                                                              ELSE "supervisor"]
        (* Process comfortable_stop_operator *)
        /\ fault_c = [self \in ComfortableStopOperators |-> defaultInitValue]
        /\ comfortable_stop_operator_ecu = [self \in ComfortableStopOperators |-> IF self = "main_comfortable_stop_operator"
                                                                                  THEN "main"
                                                                                  ELSE "sub"]
        (* Process mrm *)
        /\ fault_m = [self \in MRMs |-> defaultInitValue]
        /\ emergency_stop_exists = [self \in MRMs |-> FALSE]
        /\ comfortable_stop_exists = [self \in MRMs |-> FALSE]
        /\ mrm_ecu = [self \in MRMs |-> IF self = "main_mrm"
                                        THEN "main"
                                        ELSE IF self = "sub_mrm"
                                        THEN "sub"
                                        ELSE "supervisor"]
        (* Process self_monitoring *)
        /\ self_fault = [self \in SelfMonitorings |-> defaultInitValue]
        /\ self_monitoring_ecu = [self \in SelfMonitorings |-> IF self = "main_self_monitoring"
                                                               THEN "main"
                                                               ELSE IF self = "sub_self_monitoring"
                                                               THEN "sub"
                                                               ELSE "supervisor"]
        (* Process voter *)
        /\ fault_v = defaultInitValue
        /\ is_switch_needed = FALSE
        (* Process vehicle *)
        /\ fault = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in EmergencyStopOperators -> "OPERATE_STOP_"
                                        [] self \in ComfortableStopOperators -> "OPERATE_STOP"
                                        [] self \in MRMs -> "MRM"
                                        [] self \in SelfMonitorings -> "SelfMonitoring"
                                        [] self = "voter" -> "Voter"
                                        [] self = "vehicle" -> "Vehicle"]

OPERATE_STOP_(self) == /\ pc[self] = "OPERATE_STOP_"
                       /\ emergency_stop_operator_queue[emergency_stop_operator_ecu[self]] /= <<>>
                       /\ fault_' = [fault_ EXCEPT ![self] = Head(emergency_stop_operator_queue[emergency_stop_operator_ecu[self]])]
                       /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![emergency_stop_operator_ecu[self]] = Tail(emergency_stop_operator_queue[emergency_stop_operator_ecu[self]])]
                       /\ IF switch.state = emergency_stop_operator_ecu[self]
                             THEN /\ vehicle_queue' = Append(vehicle_queue, fault_'[self])
                                  /\ IF emergency_stop_operator_ecu[self] = "supervisor"
                                        THEN /\ voter_queue' = Append(voter_queue, fault_'[self])
                                        ELSE /\ TRUE
                                             /\ UNCHANGED voter_queue
                             ELSE /\ TRUE
                                  /\ UNCHANGED << voter_queue, vehicle_queue >>
                       /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP_"]
                       /\ UNCHANGED << fault_ecu, faults, self_faults,
                                       self_fault_queue, StopOperators,
                                       EmergencyStopOperators,
                                       comfortable_stop_operator_queue,
                                       ComfortableStopOperators, MRMs,
                                       mrm_queue, SelfMonitorings,
                                       voter_status, vehicle_status, switch,
                                       stop_operator_status,
                                       emergency_stop_operator_ecu, fault_c,
                                       comfortable_stop_operator_ecu, fault_m,
                                       emergency_stop_exists,
                                       comfortable_stop_exists, mrm_ecu,
                                       self_fault, self_monitoring_ecu,
                                       fault_v, is_switch_needed, fault >>

emergency_stop_operator(self) == OPERATE_STOP_(self)

OPERATE_STOP(self) == /\ pc[self] = "OPERATE_STOP"
                      /\ comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]] /= <<>>
                      /\ fault_c' = [fault_c EXCEPT ![self] = Head(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                      /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![comfortable_stop_operator_ecu[self]] = Tail(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                      /\ IF switch.state = comfortable_stop_operator_ecu[self]
                            THEN /\ vehicle_queue' = Append(vehicle_queue, fault_c'[self])
                            ELSE /\ TRUE
                                 /\ UNCHANGED vehicle_queue
                      /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP"]
                      /\ UNCHANGED << fault_ecu, faults, self_faults,
                                      self_fault_queue, voter_queue,
                                      StopOperators,
                                      emergency_stop_operator_queue,
                                      EmergencyStopOperators,
                                      ComfortableStopOperators, MRMs,
                                      mrm_queue, SelfMonitorings, voter_status,
                                      vehicle_status, switch,
                                      stop_operator_status, fault_,
                                      emergency_stop_operator_ecu,
                                      comfortable_stop_operator_ecu, fault_m,
                                      emergency_stop_exists,
                                      comfortable_stop_exists, mrm_ecu,
                                      self_fault, self_monitoring_ecu, fault_v,
                                      is_switch_needed, fault >>

comfortable_stop_operator(self) == OPERATE_STOP(self)

MRM(self) == /\ pc[self] = "MRM"
             /\ mrm_queue[mrm_ecu[self]] /= <<>>
             /\ fault_m' = [fault_m EXCEPT ![self] = Head(mrm_queue[mrm_ecu[self]])]
             /\ mrm_queue' = [mrm_queue EXCEPT ![mrm_ecu[self]] = Tail(mrm_queue[mrm_ecu[self]])]
             /\ IF mrm_ecu[self] = "supervisor"
                   THEN /\ IF ~emergency_stop_exists[self]
                              THEN /\ emergency_stop_exists' = [emergency_stop_exists EXCEPT ![self] = TRUE]
                                   /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![mrm_ecu[self]] = Append(emergency_stop_operator_queue[mrm_ecu[self]], fault_m'[self])]
                              ELSE /\ TRUE
                                   /\ UNCHANGED << emergency_stop_operator_queue,
                                                   emergency_stop_exists >>
                        /\ UNCHANGED << comfortable_stop_operator_queue,
                                        comfortable_stop_exists >>
                   ELSE /\ IF fault_m'[self].fault_behavior = "emergency_stop" /\ ~emergency_stop_exists[self]
                              THEN /\ emergency_stop_exists' = [emergency_stop_exists EXCEPT ![self] = TRUE]
                                   /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![mrm_ecu[self]] = Append(emergency_stop_operator_queue[mrm_ecu[self]], fault_m'[self])]
                                   /\ UNCHANGED << comfortable_stop_operator_queue,
                                                   comfortable_stop_exists >>
                              ELSE /\ IF fault_m'[self].fault_behavior = "comfortable_stop" /\ ~comfortable_stop_exists[self] /\ ~emergency_stop_exists[self]
                                         THEN /\ comfortable_stop_exists' = [comfortable_stop_exists EXCEPT ![self] = TRUE]
                                              /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![mrm_ecu[self]] = Append(comfortable_stop_operator_queue[mrm_ecu[self]], fault_m'[self])]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << comfortable_stop_operator_queue,
                                                              comfortable_stop_exists >>
                                   /\ UNCHANGED << emergency_stop_operator_queue,
                                                   emergency_stop_exists >>
             /\ pc' = [pc EXCEPT ![self] = "MRM"]
             /\ UNCHANGED << fault_ecu, faults, self_faults, self_fault_queue,
                             voter_queue, StopOperators,
                             EmergencyStopOperators, ComfortableStopOperators,
                             MRMs, SelfMonitorings, voter_status,
                             vehicle_queue, vehicle_status, switch,
                             stop_operator_status, fault_,
                             emergency_stop_operator_ecu, fault_c,
                             comfortable_stop_operator_ecu, mrm_ecu,
                             self_fault, self_monitoring_ecu, fault_v,
                             is_switch_needed, fault >>

mrm(self) == MRM(self)

SelfMonitoring(self) == /\ pc[self] = "SelfMonitoring"
                        /\ IF self_fault_queue[self_monitoring_ecu[self]] /= <<>>
                              THEN /\ self_fault' = [self_fault EXCEPT ![self] = Head(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ self_fault_queue' = [self_fault_queue EXCEPT ![self_monitoring_ecu[self]] = Tail(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ IF self_fault'[self].fault_type = "self_recoverable"
                                         THEN /\ mrm_queue' = [mrm_queue EXCEPT ![self_monitoring_ecu[self]] = Append(mrm_queue[self_monitoring_ecu[self]], self_fault'[self])]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED mrm_queue
                                   /\ voter_queue' = Append(voter_queue, self_fault'[self])
                                   /\ pc' = [pc EXCEPT ![self] = "SelfMonitoring"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << self_fault_queue,
                                                   voter_queue, mrm_queue,
                                                   self_fault >>
                        /\ UNCHANGED << fault_ecu, faults, self_faults,
                                        StopOperators,
                                        emergency_stop_operator_queue,
                                        EmergencyStopOperators,
                                        comfortable_stop_operator_queue,
                                        ComfortableStopOperators, MRMs,
                                        SelfMonitorings, voter_status,
                                        vehicle_queue, vehicle_status, switch,
                                        stop_operator_status, fault_,
                                        emergency_stop_operator_ecu, fault_c,
                                        comfortable_stop_operator_ecu, fault_m,
                                        emergency_stop_exists,
                                        comfortable_stop_exists, mrm_ecu,
                                        self_monitoring_ecu, fault_v,
                                        is_switch_needed, fault >>

self_monitoring(self) == SelfMonitoring(self)

Voter == /\ pc["voter"] = "Voter"
         /\ IF vehicle_status /= "succeeded" \/ is_switch_needed
               THEN /\ voter_queue /= <<>> \/ vehicle_status = "succeeded"
                    /\ IF voter_queue = <<>>
                          THEN /\ UNCHANGED << voter_queue, mrm_queue, switch,
                                               fault_v, is_switch_needed >>
                          ELSE /\ fault_v' = Head(voter_queue)
                               /\ voter_queue' = Tail(voter_queue)
                               /\ IF is_switch_needed
                                     THEN /\ switch' = [switch EXCEPT !.state = IF fault_v'.fault_ecu_name = "main" THEN "sub" ELSE "main"]
                                          /\ is_switch_needed' = FALSE
                                          /\ mrm_queue' = [mrm_queue EXCEPT ![switch'.state] = Append(mrm_queue[switch'.state], fault_v')]
                                     ELSE /\ IF fault_v'.fault_ecu_name = switch.state
                                                THEN /\ IF fault_v'.fault_type = "self_recoverable"
                                                           THEN /\ UNCHANGED << mrm_queue,
                                                                                switch,
                                                                                is_switch_needed >>
                                                           ELSE /\ IF fault_v'.fault_type = "non_self_recoverable"
                                                                      THEN /\ switch' = [switch EXCEPT !.state = "supervisor"]
                                                                           /\ mrm_queue' = [mrm_queue EXCEPT ![switch'.state] = Append(mrm_queue[switch'.state], fault_v')]
                                                                           /\ IF fault_v'.fault_behavior = "comfortable_stop"
                                                                                 THEN /\ is_switch_needed' = TRUE
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED is_switch_needed
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED << mrm_queue,
                                                                                           switch,
                                                                                           is_switch_needed >>
                                                ELSE /\ IF fault_v'.fault_ecu_name /= switch.state
                                                           THEN /\ mrm_queue' = [mrm_queue EXCEPT ![switch.state] = Append(mrm_queue[switch.state], fault_v')]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED mrm_queue
                                                     /\ UNCHANGED << switch,
                                                                     is_switch_needed >>
                    /\ pc' = [pc EXCEPT !["voter"] = "Voter"]
               ELSE /\ pc' = [pc EXCEPT !["voter"] = "Done"]
                    /\ UNCHANGED << voter_queue, mrm_queue, switch, fault_v,
                                    is_switch_needed >>
         /\ UNCHANGED << fault_ecu, faults, self_faults, self_fault_queue,
                         StopOperators, emergency_stop_operator_queue,
                         EmergencyStopOperators,
                         comfortable_stop_operator_queue,
                         ComfortableStopOperators, MRMs, SelfMonitorings,
                         voter_status, vehicle_queue, vehicle_status,
                         stop_operator_status, fault_,
                         emergency_stop_operator_ecu, fault_c,
                         comfortable_stop_operator_ecu, fault_m,
                         emergency_stop_exists, comfortable_stop_exists,
                         mrm_ecu, self_fault, self_monitoring_ecu, fault >>

voter == Voter

Vehicle == /\ pc["vehicle"] = "Vehicle"
           /\ vehicle_queue /= <<>>
           /\ fault' = Head(vehicle_queue)
           /\ vehicle_queue' = Tail(vehicle_queue)
           /\ vehicle_status' = "succeeded"
           /\ pc' = [pc EXCEPT !["vehicle"] = "Vehicle"]
           /\ UNCHANGED << fault_ecu, faults, self_faults, self_fault_queue,
                           voter_queue, StopOperators,
                           emergency_stop_operator_queue,
                           EmergencyStopOperators,
                           comfortable_stop_operator_queue,
                           ComfortableStopOperators, MRMs, mrm_queue,
                           SelfMonitorings, voter_status, switch,
                           stop_operator_status, fault_,
                           emergency_stop_operator_ecu, fault_c,
                           comfortable_stop_operator_ecu, fault_m,
                           emergency_stop_exists, comfortable_stop_exists,
                           mrm_ecu, self_fault, self_monitoring_ecu, fault_v,
                           is_switch_needed >>

vehicle == Vehicle

Next == voter \/ vehicle
           \/ (\E self \in EmergencyStopOperators: emergency_stop_operator(self))
           \/ (\E self \in ComfortableStopOperators: comfortable_stop_operator(self))
           \/ (\E self \in MRMs: mrm(self))
           \/ (\E self \in SelfMonitorings: self_monitoring(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

====
