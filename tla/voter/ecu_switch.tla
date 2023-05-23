---- MODULE ecu_switch ----

EXTENDS Sequences, TLC, Integers

CONSTANT ECUs, FaultTypes, FaultBehaviors, S


(*--fair algorithm ecuswitch
variables
  \*fault_ecu = "supervisor",
  fault_ecu \in ECUs,
  faults = [fault_ecu_name : {fault_ecu}, fault_type : FaultTypes, fault_behavior : FaultBehaviors, fault_monitoring : {"self_monitoring"}],
  e_faults = [fault_ecu_name : {fault_ecu}, fault_type: {"non_self_recoverable"}, fault_behavior : {"comfortable_stop"}, fault_monitoring : {"external_monitoring"}],
  self_faults \in faults \X faults \X faults \X faults,
  \*self_faults = << [fault_ecu_name |-> fault_ecu, fault_type |-> "non_self_recoverable", fault_behavior |-> "emergency_stop"], [fault_ecu_name |-> fault_ecu, fault_type |-> "non_self_recoverable", fault_behavior |-> "emergency_stop"]>>,
  self_fault_queue = [ecu \in ECUs |-> IF ecu = fault_ecu THEN self_faults ELSE <<>>],
  \*self_fault_queue = [ecu \in ECUs |-> <<>>],
  voter_queue = <<>>,
  voter_status = "none",
  StopOperators = [ecu : ECUs, behavior : FaultBehaviors],
  emergency_stop_operator_queue = [ecu \in ECUs |-> <<>>],
  EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"},
  comfortable_stop_operator_queue = [ecu \in {"main", "sub"} |-> <<>>],
  ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"},
  EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler"},
  emergency_handler_status = [ecu \in {"main", "sub"} |-> "none"],
  emergency_handler_queue = [ecu \in {"main", "sub"} |-> <<>>],
  SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"},
  vehicle_queue = <<>>,
  vehicle_status = "running",
  switch = [state |-> "main"];
  is_stop_operator_succeeded = FALSE;
  self_recoverable_flag = TRUE;


define
  VehicleStopped == <>(vehicle_status = "stopped")
end define;


macro add_fault_to_stop_operator(stop_operator_ecu, stop_operator_behavior, adding_fault)
begin
  if stop_operator_behavior = "emergency_stop" then
    emergency_stop_operator_queue[stop_operator_ecu] := Append(emergency_stop_operator_queue[stop_operator_ecu], adding_fault);
  else
    comfortable_stop_operator_queue[stop_operator_ecu] := Append(comfortable_stop_operator_queue[stop_operator_ecu], adding_fault);
  end if;
end macro;

\* operate emergency_stop or comfortable_stop in each ECU
process emergency_stop_operator \in EmergencyStopOperators
variables
  fault,
  operator_status = "idle",
  emergency_stop_operator_ecu =
    IF self = "main_emergency_stop_operator"
    THEN "main"
    ELSE IF self = "sub_emergency_stop_operator"
    THEN "sub"
    ELSE "supervisor";
begin
  OPERATE_STOP:
    while operator_status /= "stopped" do
      await emergency_stop_operator_queue[emergency_stop_operator_ecu] /= <<>> \/ (vehicle_status = "emergency_operating" /\ operator_status = "running");
      if vehicle_status = "emergency_operating" /\ operator_status = "running" then
        operator_status := "stopped";
        \* if switch.state = emergency_stop_operator_ecu then
        \* if emergency_stop_operator of fault_ecu not working
        if switch.state = emergency_stop_operator_ecu /\ ~(fault_ecu = emergency_stop_operator_ecu /\ ~self_recoverable_flag) then
          vehicle_queue := Append(vehicle_queue, "stopped");
          is_stop_operator_succeeded := TRUE;
        end if;
      else
        fault := Head(emergency_stop_operator_queue[emergency_stop_operator_ecu]);
        emergency_stop_operator_queue[emergency_stop_operator_ecu]:= Tail(emergency_stop_operator_queue[emergency_stop_operator_ecu]);
        if operator_status = "idle" then
          operator_status := "running";
          if emergency_stop_operator_ecu /= "supervisor" then
            emergency_handler_status[emergency_stop_operator_ecu] := "emergency_operating";
          end if;
          if switch.state = emergency_stop_operator_ecu then
          \* if emergency_stop_operator of fault_ecu not working
          \* if switch.state = emergency_stop_operator_ecu /\ ~(fault_ecu = emergency_stop_operator_ecu /\ ~self_recoverable_flag) then
            vehicle_queue := Append(vehicle_queue, "emergency_operating");
            if emergency_stop_operator_ecu = "supervisor" then
              (*TODO *)
              voter_queue := Append(voter_queue, fault);
            end if;
          end if;
        end if;
      end if;
    end while;
end process;

process comfortable_stop_operator \in ComfortableStopOperators
variables
  fault,
  operator_status = "idle",
  comfortable_stop_operator_ecu =
    IF self = "main_comfortable_stop_operator"
    THEN "main"
    ELSE "sub";
begin
  OPERATE_STOP:
    while operator_status /= "stopped" do
      await comfortable_stop_operator_queue[comfortable_stop_operator_ecu] /= <<>> \/ (vehicle_status = "comfortable_operating" /\ operator_status = "running");
      if vehicle_status = "comfortable_operating" /\ operator_status = "running" then
        operator_status := "stopped";
        \* if switch.state = comfortable_stop_operator_ecu then
        \* if comfortable_stop_operator of fault_ecu not working
        if switch.state = comfortable_stop_operator_ecu /\ ~(fault_ecu = comfortable_stop_operator_ecu /\ ~self_recoverable_flag) then
          emergency_handler_queue[comfortable_stop_operator_ecu] := Append(emergency_handler_queue[comfortable_stop_operator_ecu], "stopped");
        end if;
      else
        fault := Head(comfortable_stop_operator_queue[comfortable_stop_operator_ecu]);
        comfortable_stop_operator_queue[comfortable_stop_operator_ecu]:= Tail(comfortable_stop_operator_queue[comfortable_stop_operator_ecu]);
        if operator_status = "idle" then
          operator_status := "running";
          if switch.state = comfortable_stop_operator_ecu then
          \* if comfortable_stop_operator of fault_ecu not working
          \* if switch.state = comfortable_stop_operator_ecu /\ ~(fault_ecu = comfortable_stop_operator_ecu /\ ~self_recoverable_flag) then
            emergency_handler_queue[comfortable_stop_operator_ecu] := Append(emergency_handler_queue[comfortable_stop_operator_ecu], "comfortable_operating");
          end if;
        end if;
      end if;
    end while;
end process;

process emergency_handler \in EmergencyHandlers
variables
  emergency_handler_ecu =
    IF self = "main_emergency_handler"
    THEN "main"
    ELSE "sub";
begin
  EmergencyHandler:
    while TRUE do
      await emergency_handler_queue[emergency_handler_ecu] /= <<>>;
      (* select to use comfortable_stop_operator result or not*)
      comfortable_stop_operator_operation := Head(emergency_handler_queue[emergency_handler_ecu]);
      emergency_handler_queue[emergency_handler_ecu] := Tail(emergency_handler_queue[emergency_handler_ecu]);
      if emergency_handler_status[emergency_handler_ecu] /= "emergency_operating" then
        (*Cannot overide emergency_stop by comfortable_stop*)
        if switch.state = emergency_handler_ecu then
          vehicle_queue := Append(vehicle_queue, comfortable_stop_operator_operation);
        end if;
        if comfortable_stop_operator_operation = "stopped" then
          is_stop_operator_succeeded := TRUE;
        end if;
      end if;
    end while;
end process;

process self_monitoring \in SelfMonitorings
variables
  fault,
  self_monitoring_ecu =
    IF self = "main_self_monitoring"
    THEN "main"
    ELSE IF self = "sub_self_monitoring"
    THEN "sub"
    ELSE "supervisor";
begin
  SelfMonitoring:
    while self_fault_queue[self_monitoring_ecu] /= <<>> do
      fault := Head(self_fault_queue[self_monitoring_ecu]);
      self_fault_queue[self_monitoring_ecu] := Tail(self_fault_queue[self_monitoring_ecu]);
        if fault.fault_type = "self_recoverable" then
          \* Queue the fault for MRM function
          add_fault_to_stop_operator(self_monitoring_ecu, fault.fault_behavior, fault);
          \* Pass the fault to Voter's queue
        end if;
        voter_queue := Append(voter_queue, fault);
    end while;
end process;

\* decide which ECU to operate MRM
process voter = "voter"
variables
  fault;
  switch_fault;
  external_detected = FALSE;
  is_switched = FALSE;
  comfortable_stop_after_switch = FALSE;
  comfortable_stop_operator_operation;
begin
  Voter:
    while voter_status /= "succeeded" do

      await voter_queue /= <<>> \/ is_stop_operator_succeeded;
      if is_stop_operator_succeeded then
        if comfortable_stop_after_switch then
          comfortable_stop_after_switch := FALSE;
          is_stop_operator_succeeded := FALSE;
          switch.state := IF switch_fault.fault_ecu_name = "main" THEN "sub" ELSE "main";
          add_fault_to_stop_operator(switch.state, "comfortable_stop", switch_fault);
        else
          voter_status := "succeeded";
        end if;
      elsif voter_queue /= <<>> then
        fault := Head(voter_queue);
        voter_queue := Tail(voter_queue);
        if external_detected then
          \* do nothing
        else
          if fault.fault_monitoring = "external_monitoring" then
            external_detected := TRUE;
          end if;
          if fault.fault_ecu_name = switch.state then
            if fault.fault_type = "self_recoverable" then
              (* appropriate stop_operator already running *)
              if fault.fault_behavior = "emergency_stop" then
                voter_status := "emergency_operating";
              end if;
            elsif fault.fault_type = "non_self_recoverable" then
              (* need switch : emergency stop in supervisor first *)
              self_recoverable_flag := FALSE;
              switch.state := "supervisor";
              is_switched := TRUE;
              voter_status := "emergency_operating";
              add_fault_to_stop_operator("supervisor", "emergency_stop", fault);
              if fault.fault_behavior = "comfortable_stop" then
                (* comfortable_stop in ecu with no fault after emergency_stop in supervisor*)
                switch_fault := fault;
                comfortable_stop_after_switch := TRUE;
              end if;
            end if;
          elsif fault.fault_ecu_name /= switch.state then
            (* run stop_operator in ecu connecting to switch *)
            if is_switched then
              (*non_self_recoverable && switch needed fault already occured: already stop_operator running*)
            else
              add_fault_to_stop_operator(switch.state, "comfortable_stop", fault);
            end if;
          end if;
        end if;
      end if;
    end while;
end process;

process vehicle = "vehicle"
variables
  operation;
begin
  Vehicle:
    while TRUE do
      await vehicle_queue /= <<>>;
      (*TODO: emergency_stop and comfortable_stop *)
      operation := Head(vehicle_queue);
      vehicle_queue := Tail(vehicle_queue);
      if operation = "emergency_operating" then
        vehicle_status := "emergency_operating";
      elsif operation = "comfortable_operating" then
        vehicle_status := "comfortable_operating";
      elsif operation = "stopped" then
        vehicle_status := "stopped";
      end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2210c3e8" /\ chksum(tla) = "809cd33b")
\* Label OPERATE_STOP of process emergency_stop_operator at line 63 col 5 changed to OPERATE_STOP_
\* Process variable fault of process emergency_stop_operator at line 53 col 3 changed to fault_
\* Process variable operator_status of process emergency_stop_operator at line 54 col 3 changed to operator_status_
\* Process variable fault of process comfortable_stop_operator at line 97 col 3 changed to fault_c
\* Process variable fault of process self_monitoring at line 156 col 3 changed to fault_s
CONSTANT defaultInitValue
VARIABLES fault_ecu, faults, e_faults, self_faults, self_fault_queue, 
          voter_queue, voter_status, StopOperators, 
          emergency_stop_operator_queue, EmergencyStopOperators, 
          comfortable_stop_operator_queue, ComfortableStopOperators, 
          EmergencyHandlers, emergency_handler_status, 
          emergency_handler_queue, SelfMonitorings, vehicle_queue, 
          vehicle_status, switch, is_stop_operator_succeeded, 
          self_recoverable_flag, pc

(* define statement *)
VehicleStopped == <>(vehicle_status = "stopped")

VARIABLES fault_, operator_status_, emergency_stop_operator_ecu, fault_c, 
          operator_status, comfortable_stop_operator_ecu, 
          emergency_handler_ecu, fault_s, self_monitoring_ecu, fault, 
          switch_fault, external_detected, is_switched, 
          comfortable_stop_after_switch, comfortable_stop_operator_operation, 
          operation

vars == << fault_ecu, faults, e_faults, self_faults, self_fault_queue, 
           voter_queue, voter_status, StopOperators, 
           emergency_stop_operator_queue, EmergencyStopOperators, 
           comfortable_stop_operator_queue, ComfortableStopOperators, 
           EmergencyHandlers, emergency_handler_status, 
           emergency_handler_queue, SelfMonitorings, vehicle_queue, 
           vehicle_status, switch, is_stop_operator_succeeded, 
           self_recoverable_flag, pc, fault_, operator_status_, 
           emergency_stop_operator_ecu, fault_c, operator_status, 
           comfortable_stop_operator_ecu, emergency_handler_ecu, fault_s, 
           self_monitoring_ecu, fault, switch_fault, external_detected, 
           is_switched, comfortable_stop_after_switch, 
           comfortable_stop_operator_operation, operation >>

ProcSet == (EmergencyStopOperators) \cup (ComfortableStopOperators) \cup (EmergencyHandlers) \cup (SelfMonitorings) \cup {"voter"} \cup {"vehicle"}

Init == (* Global variables *)
        /\ fault_ecu \in ECUs
        /\ faults = [fault_ecu_name : {fault_ecu}, fault_type : FaultTypes, fault_behavior : FaultBehaviors, fault_monitoring : {"self_monitoring"}]
        /\ e_faults = [fault_ecu_name : {fault_ecu}, fault_type: {"non_self_recoverable"}, fault_behavior : {"comfortable_stop"}, fault_monitoring : {"external_monitoring"}]
        /\ self_faults \in faults \X faults \X faults \X faults
        /\ self_fault_queue = [ecu \in ECUs |-> IF ecu = fault_ecu THEN self_faults ELSE <<>>]
        /\ voter_queue = <<>>
        /\ voter_status = "none"
        /\ StopOperators = [ecu : ECUs, behavior : FaultBehaviors]
        /\ emergency_stop_operator_queue = [ecu \in ECUs |-> <<>>]
        /\ EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"}
        /\ comfortable_stop_operator_queue = [ecu \in {"main", "sub"} |-> <<>>]
        /\ ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"}
        /\ EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler"}
        /\ emergency_handler_status = [ecu \in {"main", "sub"} |-> "none"]
        /\ emergency_handler_queue = [ecu \in {"main", "sub"} |-> <<>>]
        /\ SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"}
        /\ vehicle_queue = <<>>
        /\ vehicle_status = "running"
        /\ switch = [state |-> "main"]
        /\ is_stop_operator_succeeded = FALSE
        /\ self_recoverable_flag = TRUE
        (* Process emergency_stop_operator *)
        /\ fault_ = [self \in EmergencyStopOperators |-> defaultInitValue]
        /\ operator_status_ = [self \in EmergencyStopOperators |-> "idle"]
        /\ emergency_stop_operator_ecu = [self \in EmergencyStopOperators |-> IF self = "main_emergency_stop_operator"
                                                                              THEN "main"
                                                                              ELSE IF self = "sub_emergency_stop_operator"
                                                                              THEN "sub"
                                                                              ELSE "supervisor"]
        (* Process comfortable_stop_operator *)
        /\ fault_c = [self \in ComfortableStopOperators |-> defaultInitValue]
        /\ operator_status = [self \in ComfortableStopOperators |-> "idle"]
        /\ comfortable_stop_operator_ecu = [self \in ComfortableStopOperators |-> IF self = "main_comfortable_stop_operator"
                                                                                  THEN "main"
                                                                                  ELSE "sub"]
        (* Process emergency_handler *)
        /\ emergency_handler_ecu = [self \in EmergencyHandlers |-> IF self = "main_emergency_handler"
                                                                   THEN "main"
                                                                   ELSE "sub"]
        (* Process self_monitoring *)
        /\ fault_s = [self \in SelfMonitorings |-> defaultInitValue]
        /\ self_monitoring_ecu = [self \in SelfMonitorings |-> IF self = "main_self_monitoring"
                                                               THEN "main"
                                                               ELSE IF self = "sub_self_monitoring"
                                                               THEN "sub"
                                                               ELSE "supervisor"]
        (* Process voter *)
        /\ fault = defaultInitValue
        /\ switch_fault = defaultInitValue
        /\ external_detected = FALSE
        /\ is_switched = FALSE
        /\ comfortable_stop_after_switch = FALSE
        /\ comfortable_stop_operator_operation = defaultInitValue
        (* Process vehicle *)
        /\ operation = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self \in EmergencyStopOperators -> "OPERATE_STOP_"
                                        [] self \in ComfortableStopOperators -> "OPERATE_STOP"
                                        [] self \in EmergencyHandlers -> "EmergencyHandler"
                                        [] self \in SelfMonitorings -> "SelfMonitoring"
                                        [] self = "voter" -> "Voter"
                                        [] self = "vehicle" -> "Vehicle"]

OPERATE_STOP_(self) == /\ pc[self] = "OPERATE_STOP_"
                       /\ IF operator_status_[self] /= "stopped"
                             THEN /\ emergency_stop_operator_queue[emergency_stop_operator_ecu[self]] /= <<>> \/ (vehicle_status = "emergency_operating" /\ operator_status_[self] = "running")
                                  /\ IF vehicle_status = "emergency_operating" /\ operator_status_[self] = "running"
                                        THEN /\ operator_status_' = [operator_status_ EXCEPT ![self] = "stopped"]
                                             /\ IF switch.state = emergency_stop_operator_ecu[self] /\ ~(fault_ecu = emergency_stop_operator_ecu[self] /\ ~self_recoverable_flag)
                                                   THEN /\ vehicle_queue' = Append(vehicle_queue, "stopped")
                                                        /\ is_stop_operator_succeeded' = TRUE
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << vehicle_queue, 
                                                                        is_stop_operator_succeeded >>
                                             /\ UNCHANGED << voter_queue, 
                                                             emergency_stop_operator_queue, 
                                                             emergency_handler_status, 
                                                             fault_ >>
                                        ELSE /\ fault_' = [fault_ EXCEPT ![self] = Head(emergency_stop_operator_queue[emergency_stop_operator_ecu[self]])]
                                             /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![emergency_stop_operator_ecu[self]] = Tail(emergency_stop_operator_queue[emergency_stop_operator_ecu[self]])]
                                             /\ IF operator_status_[self] = "idle"
                                                   THEN /\ operator_status_' = [operator_status_ EXCEPT ![self] = "running"]
                                                        /\ IF emergency_stop_operator_ecu[self] /= "supervisor"
                                                              THEN /\ emergency_handler_status' = [emergency_handler_status EXCEPT ![emergency_stop_operator_ecu[self]] = "emergency_operating"]
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED emergency_handler_status
                                                        /\ IF switch.state = emergency_stop_operator_ecu[self]
                                                              THEN /\ vehicle_queue' = Append(vehicle_queue, "emergency_operating")
                                                                   /\ IF emergency_stop_operator_ecu[self] = "supervisor"
                                                                         THEN /\ voter_queue' = Append(voter_queue, fault_'[self])
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED voter_queue
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << voter_queue, 
                                                                                   vehicle_queue >>
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << voter_queue, 
                                                                        emergency_handler_status, 
                                                                        vehicle_queue, 
                                                                        operator_status_ >>
                                             /\ UNCHANGED is_stop_operator_succeeded
                                  /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << voter_queue, 
                                                  emergency_stop_operator_queue, 
                                                  emergency_handler_status, 
                                                  vehicle_queue, 
                                                  is_stop_operator_succeeded, 
                                                  fault_, operator_status_ >>
                       /\ UNCHANGED << fault_ecu, faults, e_faults, 
                                       self_faults, self_fault_queue, 
                                       voter_status, StopOperators, 
                                       EmergencyStopOperators, 
                                       comfortable_stop_operator_queue, 
                                       ComfortableStopOperators, 
                                       EmergencyHandlers, 
                                       emergency_handler_queue, 
                                       SelfMonitorings, vehicle_status, switch, 
                                       self_recoverable_flag, 
                                       emergency_stop_operator_ecu, fault_c, 
                                       operator_status, 
                                       comfortable_stop_operator_ecu, 
                                       emergency_handler_ecu, fault_s, 
                                       self_monitoring_ecu, fault, 
                                       switch_fault, external_detected, 
                                       is_switched, 
                                       comfortable_stop_after_switch, 
                                       comfortable_stop_operator_operation, 
                                       operation >>

emergency_stop_operator(self) == OPERATE_STOP_(self)

OPERATE_STOP(self) == /\ pc[self] = "OPERATE_STOP"
                      /\ IF operator_status[self] /= "stopped"
                            THEN /\ comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]] /= <<>> \/ (vehicle_status = "comfortable_operating" /\ operator_status[self] = "running")
                                 /\ IF vehicle_status = "comfortable_operating" /\ operator_status[self] = "running"
                                       THEN /\ operator_status' = [operator_status EXCEPT ![self] = "stopped"]
                                            /\ IF switch.state = comfortable_stop_operator_ecu[self] /\ ~(fault_ecu = comfortable_stop_operator_ecu[self] /\ ~self_recoverable_flag)
                                                  THEN /\ emergency_handler_queue' = [emergency_handler_queue EXCEPT ![comfortable_stop_operator_ecu[self]] = Append(emergency_handler_queue[comfortable_stop_operator_ecu[self]], "stopped")]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED emergency_handler_queue
                                            /\ UNCHANGED << comfortable_stop_operator_queue, 
                                                            fault_c >>
                                       ELSE /\ fault_c' = [fault_c EXCEPT ![self] = Head(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                                            /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![comfortable_stop_operator_ecu[self]] = Tail(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                                            /\ IF operator_status[self] = "idle"
                                                  THEN /\ operator_status' = [operator_status EXCEPT ![self] = "running"]
                                                       /\ IF switch.state = comfortable_stop_operator_ecu[self]
                                                             THEN /\ emergency_handler_queue' = [emergency_handler_queue EXCEPT ![comfortable_stop_operator_ecu[self]] = Append(emergency_handler_queue[comfortable_stop_operator_ecu[self]], "comfortable_operating")]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED emergency_handler_queue
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << emergency_handler_queue, 
                                                                       operator_status >>
                                 /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << comfortable_stop_operator_queue, 
                                                 emergency_handler_queue, 
                                                 fault_c, operator_status >>
                      /\ UNCHANGED << fault_ecu, faults, e_faults, self_faults, 
                                      self_fault_queue, voter_queue, 
                                      voter_status, StopOperators, 
                                      emergency_stop_operator_queue, 
                                      EmergencyStopOperators, 
                                      ComfortableStopOperators, 
                                      EmergencyHandlers, 
                                      emergency_handler_status, 
                                      SelfMonitorings, vehicle_queue, 
                                      vehicle_status, switch, 
                                      is_stop_operator_succeeded, 
                                      self_recoverable_flag, fault_, 
                                      operator_status_, 
                                      emergency_stop_operator_ecu, 
                                      comfortable_stop_operator_ecu, 
                                      emergency_handler_ecu, fault_s, 
                                      self_monitoring_ecu, fault, switch_fault, 
                                      external_detected, is_switched, 
                                      comfortable_stop_after_switch, 
                                      comfortable_stop_operator_operation, 
                                      operation >>

comfortable_stop_operator(self) == OPERATE_STOP(self)

EmergencyHandler(self) == /\ pc[self] = "EmergencyHandler"
                          /\ emergency_handler_queue[emergency_handler_ecu[self]] /= <<>>
                          /\ comfortable_stop_operator_operation' = Head(emergency_handler_queue[emergency_handler_ecu[self]])
                          /\ emergency_handler_queue' = [emergency_handler_queue EXCEPT ![emergency_handler_ecu[self]] = Tail(emergency_handler_queue[emergency_handler_ecu[self]])]
                          /\ IF emergency_handler_status[emergency_handler_ecu[self]] /= "emergency_operating"
                                THEN /\ IF switch.state = emergency_handler_ecu[self]
                                           THEN /\ vehicle_queue' = Append(vehicle_queue, comfortable_stop_operator_operation')
                                           ELSE /\ TRUE
                                                /\ UNCHANGED vehicle_queue
                                     /\ IF comfortable_stop_operator_operation' = "stopped"
                                           THEN /\ is_stop_operator_succeeded' = TRUE
                                           ELSE /\ TRUE
                                                /\ UNCHANGED is_stop_operator_succeeded
                                ELSE /\ TRUE
                                     /\ UNCHANGED << vehicle_queue, 
                                                     is_stop_operator_succeeded >>
                          /\ pc' = [pc EXCEPT ![self] = "EmergencyHandler"]
                          /\ UNCHANGED << fault_ecu, faults, e_faults, 
                                          self_faults, self_fault_queue, 
                                          voter_queue, voter_status, 
                                          StopOperators, 
                                          emergency_stop_operator_queue, 
                                          EmergencyStopOperators, 
                                          comfortable_stop_operator_queue, 
                                          ComfortableStopOperators, 
                                          EmergencyHandlers, 
                                          emergency_handler_status, 
                                          SelfMonitorings, vehicle_status, 
                                          switch, self_recoverable_flag, 
                                          fault_, operator_status_, 
                                          emergency_stop_operator_ecu, fault_c, 
                                          operator_status, 
                                          comfortable_stop_operator_ecu, 
                                          emergency_handler_ecu, fault_s, 
                                          self_monitoring_ecu, fault, 
                                          switch_fault, external_detected, 
                                          is_switched, 
                                          comfortable_stop_after_switch, 
                                          operation >>

emergency_handler(self) == EmergencyHandler(self)

SelfMonitoring(self) == /\ pc[self] = "SelfMonitoring"
                        /\ IF self_fault_queue[self_monitoring_ecu[self]] /= <<>>
                              THEN /\ fault_s' = [fault_s EXCEPT ![self] = Head(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ self_fault_queue' = [self_fault_queue EXCEPT ![self_monitoring_ecu[self]] = Tail(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ IF fault_s'[self].fault_type = "self_recoverable"
                                         THEN /\ IF (fault_s'[self].fault_behavior) = "emergency_stop"
                                                    THEN /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![self_monitoring_ecu[self]] = Append(emergency_stop_operator_queue[self_monitoring_ecu[self]], fault_s'[self])]
                                                         /\ UNCHANGED comfortable_stop_operator_queue
                                                    ELSE /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![self_monitoring_ecu[self]] = Append(comfortable_stop_operator_queue[self_monitoring_ecu[self]], fault_s'[self])]
                                                         /\ UNCHANGED emergency_stop_operator_queue
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << emergency_stop_operator_queue, 
                                                              comfortable_stop_operator_queue >>
                                   /\ voter_queue' = Append(voter_queue, fault_s'[self])
                                   /\ pc' = [pc EXCEPT ![self] = "SelfMonitoring"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                   /\ UNCHANGED << self_fault_queue, 
                                                   voter_queue, 
                                                   emergency_stop_operator_queue, 
                                                   comfortable_stop_operator_queue, 
                                                   fault_s >>
                        /\ UNCHANGED << fault_ecu, faults, e_faults, 
                                        self_faults, voter_status, 
                                        StopOperators, EmergencyStopOperators, 
                                        ComfortableStopOperators, 
                                        EmergencyHandlers, 
                                        emergency_handler_status, 
                                        emergency_handler_queue, 
                                        SelfMonitorings, vehicle_queue, 
                                        vehicle_status, switch, 
                                        is_stop_operator_succeeded, 
                                        self_recoverable_flag, fault_, 
                                        operator_status_, 
                                        emergency_stop_operator_ecu, fault_c, 
                                        operator_status, 
                                        comfortable_stop_operator_ecu, 
                                        emergency_handler_ecu, 
                                        self_monitoring_ecu, fault, 
                                        switch_fault, external_detected, 
                                        is_switched, 
                                        comfortable_stop_after_switch, 
                                        comfortable_stop_operator_operation, 
                                        operation >>

self_monitoring(self) == SelfMonitoring(self)

Voter == /\ pc["voter"] = "Voter"
         /\ IF voter_status /= "succeeded"
               THEN /\ voter_queue /= <<>> \/ is_stop_operator_succeeded
                    /\ IF is_stop_operator_succeeded
                          THEN /\ IF comfortable_stop_after_switch
                                     THEN /\ comfortable_stop_after_switch' = FALSE
                                          /\ is_stop_operator_succeeded' = FALSE
                                          /\ switch' = [switch EXCEPT !.state = IF switch_fault.fault_ecu_name = "main" THEN "sub" ELSE "main"]
                                          /\ IF "comfortable_stop" = "emergency_stop"
                                                THEN /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![(switch'.state)] = Append(emergency_stop_operator_queue[(switch'.state)], switch_fault)]
                                                     /\ UNCHANGED comfortable_stop_operator_queue
                                                ELSE /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![(switch'.state)] = Append(comfortable_stop_operator_queue[(switch'.state)], switch_fault)]
                                                     /\ UNCHANGED emergency_stop_operator_queue
                                          /\ UNCHANGED voter_status
                                     ELSE /\ voter_status' = "succeeded"
                                          /\ UNCHANGED << emergency_stop_operator_queue, 
                                                          comfortable_stop_operator_queue, 
                                                          switch, 
                                                          is_stop_operator_succeeded, 
                                                          comfortable_stop_after_switch >>
                               /\ UNCHANGED << voter_queue, 
                                               self_recoverable_flag, fault, 
                                               switch_fault, external_detected, 
                                               is_switched >>
                          ELSE /\ IF voter_queue /= <<>>
                                     THEN /\ fault' = Head(voter_queue)
                                          /\ voter_queue' = Tail(voter_queue)
                                          /\ IF external_detected
                                                THEN /\ UNCHANGED << voter_status, 
                                                                     emergency_stop_operator_queue, 
                                                                     comfortable_stop_operator_queue, 
                                                                     switch, 
                                                                     self_recoverable_flag, 
                                                                     switch_fault, 
                                                                     external_detected, 
                                                                     is_switched, 
                                                                     comfortable_stop_after_switch >>
                                                ELSE /\ IF fault'.fault_monitoring = "external_monitoring"
                                                           THEN /\ external_detected' = TRUE
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED external_detected
                                                     /\ IF fault'.fault_ecu_name = switch.state
                                                           THEN /\ IF fault'.fault_type = "self_recoverable"
                                                                      THEN /\ IF fault'.fault_behavior = "emergency_stop"
                                                                                 THEN /\ voter_status' = "emergency_operating"
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED voter_status
                                                                           /\ UNCHANGED << emergency_stop_operator_queue, 
                                                                                           comfortable_stop_operator_queue, 
                                                                                           switch, 
                                                                                           self_recoverable_flag, 
                                                                                           switch_fault, 
                                                                                           is_switched, 
                                                                                           comfortable_stop_after_switch >>
                                                                      ELSE /\ IF fault'.fault_type = "non_self_recoverable"
                                                                                 THEN /\ self_recoverable_flag' = FALSE
                                                                                      /\ switch' = [switch EXCEPT !.state = "supervisor"]
                                                                                      /\ is_switched' = TRUE
                                                                                      /\ voter_status' = "emergency_operating"
                                                                                      /\ IF "emergency_stop" = "emergency_stop"
                                                                                            THEN /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT !["supervisor"] = Append(emergency_stop_operator_queue["supervisor"], fault')]
                                                                                                 /\ UNCHANGED comfortable_stop_operator_queue
                                                                                            ELSE /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT !["supervisor"] = Append(comfortable_stop_operator_queue["supervisor"], fault')]
                                                                                                 /\ UNCHANGED emergency_stop_operator_queue
                                                                                      /\ IF fault'.fault_behavior = "comfortable_stop"
                                                                                            THEN /\ switch_fault' = fault'
                                                                                                 /\ comfortable_stop_after_switch' = TRUE
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED << switch_fault, 
                                                                                                                 comfortable_stop_after_switch >>
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED << voter_status, 
                                                                                                      emergency_stop_operator_queue, 
                                                                                                      comfortable_stop_operator_queue, 
                                                                                                      switch, 
                                                                                                      self_recoverable_flag, 
                                                                                                      switch_fault, 
                                                                                                      is_switched, 
                                                                                                      comfortable_stop_after_switch >>
                                                           ELSE /\ IF fault'.fault_ecu_name /= switch.state
                                                                      THEN /\ IF is_switched
                                                                                 THEN /\ UNCHANGED << emergency_stop_operator_queue, 
                                                                                                      comfortable_stop_operator_queue >>
                                                                                 ELSE /\ IF "comfortable_stop" = "emergency_stop"
                                                                                            THEN /\ emergency_stop_operator_queue' = [emergency_stop_operator_queue EXCEPT ![(switch.state)] = Append(emergency_stop_operator_queue[(switch.state)], fault')]
                                                                                                 /\ UNCHANGED comfortable_stop_operator_queue
                                                                                            ELSE /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![(switch.state)] = Append(comfortable_stop_operator_queue[(switch.state)], fault')]
                                                                                                 /\ UNCHANGED emergency_stop_operator_queue
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED << emergency_stop_operator_queue, 
                                                                                           comfortable_stop_operator_queue >>
                                                                /\ UNCHANGED << voter_status, 
                                                                                switch, 
                                                                                self_recoverable_flag, 
                                                                                switch_fault, 
                                                                                is_switched, 
                                                                                comfortable_stop_after_switch >>
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << voter_queue, 
                                                          voter_status, 
                                                          emergency_stop_operator_queue, 
                                                          comfortable_stop_operator_queue, 
                                                          switch, 
                                                          self_recoverable_flag, 
                                                          fault, switch_fault, 
                                                          external_detected, 
                                                          is_switched, 
                                                          comfortable_stop_after_switch >>
                               /\ UNCHANGED is_stop_operator_succeeded
                    /\ pc' = [pc EXCEPT !["voter"] = "Voter"]
               ELSE /\ pc' = [pc EXCEPT !["voter"] = "Done"]
                    /\ UNCHANGED << voter_queue, voter_status, 
                                    emergency_stop_operator_queue, 
                                    comfortable_stop_operator_queue, switch, 
                                    is_stop_operator_succeeded, 
                                    self_recoverable_flag, fault, switch_fault, 
                                    external_detected, is_switched, 
                                    comfortable_stop_after_switch >>
         /\ UNCHANGED << fault_ecu, faults, e_faults, self_faults, 
                         self_fault_queue, StopOperators, 
                         EmergencyStopOperators, ComfortableStopOperators, 
                         EmergencyHandlers, emergency_handler_status, 
                         emergency_handler_queue, SelfMonitorings, 
                         vehicle_queue, vehicle_status, fault_, 
                         operator_status_, emergency_stop_operator_ecu, 
                         fault_c, operator_status, 
                         comfortable_stop_operator_ecu, emergency_handler_ecu, 
                         fault_s, self_monitoring_ecu, 
                         comfortable_stop_operator_operation, operation >>

voter == Voter

Vehicle == /\ pc["vehicle"] = "Vehicle"
           /\ vehicle_queue /= <<>>
           /\ operation' = Head(vehicle_queue)
           /\ vehicle_queue' = Tail(vehicle_queue)
           /\ IF operation' = "emergency_operating"
                 THEN /\ vehicle_status' = "emergency_operating"
                 ELSE /\ IF operation' = "comfortable_operating"
                            THEN /\ vehicle_status' = "comfortable_operating"
                            ELSE /\ IF operation' = "stopped"
                                       THEN /\ vehicle_status' = "stopped"
                                       ELSE /\ TRUE
                                            /\ UNCHANGED vehicle_status
           /\ pc' = [pc EXCEPT !["vehicle"] = "Vehicle"]
           /\ UNCHANGED << fault_ecu, faults, e_faults, self_faults, 
                           self_fault_queue, voter_queue, voter_status, 
                           StopOperators, emergency_stop_operator_queue, 
                           EmergencyStopOperators, 
                           comfortable_stop_operator_queue, 
                           ComfortableStopOperators, EmergencyHandlers, 
                           emergency_handler_status, emergency_handler_queue, 
                           SelfMonitorings, switch, is_stop_operator_succeeded, 
                           self_recoverable_flag, fault_, operator_status_, 
                           emergency_stop_operator_ecu, fault_c, 
                           operator_status, comfortable_stop_operator_ecu, 
                           emergency_handler_ecu, fault_s, self_monitoring_ecu, 
                           fault, switch_fault, external_detected, is_switched, 
                           comfortable_stop_after_switch, 
                           comfortable_stop_operator_operation >>

vehicle == Vehicle

Next == voter \/ vehicle
           \/ (\E self \in EmergencyStopOperators: emergency_stop_operator(self))
           \/ (\E self \in ComfortableStopOperators: comfortable_stop_operator(self))
           \/ (\E self \in EmergencyHandlers: emergency_handler(self))
           \/ (\E self \in SelfMonitorings: self_monitoring(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION


====
