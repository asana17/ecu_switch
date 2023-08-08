---- MODULE ecu_switch ----

EXTENDS Sequences, TLC, Integers

CONSTANT ECUs, FaultTypes, FaultBehaviors, S


(*--fair algorithm ecuswitch
variables
  \*fault_ecu = "supervisor",
  fault_ecu \in ECUs,
  faults = [fault_ecu_name : {fault_ecu}, self_recoverable : {TRUE, FALSE}, fault_behavior : FaultBehaviors, monitoring_type : {"self_monitoring"}],
  no_fault = [fault_ecu_name |-> "none", fault_behavior |-> "none"]
  e_faults = [fault_ecu_name : {fault_ecu}, self_recoverable: FALSE, fault_behavior : {"comfortable_stop"}, monitoring_type : {"external_monitoring"}],
  faults_list \in faults \X faults,
  \*self_faults = << [fault_ecu_name |-> fault_ecu, self_recoverable |-> FALSE,  fault_behavior |-> "emergency_stop"], [fault_ecu_name |-> fault_ecu, self_recoverable |-> FALSE, fault_behavior |-> "emergency_stop"]>>,
  self_faults = [ecu \in ECUs |-> no_fault],
  external_faults = [ecu \in ECUs |-> no_fault],
  EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler"},
  emergency_handler_status = [ecu \in {"main", "sub"} |-> "none"],
  SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"},
  ExternalMonitorings = {"main_external_monitoring", "sub_external_monitoring", "supervisor_external_monitoring"},
  self_monitoring_results = [ecu \in ECUs |-> no_fault],
  external_monitoring_results = [ecu \in ECUs |-> no_fault],
  EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler", "supervisor_emergency_handler"},
  emergency_stop_operator_request = [ecu \in ECUs |-> NULL],
  comfortable_stop_operator_request = [ecu \in ECUs |-> NULL],
  EmergencyStopServices = {"main_emergency_stop_service", "sub_emergency_stop_service", "supervisor_emergency_stop_service"},
  EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"},
  ComfortableStopServices = {"main_comfortable_stop_service", "sub_comfortable_stop_service"}, \* No comfortable_stop operator in Supervisor
  ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"},
  emergency_stop_operator_status = [ecu \in ECUs |-> "available"],
  comfortable_stop_operator_status = [ecu \in ECUs |-> "available"],
  self_error_status = [ecu \in ECUs |-> [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]],
  external_error_status = [ecu \in ECUs |-> [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]],
  voter_state = [state |-> "normal", external_detected |-> FALSE, comfortable_stop_after_switch |-> FALSE],
  mrm_operation = [fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE],
  vehicle_status = "running",
  initial_selected_ecu = "main",
  switch = [state |-> initial_selected_ecu],
  is_stop_operator_succeeded = FALSE,
  self_recoverable_flag = TRUE,
  no_operation_during_emergency = TRUE;


define
  VehicleStopped == <>(vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped")
  NoOperationDuringEmergency == [](no_operation_during_emergency) \* comfortable stop and pull over cannot override emergency stop
  \*ProperMrm == <>(final_mrm_operation)
end define;

macro monitor(fault_list, result_list, ecu)
begin
  if fault_list[ecu] = no_fault then
    result_list[ecu] := no_fault;
  else
    result_list[ecu] := fault_list[ecu];
  end if;
end macro;

macro update_mrm_state(mrm_state, is_emergency)
begin
  if mrm_state.state = "normal" then
    if is_emergency then
      mrm_state.state := "operating";
    end if;
  elsif ~is_emergency then
    mrm_state.state := "normal";
  elsif mrm_state.state = "operating" then
    if is_stopped then
      mrm_state.state := "succeeded";
    end if;
  end if;
end macro;

macro mrm_request(mrm_behavior, ecu, request)
begin
  if mrm_behavior = "emergency_stop" then
    emergency_stop_operator_request[ecu] := request;
  elsif mrm_behavior = "comfortable_stop" then
    comfortable_stop_operator_request[ecu] := request;
  end if;
end macro;

macro get_current_mrm_behavior(mrm_state, monitoring_results, current_mrm_behavior)
begin
  if mrm_state.behavior = "none" then
    if monitoring_results.fault_behavior = "comfortable_stop" then
      current_mrm_behavior := "comfortable_stop";
    elsif monitoring_results.fault_behavior = "emergency_stop" then
      current_mrm_behavior := "emergency_stop";
    end if;
  elsif mrm_state.behavior = "comfortable_stop" then
    if monitoring_results.fault_behavior = "emergency_stop" then
      current_mrm_behavior := "emergency_stop";
    end if;
  end if;
end macro;

macro operate_mrm(mrm_state, current_mrm_behavior, ecu)
begin
  if mrm_state.state = "normal" then
    if mrm_state.behavior /= "none" then
      mrm_request(mrm_state.behavior, ecu, FALSE);
      mrm_state.behavior := "none";
    end if;
  elsif mrm_state.state = "operating" then
    if current_mrm_behavior /= mrm_state.behavior then
      mrm_request(mrm_state.behavior, ecu, FALSE);
      mrm_request(current_mrm_behavior, ecu, TRUE);
      mrm_state.behavior := current_mrm_behavior;
    end if;
  end if; \* if other state, do nothing
end macro;

macro operate_service(behavior, ecu)
begin
  if behavior = "emergency_stop" then
    if emergency_stop_operator_request[ecu] then
      emergency_stop_operator_status[ecu] := "operating";
    else
      emergency_stop_operator_status[ecu] := "available";
    end if;
    emergency_stop_operator_request[ecu] := NULL;
  elsif behavior = "comfortable_stop" then
    if comfortable_stop_operator_request[ecu] then
      comfortable_stop_operator_status[ecu] := "operating";
    else
      comfortable_stop_operator_status[ecu] := "available";
    end if;
    comfortable_stop_operator_request[ecu] := NULL;
  end if;
end macro;

macro update_self_error_status(ecu)
begin
  if self_monitoring_results[ecu] = no_fault then
    self_error_status[ecu].is_emergency := FALSE;
    self_error_status[ecu].stop_operation_needed := FALSE;
    self_error_status[ecu].switch_needed := FALSE;
  else \* fault detected
    if switch.state = ecu then
      if self_monitoring_results[ecu].self_recoverable then \* already mrm operaor called in emergency_handler
        self_error_status[ecu].is_emergency := TRUE;
        self_error_status[ecu].stop_operation_needed := FALSE;
        self_error_status[ecu].switch_needed := FALSE;
      else
        self_error_status[ecu].is_emergency := TRUE;
        self_error_status[ecu].stop_operation_needed := TRUE;
        self_error_status[ecu].switch_needed := TRUE;
      end if;
    else
      if switch.state /= initial_selected_ecu then \* already switched:
        self_error_status[ecu].is_emergency := TRUE;
        self_error_status[ecu].stop_operation_needed := FALSE;
        self_error_status[ecu].switch_needed := FALSE;
      else \* fault occured at redundant ecu
        self_error_status[ecu].is_emergency := TRUE;
        self_error_status[ecu].stop_operation_needed := TRUE;
        self_error_status[ecu].switch_needed := FALSE;
      end if;
    end if;
  end if;
end macro;

macro update_external_error_status(ecu)
begin
  if external_monitoring_results[ecu] = no_fault then
    external_error_status[ecu].is_emergency := FALSE;
    external_error_status[ecu].stop_operation_needed := FALSE;
    external_error_status[ecu].switch_needed := FALSE;
  else \* fault detected
    if switch.state = ecu then
      external_error_status[ecu].is_emergency := TRUE;
      external_error_status[ecu].stop_operation_needed := TRUE;
      external_error_status[ecu].switch_needed := TRUE;
    else
      if switch.state /= initial_selected_ecu then \* already switched:
        external_error_status[ecu].is_emergency := TRUE;
        external_error_status[ecu].stop_operation_needed := FALSE;
        external_error_status[ecu].switch_needed := FALSE;
      else \* fault occured at redundant ecu
        external_error_status[ecu].is_emergency := TRUE;
        external_error_status[ecu].stop_operation_needed := TRUE;
        external_error_status[ecu].switch_needed := FALSE;
      end if;
    end if;
  end if;
end macro;

macro error_status_to_int(error_status, int_value)
begin
  if error_status = no_fault then
    int_value := 0;
  else
    int_value := 1;
  end if;
end macro;

macro get_no_mrm_operation()
begin
  mrm_operation.fault_ecu := "none";
  mrm_operation.mrm_ecu := "none";
  mrm_operation.comfortable_stop_after_switch:= FALSE;
end macro;

macro get_mrm_operation_internal_ecu(error_status, ecu)
begin
  if error_status[ecu].is_emergency then
    mrm_operation.fault_ecu := ecu;
    if error_status[ecu].stop_operation_needed then
      if error_status[ecu].switch_needed then
        mrm_operation.mrm_ecu := "supervisor";
        mrm_operation.comfortable_stop_after_switch := TRUE;
      else
        mrm_operation.mrm_ecu := switch.state;
        mrm_operation.comfortable_stop_after_switch := FALSE;
      end if;
    end if;
  end if;
end macro;

macro get_mrm_operation_internal(error_status)
begin
  get_mrm_operation_internal_ecu(error_status, "main");
  get_mrm_operation_internal_ecu(error_status, "sub");
  get_mrm_operation_internal_ecu(error_status, "supervisor");
end macro;

macro get_mrm_operation_multiple_ecu_error()
begin
  mrm_operation.fault_ecu := "unknown";
  mrm_operation.mrm_ecu := "supervisor";
  mrm_operation.comfortable_stop_after_switch := FALSE;
end macro;


macro get_mrm_operation_from_self_monitoring(count)
begin
  if count = 0 then
    get_no_mrm_operation();
  elsif count = 1 then
    get_mrm_operation_internal(self_error_status);
  else
    get_mrm_operation_multiple_ecu_error();
  end if;
end macro;

macro get_mrm_operation_from_external_monitoring(count)
begin
  if count = 0 then
    voter_state.external_detected := FALSE;
    get_no_mrm_operation();
  else
    voter_state.external_detected := TRUE;
    if count = 1 then
      get_mrm_operation_internal(external_error_status);
    else
      get_mrm_operation_multiple_ecu_error();
    end if;
  end if;
end macro;


macro judge_mrm_operation(self_monitoring_count, external_monitoring_count)
begin
  get_mrm_operation_from_external_monitoring(external_monitoring_count);
  if ~voter_state.external_detected then \* prioritize external_monitoring
    get_mrm_operation_from_self_monitoring(self_monitoring_count);
  end if;
end macro;

macro transit_voter_normal()
begin
  voter_state.state := "normal";
  voter_state.fault_ecu := "none";
  voter_state.mrm_ecu := "none";
  voter_state.comfortable_stop_after_switch:= FALSE;
end macro;

macro transit_voter_supervisor_stop()
begin
  voter_state.state := "supervisor_stop";
  voter_state.fault_ecu := mrm_operation.fault_ecu;
  voter_state.mrm_ecu := "supervisor";
  voter_state.comfortable_stop_after_switch:= mrm_operation.comfortable_stop_after_switch;
end macro;

macro transit_voter_unexpected_behavior()
begin
  voter_state.state := "supervisor_stop";
  voter_state.fault_ecu := mrm_operation.fault_ecu;
  voter_state.mrm_ecu := "supervisor";
  voter_state.comfortable_stop_after_switch:= false;
end macro;

macro transit_voter_comfortable_stop()
begin
  voter_state.state := "comfortable_stop";
  voter_state.fault_ecu := mrm_operation.fault_ecu;
  voter_state.mrm_ecu := mrm_operation.mrm_ecu;
  voter_state.comfortable_stop_after_switch := false;
end macro;

macro update_voter_state()
begin
  \*--- normal ---
  if voter_state.state = "normal" then
    if mrm_operation.mrm_ecu = "supervisor" then
      transit_voter_supervisor_stop();
    elsif mrm_operation.mrm_ecu = "unknown" then
      transit_voter_unexpected_behavior();
    elsif mrm_operation.mrm_operation /= "none" then \* main or sub comfortable_stopp
      if mrm_operation.mrm_ecu /= initial_selected_ecu then \* invalid operation: directory calling comfortable_stop on extra ecu
        transit_voter_unexpected_behavior();
      else
        transit_voter_comfortable_stop();
      end if;
    end if;
  \*--- supervisor stop ---
  elsif voter_state.state = "supervisor_stop" then
    if vehicle_status = "emergency_stopped" /\ vehicle_status = "comfortable_stopped" then \* vehicle stopped
      if voter_state.comfortable_stop_after_switch then
        voter_state.comfortable_stop_after_switch := false;
        if voter_state.fault_ecu = "main" then
          voter_state.state := "comfortable_stop";
          voter_state.mrm_ecu = "sub";
        elsif voter_state.fault_ecu = "sub" then
          voter_state.state := "comfortable_stop";
          voter_state.mrm_ecu := "main";
        else
          voter_state.state := "failed";
        end if;
      else
        voter_state.state := "succeeded";
      end if;
    elsif mrm_operation.fault_ecu = "none" then
      transit_voter_normal();
    elsif mrm_operation.mrm_ecu /= "supervisor" /\ mrm_operation.mrm_ecu /= "none" then \* main or sub comfortable_stop
      if mrm_operation.mrm_ecu /= initial_selected_ecu then \* invalid operation: directory calling comfortable_stop on extra ecu
        transit_voter_unexpected_behavior();
      else
        transit_voter_comfortable_stop();
      end if;
    else
      voter_state.fault_ecu := mrm_operation.fault_ecu; \* if emergency occurs on another single ecu, continue supervisor stop
      if ~mrm_operation.comfortable_stop_after_switch then \* if comfortable_stop_after_switch become false, update it
        voter_state.comfortable_stop_after_switch := false;
      end if;
    end if;
  \* currently only comfortable_stop is operated in main and sub
  \*--- comfortable stop ---
  elsif voter_state.state = "comfortable_stop" then
    if vehicle_status = "emergency_stopped" /\ vehicle_status = "comfortable_stopped" then \* vehicle stopped
      voter_state.state := "succeeded";
    elsif mrm_operation.fault_ecu = "none" then
      transit_voter_normal();
    elsif mrm_operation.mrm_ecu = "supervisor" then
      transit_voter_supervisor_stop();
    elsif mrm_operation.mrm_ecu ~= "none" then
      if mrm_operation.mrm_ecu /= voter_state.mrm_ecu then
        if mrm_operation.mrm_ecu /= initial_selected_ecu then
          transit_voter_unexpected_behavior();
        else
          transit_voter_comfortable_stop();
        end if;
      end if;
    end if;
  end if;
end macro;

macro cancel_current_mrm_on_voter(ecu)
begin
  if ecu = "supervisor" then
    if emergency_stop_operator_status[ecu] = "operating" then
      emergency_stop_operator_request[ecu] := FALSE;
    end if;
  else
    if comfortable_stop_operator_status[ecu] = "operating" then
      comfortable_stop_operator_request[ecu] := FALSE;
    end if;
  end if;
end macro;

macro operate_mrm_on_voter(current_mrm_ecu)
begin
  \*--- normal ---
  if voter_state.state = "normal" then
    if current_mrm_ecu /= "none" then
      switch.state := initial_selected_ecu;
      \* TODO need check
      if current_mrm_ecu = "supervisor" then
        if emergency_stop_operator_status[current_mrm_ecu] = "operating" then
          cancel_current_mrm_on_voter(current_mrm_ecu);
        else
          current_mrm_ecu := "none";
        end if;
      else
        if comfortable_stop_operator_status[current_mrm_ecu] = "operating" then
          cancel_current_mrm_on_voter(current_mrm_ecu);
        else
          current_mrm_ecu := "none"; \* main and sub emergency_stop_operator is called/canceled by emergency_handler
      end if;
    end if;
  \*--- supervisor_stop---
  elsif voter_state.state = "supervisor_stop" then
    if current_mrm_ecu /= "supervisor" then
      if comfortable_stop_operator_status[current_mrm_ecu] = "operating" then
        cancel_current_mrm_on_voter(current_mrm_ecu);
      elsif emergency_stop_operator_status["supervisor"] /= "operating" then
        emergency_stop_operator_request["supervisor"] := TRUE;
      else
        switch.state := "supervisor"
        current_mrm_ecu := "supervisor";
      end if;
    end if;
  \*--- comfortable_stop---
  elsif voter_state.state = "comfortable_stop" then
    \* TODO! current_mrm_ecuがsupervisorなのか、main(initial_selected_ecu)なのか、subなのかで変わってくるので遷移を考える必要あり。
    )なのか、subなのか
    if current_mrm_ecu /= voter_state.mrm_ecu then
      if emergency_stop_operator_status["supervisor"] = "operating" then
        cancel_current_mrm_on_voter("supervisor");
      elsif comfortable_stop_operator_status["current_mrm_ecu"] = "operating" then \* direct transition from Sub ComfortableStop to Main ComfortableStop is available.
        cancel_current_mrm_on_voter(current_mrm_ecu);
      elsif voter_state.mrm_ecu = "main" then
        if emergency_stop_operator_status("main") /= "operating" then \* check main emergency_stop operator status: if emergency_stop not running, comfortable stop can be operated
          if comfortable_stop_operator_status["main"] /= "operating" then
            comfortable_stop_operator_request["main"] := TRUE;
          else
            switch.state := "main";
            voter_state.mrm_ecu := "main";
          end if;
        end if;
      elsif voter_state.mrm_ecu = "sub" then



    end if;
    if voter_state.mrm_ecu = "main" then



end macro;

process safety_mechanism = "safety_mechanism"
variables
  fault;
begin
  SafetyMechanism:
    while fault_list /= <<>> do
      fault := Head(fault_queue);
      fault_queue := Tail(fault_queue);
      if fault.monitoring_type = "self_monitoring" then
        self_faults[fault.ecu] := fault;
      else
        external_faults[fault.ecu] := fault;
      end if;
    end while;
end process;

process self_monitoring \in SelfMonitorings
variables
  ecu =
    IF self = "main_self_monitoring" THEN "main"
    ELSE IF self = "sub_self_monitoring" THEN "sub"
    ELSE "supervisor";
begin
  SelfMonitoring:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      monitor(self_faults, self_monitoring_results, ecu);
    end while;
end process;

process external_monitoring \in ExternalMonitorings
variables
  ecu =
    IF self = "main_external_monitoring" THEN "main"
    ELSE IF self = "sub_external_monitoring" THEN "sub"
    ELSE "supervisor";
begin
  ExternalMonitoring:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      monitor(external_faults, external_monitoring_results, ecu);
    end while;
end process;

process emergency_handler \in EmergencyHandlers
variables
  is_emergency = FALSE,
  current_mrm_behavior,
  mrm_state = [state |-> "normal", behavior |-> "none"],
  ecu =
    IF self = "main_emergency_handler" THEN "main"
    ELSE IF self = "sub_emergency_handler" THEN "sub"
    ELSE "supervisor";
begin
  EmergencyHandling:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      is_emergency := self_monitoring_results[ecu] /= no_fault;
      update_mrm_state(mrm_state, is_emergency);
      get_current_mrm_behavior(mrm_state, self_monitoring_results[ecu], current_mrm_behavior)
      operate_mrm(mrm_state, current_mrm_behavior, ecu);
    end while;
end process;

process emergency_stop_service \in EmergencyStopServices
variables
ecu =
    IF self = "main_emergency_stop_service" THEN "main"
    ELSE IF self = "sub_emergency_stop_service" THEN "sub"
    ELSE "supervisor";
begin
  EmergencyStopService:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      await emergency_stop_operator_request[ecu] /= NULL;
        operate_service("emergency_stop", ecu);
      end if;
    end while;
end process;

process comfortable_stop_service \in ComfortableStopServices
variables
ecu =
    IF self = "main_comfortable_stop_service" THEN "main" ELSE "sub";
begin
  ComfortableStopService:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      await comfortable_stop_operator_request /= NULL;
      operate_service("comfortable_stop", ecu);
    end while;
end process;


\* operate emergency_stop or comfortable_stop in each ECU
process emergency_stop_operator \in EmergencyStopOperators
variables
  ecu =
    IF self = "main_emergency_stop_operator" THEN "main"
    ELSE IF self = "sub_emergency_stop_operator" THEN "sub"
    ELSE "supervisor";
begin
  OperateEmergencyStop:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      if switch.state = ecu then
        if emergency_stop_operator_status[ecu] = "operating" then
          vehicle_status := "emergency_operating";
        else
          vehicle_status := "running";
        end if;
      end if;
    end while;
end process;

process comfortable_stop_operator \in ComfortableStopOperators
variables
  ecu =
    IF self = "main_comfortable_stop_operator" THEN "main" ELSE "sub";
begin
  OperatecomfortableStop:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      if switch.state = ecu then
        if comfortable_stop_operator_status[ecu] = "operating" then
          if emergency_stop_operator_status[ecu] = "operating" then
            no_operation_during_emergency := FALSE;
          end if;
          vehicle_status := "comfortable_operating";
        else
          vehicle_status := "running";
        end if;
      end if;
    end while;
end process;

\* decide which ECU to operate MRM
process voter = "voter"
variables
  self_monitoring_count,
  external_monitoring_count,
  current_mrm_ecu = "none";
begin
  Voter:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      update_self_error_status("main");
      update_self_error_status("sub");
      update_self_error_status("supervisor");
      update_external_error_status("main");
      update_external_error_status("sub");
      update_external_error_status("supervisor");
      self_monitoring_count := error_status_to_int(self_error_status["main"]) + error_status_to_int(self_error_status["sub"]) + error_status_to_int(self_error_status["supervisor"]);
      external_monitoring_count := error_status_to_int(external_error_status["main"]) + error_status_to_int(external_error_status["sub"]) + error_status_to_int(external_error_status["supervisor"]);
      judge_mrm_operation(self_monitoring_count, external_monitoring_count);
      update_voter_state();
      operate_mrm_on_voter(current_mrm_ecu);
    end while;
end process;

process vehicle = "vehicle"
begin
  Vehicle:
    while vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"  do
      if vehicle_status = "emergency_operating" then
        vehicle_status := "emergency_stopped";
      elsif vehicle_status := "comfortable_operating" then
        vehicle_status := "comfortable_stopped";
      end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "db8c21dc" /\ chksum(tla) = "c0bd7da3")
\* Label OPERATE_STOP of process emergency_stop_operator at line 77 col 5 changed to OPERATE_STOP_
\* Process variable fault of process emergency_stop_operator at line 67 col 3 changed to fault_
\* Process variable operator_status of process emergency_stop_operator at line 68 col 3 changed to operator_status_
\* Process variable fault of process comfortable_stop_operator at line 111 col 3 changed to fault_c
\* Process variable fault of process self_monitoring at line 145 col 3 changed to fault_s
CONSTANT defaultInitValue
VARIABLES fault_ecu, faults, e_faults, self_faults, self_fault_queue,
          voter_queue, voter_status, StopOperators,
          emergency_stop_operator_queue, EmergencyStopOperators,
          comfortable_stop_operator_queue, ComfortableStopOperators,
          EmergencyHandlers, emergency_handler_status, SelfMonitorings,
          vehicle_status, switch, is_stop_operator_succeeded,
          self_recoverable_flag, no_operation_during_emergency, pc

(* define statement *)
NoOperationDuringEmergency == no_operation_during_emergency = TRUE
ProperMrm == <>(final_mrm_operation)

VARIABLES fault_, operator_status_, emergency_stop_operator_ecu, fault_c,
          operator_status, comfortable_stop_operator_ecu, fault_s,
          self_monitoring_ecu, fault, switch_fault, external_detected,
          is_switched, comfortable_stop_after_switch,
          comfortable_stop_operator_operation

vars == << fault_ecu, faults, e_faults, self_faults, self_fault_queue,
           voter_queue, voter_status, StopOperators,
           emergency_stop_operator_queue, EmergencyStopOperators,
           comfortable_stop_operator_queue, ComfortableStopOperators,
           EmergencyHandlers, emergency_handler_status, SelfMonitorings,
           vehicle_status, switch, is_stop_operator_succeeded,
           self_recoverable_flag, no_operation_during_emergency, pc, fault_,
           operator_status_, emergency_stop_operator_ecu, fault_c,
           operator_status, comfortable_stop_operator_ecu, fault_s,
           self_monitoring_ecu, fault, switch_fault, external_detected,
           is_switched, comfortable_stop_after_switch,
           comfortable_stop_operator_operation >>

ProcSet == (EmergencyStopOperators) \cup (ComfortableStopOperators) \cup (SelfMonitorings) \cup {"voter"}

Init == (* Global variables *)
        /\ fault_ecu \in ECUs
        /\ faults = [fault_ecu_name : {fault_ecu}, self_recoverable : FaultTypes, fault_behavior : FaultBehaviors, monitoring_type : {"self_monitoring"}]
        /\ e_faults = [fault_ecu_name : {fault_ecu}, self_recoverable: {"non_self_recoverable"}, fault_behavior : {"comfortable_stop"}, monitoring_type : {"external_monitoring"}]
        /\ self_faults \in faults \X faults \X faults
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
        /\ SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"}
        /\ vehicle_status = "running"
        /\ switch = [state |-> "main"]
        /\ is_stop_operator_succeeded = FALSE
        /\ self_recoverable_flag = TRUE
        /\ no_operation_during_emergency = TRUE
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
        /\ pc = [self \in ProcSet |-> CASE self \in EmergencyStopOperators -> "OPERATE_STOP_"
                                        [] self \in ComfortableStopOperators -> "OPERATE_STOP"
                                        [] self \in SelfMonitorings -> "SelfMonitoring"
                                        [] self = "voter" -> "Voter"]

OPERATE_STOP_(self) == /\ pc[self] = "OPERATE_STOP_"
                       /\ IF operator_status_[self] /= "stopped"
                             THEN /\ emergency_stop_operator_queue[emergency_stop_operator_ecu[self]] /= <<>> \/ (vehicle_status = "emergency_operating" /\ operator_status_[self] = "running")
                                  /\ IF vehicle_status = "emergency_operating" /\ operator_status_[self] = "running"
                                        THEN /\ operator_status_' = [operator_status_ EXCEPT ![self] = "stopped"]
                                             /\ IF switch.state = emergency_stop_operator_ecu[self] /\ ~(fault_ecu = emergency_stop_operator_ecu[self] /\ ~self_recoverable_flag)
                                                   THEN /\ vehicle_status' = "stopped"
                                                        /\ is_stop_operator_succeeded' = TRUE
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << vehicle_status,
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
                                                              THEN /\ vehicle_status' = "emergency_operating"
                                                                   /\ IF emergency_stop_operator_ecu[self] = "supervisor"
                                                                         THEN /\ voter_queue' = Append(voter_queue, fault_'[self])
                                                                         ELSE /\ TRUE
                                                                              /\ UNCHANGED voter_queue
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED << voter_queue,
                                                                                   vehicle_status >>
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED << voter_queue,
                                                                        emergency_handler_status,
                                                                        vehicle_status,
                                                                        operator_status_ >>
                                             /\ UNCHANGED is_stop_operator_succeeded
                                  /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP_"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                  /\ UNCHANGED << voter_queue,
                                                  emergency_stop_operator_queue,
                                                  emergency_handler_status,
                                                  vehicle_status,
                                                  is_stop_operator_succeeded,
                                                  fault_, operator_status_ >>
                       /\ UNCHANGED << fault_ecu, faults, e_faults,
                                       self_faults, self_fault_queue,
                                       voter_status, StopOperators,
                                       EmergencyStopOperators,
                                       comfortable_stop_operator_queue,
                                       ComfortableStopOperators,
                                       EmergencyHandlers, SelfMonitorings,
                                       switch, self_recoverable_flag,
                                       no_operation_during_emergency,
                                       emergency_stop_operator_ecu, fault_c,
                                       operator_status,
                                       comfortable_stop_operator_ecu, fault_s,
                                       self_monitoring_ecu, fault,
                                       switch_fault, external_detected,
                                       is_switched,
                                       comfortable_stop_after_switch,
                                       comfortable_stop_operator_operation >>

emergency_stop_operator(self) == OPERATE_STOP_(self)

OPERATE_STOP(self) == /\ pc[self] = "OPERATE_STOP"
                      /\ IF operator_status[self] /= "stopped"
                            THEN /\ comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]] /= <<>> \/ (vehicle_status = "comfortable_operating" /\ operator_status[self] = "running")
                                 /\ IF vehicle_status = "comfortable_operating" /\ operator_status[self] = "running"
                                       THEN /\ operator_status' = [operator_status EXCEPT ![self] = "stopped"]
                                            /\ IF switch.state = comfortable_stop_operator_ecu[self] /\ ~(fault_ecu = comfortable_stop_operator_ecu[self] /\ ~self_recoverable_flag)
                                                  THEN /\ IF emergency_handler_status[comfortable_stop_operator_ecu[self]] /= "emergency_operating"
                                                             THEN /\ IF switch.state = comfortable_stop_operator_ecu[self]
                                                                        THEN /\ vehicle_status' = "stopped"
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED vehicle_status
                                                                  /\ IF "stopped" = "stopped"
                                                                        THEN /\ is_stop_operator_succeeded' = TRUE
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED is_stop_operator_succeeded
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED << vehicle_status,
                                                                                  is_stop_operator_succeeded >>
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << vehicle_status,
                                                                       is_stop_operator_succeeded >>
                                            /\ UNCHANGED << comfortable_stop_operator_queue,
                                                            fault_c >>
                                       ELSE /\ fault_c' = [fault_c EXCEPT ![self] = Head(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                                            /\ comfortable_stop_operator_queue' = [comfortable_stop_operator_queue EXCEPT ![comfortable_stop_operator_ecu[self]] = Tail(comfortable_stop_operator_queue[comfortable_stop_operator_ecu[self]])]
                                            /\ IF operator_status[self] = "idle"
                                                  THEN /\ operator_status' = [operator_status EXCEPT ![self] = "running"]
                                                       /\ IF switch.state = comfortable_stop_operator_ecu[self]
                                                             THEN /\ IF emergency_handler_status[comfortable_stop_operator_ecu[self]] /= "emergency_operating"
                                                                        THEN /\ IF switch.state = comfortable_stop_operator_ecu[self]
                                                                                   THEN /\ vehicle_status' = "comfortable_operating"
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED vehicle_status
                                                                             /\ IF "comfortable_operating" = "stopped"
                                                                                   THEN /\ is_stop_operator_succeeded' = TRUE
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED is_stop_operator_succeeded
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED << vehicle_status,
                                                                                             is_stop_operator_succeeded >>
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED << vehicle_status,
                                                                                  is_stop_operator_succeeded >>
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << vehicle_status,
                                                                       is_stop_operator_succeeded,
                                                                       operator_status >>
                                 /\ pc' = [pc EXCEPT ![self] = "OPERATE_STOP"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                 /\ UNCHANGED << comfortable_stop_operator_queue,
                                                 vehicle_status,
                                                 is_stop_operator_succeeded,
                                                 fault_c, operator_status >>
                      /\ UNCHANGED << fault_ecu, faults, e_faults, self_faults,
                                      self_fault_queue, voter_queue,
                                      voter_status, StopOperators,
                                      emergency_stop_operator_queue,
                                      EmergencyStopOperators,
                                      ComfortableStopOperators,
                                      EmergencyHandlers,
                                      emergency_handler_status,
                                      SelfMonitorings, switch,
                                      self_recoverable_flag,
                                      no_operation_during_emergency, fault_,
                                      operator_status_,
                                      emergency_stop_operator_ecu,
                                      comfortable_stop_operator_ecu, fault_s,
                                      self_monitoring_ecu, fault, switch_fault,
                                      external_detected, is_switched,
                                      comfortable_stop_after_switch,
                                      comfortable_stop_operator_operation >>

comfortable_stop_operator(self) == OPERATE_STOP(self)

SelfMonitoring(self) == /\ pc[self] = "SelfMonitoring"
                        /\ IF self_fault_queue[self_monitoring_ecu[self]] /= <<>>
                              THEN /\ fault_s' = [fault_s EXCEPT ![self] = Head(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ self_fault_queue' = [self_fault_queue EXCEPT ![self_monitoring_ecu[self]] = Tail(self_fault_queue[self_monitoring_ecu[self]])]
                                   /\ IF fault_s'[self].self_recoverable = "self_recoverable"
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
                                        SelfMonitorings, vehicle_status,
                                        switch, is_stop_operator_succeeded,
                                        self_recoverable_flag,
                                        no_operation_during_emergency, fault_,
                                        operator_status_,
                                        emergency_stop_operator_ecu, fault_c,
                                        operator_status,
                                        comfortable_stop_operator_ecu,
                                        self_monitoring_ecu, fault,
                                        switch_fault, external_detected,
                                        is_switched,
                                        comfortable_stop_after_switch,
                                        comfortable_stop_operator_operation >>

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
                                                ELSE /\ IF fault'.monitoring_type = "external_monitoring"
                                                           THEN /\ external_detected' = TRUE
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED external_detected
                                                     /\ IF fault'.fault_ecu_name = switch.state
                                                           THEN /\ IF fault'.self_recoverable = "self_recoverable"
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
                                                                      ELSE /\ IF fault'.self_recoverable = "non_self_recoverable"
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
                         SelfMonitorings, vehicle_status,
                         no_operation_during_emergency, fault_,
                         operator_status_, emergency_stop_operator_ecu,
                         fault_c, operator_status,
                         comfortable_stop_operator_ecu, fault_s,
                         self_monitoring_ecu,
                         comfortable_stop_operator_operation >>

voter == Voter

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == voter
           \/ (\E self \in EmergencyStopOperators: emergency_stop_operator(self))
           \/ (\E self \in ComfortableStopOperators: comfortable_stop_operator(self))
           \/ (\E self \in SelfMonitorings: self_monitoring(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


====
