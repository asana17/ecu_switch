---- MODULE ecu_switch ----

EXTENDS Sequences, TLC, Integers

CONSTANT ECUs, FaultTypes, FaultBehaviors, MonitoringTypes


(*--fair algorithm ecuswitch
variables
  \*fault_ecu = "supervisor",
  fault_ecu \in ECUs,
  s_faults = [fault_ecu_name : {fault_ecu}, self_recoverable : {TRUE, FALSE}, fault_behavior : FaultBehaviors, monitoring_type : {"self_monitoring"}],
  no_faults = [fault_ecu_name : {"none"}, self_recoverable : {TRUE}, fault_behavior : {"none"}, monitoring_type : MonitoringTypes],
  e_faults = [fault_ecu_name : {fault_ecu}, self_recoverable : {FALSE}, fault_behavior : {"comfortable_stop"}, monitoring_type : {"external_monitoring"}],
  faults = s_faults \union e_faults,
  faults_and_no_faults = faults \union no_faults,
  fault_queue \in faults_and_no_faults \X faults_and_no_faults \X faults_and_no_faults \X faults,
  no_fault = [fault_ecu_name |-> "none", fault_behavior |-> "none"],
  \*self_faults = << [fault_ecu_name |-> fault_ecu, self_recoverable |-> FALSE,  fault_behavior |-> "emergency_stop"], [fault_ecu_name |-> fault_ecu, self_recoverable |-> FALSE, fault_behavior |-> "emergency_stop"]>>,
  self_faults = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault],
  external_faults = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault],
  EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler"},
  emergency_handler_status = [main |-> "none", sub |-> "none"],
  SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"},
  ExternalMonitorings = {"main_external_monitoring", "sub_external_monitoring", "supervisor_external_monitoring"},
  self_monitoring_results = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault],
  external_monitoring_results = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault],
  emergency_stop_operator_request = [main |-> "none", sub |-> "none", supervisor |-> "none"],
  comfortable_stop_operator_request = [main |-> "none", sub |-> "none"],
  EmergencyStopServices = {"main_emergency_stop_service", "sub_emergency_stop_service", "supervisor_emergency_stop_service"},
  EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"},
  ComfortableStopServices = {"main_comfortable_stop_service", "sub_comfortable_stop_service"}, \* No comfortable_stop operator in Supervisor
  ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"},
  emergency_stop_operator_status = [main |-> "available", sub |-> "available", supervisor |-> "available"],
  comfortable_stop_operator_status = [main |-> "available", sub |-> "available", supervisor |-> "available"],
  no_error = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE],
  main_self_error_status = no_error;
  sub_self_error_status = no_error;
  supervisor_self_error_status = no_error;
  main_external_error_status = no_error;
  sub_external_error_status = no_error;
  supervisor_external_error_status = no_error;
  voter_state = [state |-> "normal", external_detected |-> FALSE, comfortable_stop_after_switch |-> FALSE],
  mrm_operation = [fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE],
  vehicle_status = "running",
  initial_selected_ecu = "main",
  extra_ecu = "sub",
  switch = [state |-> initial_selected_ecu],
  is_stop_operator_succeeded = FALSE,
  self_recoverable_flag = TRUE,
  no_operation_during_emergency = TRUE;


define
  VehicleStopped == <>[](vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped")
  NoOperationDuringEmergency == no_operation_during_emergency \* comfortable stop and pull over cannot override emergency stop
  \*ProperMrm == <>(final_mrm_operation)
end define;

macro monitor(fault_list, result_list, ecu)
begin
  if fault_list[ecu].fault_ecu_name = "none" then
    result_list[ecu] := no_fault;
  else
    result_list[ecu] := fault_list[ecu];
  end if;
end macro;

macro update_mrm_state(mrm_state, is_emergency)
begin
  if mrm_state = "normal" then
    if is_emergency then
      mrm_state := "operating";
    end if;
  elsif ~is_emergency then
    mrm_state := "normal";
  elsif mrm_state = "operating" then
    if vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped" then
      mrm_state := "succeeded";
    end if;
  end if;
end macro;

macro get_current_mrm_behavior(mrm_behavior, monitoring_results, current_mrm_behavior)
begin
  if mrm_behavior = "none" then
    if monitoring_results.fault_behavior = "comfortable_stop" then
      current_mrm_behavior := "comfortable_stop";
    elsif monitoring_results.fault_behavior = "emergency_stop" then
      current_mrm_behavior := "emergency_stop";
    end if;
  elsif mrm_behavior = "comfortable_stop" then
    if monitoring_results.fault_behavior = "emergency_stop" then
      current_mrm_behavior := "emergency_stop";
    end if;
  end if;
end macro;

macro operate_mrm(mrm_state, mrm_behavior, current_mrm_behavior, ecu)
begin
  if mrm_state = "normal" then
    if mrm_behavior /= "none" then
      if mrm_behavior = "emergency_stop" then
        emergency_stop_operator_request[ecu] := "cancel";
      elsif mrm_behavior = "comfortable_stop" then
        comfortable_stop_operator_request[ecu] := "cancel";
      end if;
      mrm_behavior := "none";
    end if;
  elsif mrm_state = "operating" then
    if current_mrm_behavior /= mrm_behavior then
      if mrm_behavior = "emergency_stop" then
        emergency_stop_operator_request[ecu] := "cancel";
        if current_mrm_behavior = "comfortable_stop" then
          comfortable_stop_operator_request[ecu] := "operate";
        end if;
      elsif mrm_behavior = "comfortable_stop" then
        comfortable_stop_operator_request[ecu] := "cancel";
        if current_mrm_behavior = "emergency_stop" then
          emergency_stop_operator_request[ecu] := "operate";
        end if;
      else
        emergency_stop_operator_request[ecu] := "operate" ;
      end if;
      mrm_behavior := current_mrm_behavior;
    end if;
  end if; \* if other state, do nothing
end macro;

macro operate_service(behavior, ecu)
begin
  if behavior = "emergency_stop" then
    if emergency_stop_operator_request[ecu] = "operate" then
      emergency_stop_operator_status[ecu] := "operating";
    elsif emergency_stop_operator_request[ecu] = "cancel" then
      emergency_stop_operator_status[ecu] := "available";
    end if;
    emergency_stop_operator_request[ecu] := "none";
  elsif behavior = "comfortable_stop" then
    if comfortable_stop_operator_request[ecu] = "operate" then
      comfortable_stop_operator_status[ecu] := "operating";
    elsif comfortable_stop_operator_request[ecu] = "cancel" then
      comfortable_stop_operator_status[ecu] := "available";
    end if;
    comfortable_stop_operator_request[ecu] := "none";
  end if;
end macro;

macro update_self_error_status(self_monitoring_results, ecu_error_status, ecu)
begin
  if self_monitoring_results = no_fault then
    ecu_error_status := [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE];
  else \* fault detected
    if switch.state = ecu then
      if self_monitoring_results.self_recoverable then \* already mrm operaor called in emergency_handler
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE];
      else
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE];
      end if;
    else
      if switch.state /= initial_selected_ecu then \* already switched:
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE];
      else \* fault occured at redundant ecu
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE];
      end if;
    end if;
  end if;
end macro;

macro update_external_error_status(external_monitoring_results, ecu_error_status, ecu)
begin
  if external_monitoring_results = no_fault then
    ecu_error_status := [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE];
  else \* fault detected
    if switch.state = ecu then
      ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE];
    else
      if switch.state /= initial_selected_ecu then \* already switched:
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE];
      else \* fault occured at redundant ecu
        ecu_error_status := [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE];
      end if;
    end if;
  end if;
end macro;

macro error_status_to_int(error_status, int_value)
begin
  if error_status = no_error then
    int_value := 0;
  else
    int_value := 1;
  end if;
end macro;

macro get_no_mrm_operation()
begin
  mrm_operation := [fault_ecu |-> "none", mrm_ecu |->"none", comfortable_stop_after_switch |-> FALSE];
end macro;

macro get_mrm_operation_internal_ecu(error_status, ecu)
begin
  if error_status.is_emergency then
    if error_status.stop_operation_needed then
      if error_status.switch_needed then
        mrm_operation := [fault_ecu |-> ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE];
      else
        mrm_operation := [fault_ecu |-> ecu, mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE];
      end if;
    else
      mrm_operation := [fault_ecu |-> ecu,  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE];
    end if;
  end if;
end macro;

macro get_mrm_operation_multiple_ecu_error()
begin
  mrm_operation := [fault_ecu |-> "unknown", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE];
end macro;


macro transit_voter_normal()
begin
  voter_state := [state |-> "normal", fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE];
end macro;

macro transit_voter_supervisor_stop()
begin
  voter_state := [state |-> "supervisor_stop", fault_ecu |-> mrm_operation.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> mrm_operation.comfortable_stop_after_switch];
end macro;

macro transit_voter_unexpected_behavior()
begin
  voter_state := [state |-> "supervisor_stop", fault_ecu |-> mrm_operation.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE];
end macro;

macro transit_voter_comfortable_stop()
begin
  voter_state := [state |-> "comfortable_stop", fault_ecu |-> mrm_operation.fault_ecu, mrm_ecu |-> mrm_operation.mrm_ecu, comfortable_stop_after_switch |-> FALSE];
end macro;

macro update_voter_state()
begin
  \*--- normal ---
  if voter_state.state = "normal" then
    if mrm_operation.fault_ecu /= "none" then
      if mrm_operation.mrm_ecu = "supervisor" then
        transit_voter_supervisor_stop();
      elsif mrm_operation.mrm_ecu = "unknown" then
        transit_voter_unexpected_behavior();
      elsif mrm_operation.mrm_ecu /= "none" then \* main or sub comfortable_stopp
        if mrm_operation.mrm_ecu /= initial_selected_ecu then \* invalid operation: directory calling comfortable_stop on extra ecu
          transit_voter_unexpected_behavior();
        else
          transit_voter_comfortable_stop();
        end if;
      end if;
    end if;
  \*--- supervisor stop ---
  elsif voter_state.state = "supervisor_stop" then
    if vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped" then \* vehicle stopped
      if voter_state.comfortable_stop_after_switch then
        if voter_state.fault_ecu = "main" then
          voter_state := [state |-> "comfortable_stop", fault_ecu |-> "main", mrm_ecu |-> "sub", comfortable_stop_after_switch |-> TRUE];
        elsif voter_state.fault_ecu = "sub" then
          voter_state := [state |-> "comfortable_stop", fault_ecu |-> "sub", mrm_ecu |-> "main", comfortable_stop_after_switch |-> TRUE];
        else
          voter_state := [state |-> "failed", fault_ecu |-> "unknown", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE];
        end if;
      else
        voter_state := [state |-> "succeeded", fault_ecu |-> voter_state.fault_ecu, mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE];
      end if;
    elsif mrm_operation.fault_ecu = "none" then
      transit_voter_normal();
    elsif mrm_operation.mrm_ecu /= "supervisor" /\ mrm_operation.mrm_ecu /= "none" then \* main or sub comfortable_stop
      if mrm_operation.mrm_ecu /= initial_selected_ecu then \* invalid operation: directory calling comfortable_stop on extra ecu
        transit_voter_unexpected_behavior();
      else
        transit_voter_comfortable_stop();
      end if;
    elsif mrm_operation.mrm_ecu = "supervisor" then
      transit_voter_supervisor_stop(); \* update fault_ecu and comfortable_stop_after_switch flag
    end if;
  \* currently only comfortable_stop is operated in main and sub
  \*--- comfortable stop ---
  elsif voter_state.state = "comfortable_stop" then
    if vehicle_status = "comfortable_stopped" then \* vehicle stopped
      voter_state := [state |-> "succeeded", fault_ecu |-> voter_state.fault_ecu, mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE];
    elsif mrm_operation.fault_ecu = "none" then
      transit_voter_normal();
    elsif mrm_operation.mrm_ecu = "supervisor" then
      if ~voter_state.comfortable_stop_after_switch then
        transit_voter_supervisor_stop();
      end if;
    elsif mrm_operation.mrm_ecu /= "none" then
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

macro operate_mrm_on_voter(current_mrm_ecu)
begin
  \*--- normal ---
  if voter_state.state = "normal" then
    if current_mrm_ecu /= "none" then
      if current_mrm_ecu = "supervisor" then
        emergency_stop_operator_request[current_mrm_ecu] := "cancel";
      else \* if current_mrm_ecu is Main or Sub
        comfortable_stop_operator_request[current_mrm_ecu] := "cancel";
      end if;
      switch.state := initial_selected_ecu;
      current_mrm_ecu := "none";
    end if;
  \*--- supervisor_stop---
  elsif voter_state.state = "supervisor_stop" then
    if current_mrm_ecu /= "supervisor" then
      if current_mrm_ecu /= "none" then
        if comfortable_stop_operator_status[current_mrm_ecu] = "operating" then \* no need to wait canceling: MRM on other ECUs has nothing to do with Supervisor Stop
          comfortable_stop_operator_request[current_mrm_ecu] := "cancel";
        end if;
      end if;
      emergency_stop_operator_request["supervisor"] := "operate";
      if emergency_stop_operator_status["supervisor"] = "operating" then \* if Supervisor Stop running, change switch and current_mrm_ecu
        switch.state := "supervisor";
        current_mrm_ecu := "supervisor";
      end if;
    end if;
  \*--- comfortable_stop---
  elsif voter_state.state = "comfortable_stop" then
    \* MRM operation will be change if mrm_ecu is initial_selected_ecu or not
    if current_mrm_ecu /= voter_state.mrm_ecu then
      if voter_state.mrm_ecu = initial_selected_ecu then
        if emergency_stop_operator_status["supervisor"] = "operating" then \* no need to wait canceling: MRM on other ECUs has nothing to do with Main Comfortable Stop
          emergency_stop_operator_request["supervisor"] := "cancel";
        end if;

        if comfortable_stop_operator_status[extra_ecu] = "operating" then \* if sub comfortable_stop is operating, cancel it (no need to wait)
          if emergency_stop_operator_status[initial_selected_ecu] /= "operating" then \* check whether emergency_stop is running on Main: if not running, operate comfortable stop
            comfortable_stop_operator_request := [main |-> "operate", sub |-> "cancel"];
            if comfortable_stop_operator_status[initial_selected_ecu] = "operating" then
              switch.state := initial_selected_ecu;
              current_mrm_ecu := initial_selected_ecu;
            end if;
          else
            comfortable_stop_operator_request[extra_ecu] := "cancel";
            switch.state := initial_selected_ecu;
            current_mrm_ecu := initial_selected_ecu;
          end if;
        else
          if emergency_stop_operator_status[initial_selected_ecu] /= "operating" then \* check whether emergency_stop is running on Main: if not running, operate comfortable stop
            comfortable_stop_operator_request[initial_selected_ecu] := "operate";
            if comfortable_stop_operator_status[initial_selected_ecu] = "operating" then
              switch.state := initial_selected_ecu;
              current_mrm_ecu := initial_selected_ecu;
            end if;
          end if;
        end if;
      elsif voter_state.mrm_ecu = extra_ecu then
        if emergency_stop_operator_status["supervisor"] = "operating" then \* Voter state transition from Main comfortable_stop to Sub comfortable_stop is rejected in update_voter_state: only need to cancel Supervisor Stop
          emergency_stop_operator_request["supervisor"] := "cancel";
        end if;
        if emergency_stop_operator_status[extra_ecu] /= "operating" then \* check whether emergency_stop is running on Sub: if not running, operate comfortable stop
          comfortable_stop_operator_request[extra_ecu] := "operate";
          if comfortable_stop_operator_status[extra_ecu] = "operating" then
            switch.state := extra_ecu;
            current_mrm_ecu := extra_ecu;
          end if;
        end if;
      end if;
    end if;
  elsif voter_state.state = "succeeded" then
    emergency_stop_operator_request := [main |-> "cancel", sub |-> "cancel", supervisor |-> "cancel"];
    comfortable_stop_operator_request := [main |-> "cancel", sub |-> "cancel"];
    current_mrm_ecu := "none";
  end if;
end macro;

fair process safety_mechanism = "safety_mechanism"
variables
  fault;
begin
  SafetyMechanism:
    while fault_queue /= <<>> do
      fault := Head(fault_queue);
      fault_queue := Tail(fault_queue);
      if fault.fault_ecu_name = "none" then
        if fault.monitoring_type = "self_monitoring" then
          self_faults := [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault];
        else
          external_faults := [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault];
        end if;
      else
        if fault.monitoring_type = "self_monitoring" then
          self_faults[fault.fault_ecu_name] := fault;
        elsif fault.monitoring_type = "external_monitoring" then
          external_faults[fault.fault_ecu_name] := fault;
        end if;
      end if;
    end while;
end process;

(*process self_monitoring \in SelfMonitorings
variables
  ecu =
    IF self = "main_self_monitoring" THEN "main"
    ELSE IF self = "sub_self_monitoring" THEN "sub"
    ELSE "supervisor";
begin
  SelfMonitoring:
    while TRUE do
      monitor(self_faults, self_monitoring_results, ecu);
    end while;
end process;*)

fair process main_self_monitoring = "main_self_monitoring"
variables
  ecu = "main";
begin
  SelfMonitoring:
    while TRUE do
      monitor(self_faults, self_monitoring_results, ecu);
    end while;
end process;

fair process sub_self_monitoring = "sub_self_monitoring"
variables
  ecu = "sub";
begin
  SelfMonitoring:
    while TRUE do
      monitor(self_faults, self_monitoring_results, ecu);
    end while;
end process;

fair process supervisor_self_monitoring = "supervisor_self_monitoring"
variables
  ecu = "supervisor";
begin
  SelfMonitoring:
    while TRUE do
      monitor(self_faults, self_monitoring_results, ecu);
    end while;
end process;


(*process external_monitoring \in ExternalMonitorings
variables
  ecu =
    IF self = "main_external_monitoring" THEN "main"
    ELSE IF self = "sub_external_monitoring" THEN "sub"
    ELSE "supervisor";
begin
  ExternalMonitoring:
    while TRUE do
      monitor(external_faults, external_monitoring_results, ecu);
    end while;
end process;*)

fair process main_external_monitoring = "main_external_monitoring"
variables
  ecu = "main"
begin
  ExternalMonitoring:
    while TRUE do
      monitor(external_faults, external_monitoring_results, ecu);
    end while;
end process;

fair process sub_external_monitoring = "sub_external_monitoring"
variables
  ecu = "sub"
begin
  ExternalMonitoring:
    while TRUE do
      monitor(external_faults, external_monitoring_results, ecu);
    end while;
end process;

fair process supervisor_external_monitoring = "supervisor_external_monitoring"
variables
  ecu = "supervisor"
begin
  ExternalMonitoring:
    while TRUE do
      monitor(external_faults, external_monitoring_results, ecu);
    end while;
end process;

(*process emergency_handler \in EmergencyHandlers
variables
  is_emergency = FALSE,
  current_mrm_behavior = "none",
  mrm_state = "normal",
  mrm_behavior = "none",
  ecu =
    IF self = "main_emergency_handler" THEN "main" ELSE "sub";
begin
  EmergencyHandling:
    while mrm_state /= "succeeded" do
      is_emergency := self_monitoring_results[ecu] /= no_fault;
      update_mrm_state(mrm_state, is_emergency);
      get_current_mrm_behavior(mrm_behavior, self_monitoring_results[ecu], current_mrm_behavior);
      operate_mrm(mrm_state, mrm_behavior, current_mrm_behavior, ecu);
    end while;
end process;*)

fair process main_emergency_handler = "main_emergency_handler"
variables
  is_emergency = FALSE,
  current_mrm_behavior = "none",
  mrm_state = "normal",
  mrm_behavior = "none",
  ecu = "main"
begin
  EmergencyHandling:
    while mrm_state /= "succeeded" do
      is_emergency := self_monitoring_results[ecu] /= no_fault;
      update_mrm_state(mrm_state, is_emergency);
      get_current_mrm_behavior(mrm_behavior, self_monitoring_results[ecu], current_mrm_behavior);
      operate_mrm(mrm_state, mrm_behavior, current_mrm_behavior, ecu);
    end while;
end process;

fair process sub_emergency_handler = "sub_emergency_handler"
variables
  is_emergency = FALSE,
  current_mrm_behavior = "none",
  mrm_state = "normal",
  mrm_behavior = "none",
  ecu = "sub"
begin
  EmergencyHandling:
    while mrm_state /= "succeeded" do
      is_emergency := self_monitoring_results[ecu] /= no_fault;
      update_mrm_state(mrm_state, is_emergency);
      get_current_mrm_behavior(mrm_behavior, self_monitoring_results[ecu], current_mrm_behavior);
      operate_mrm(mrm_state, mrm_behavior, current_mrm_behavior, ecu);
    end while;
end process;


(* process emergency_stop_service \in EmergencyStopServices
variables
ecu =
    IF self = "main_emergency_stop_service" THEN "main"
    ELSE IF self = "sub_emergency_stop_service" THEN "sub"
    ELSE "supervisor";
begin
  EmergencyStopService:
    while TRUE do
      await emergency_stop_operator_request[ecu] /= "none";
      operate_service("emergency_stop", ecu);
    end while;
end process;*)

fair process main_emergency_stop_service = "main_emergency_stop_service"
variables
ecu = "main";
begin
  EmergencyStopService:
    while TRUE do
      await emergency_stop_operator_request[ecu] /= "none";
      operate_service("emergency_stop", ecu);
    end while;
end process;

fair process sub_emergency_stop_service = "sub_emergency_stop_service"
variables
ecu = "sub";
begin
  EmergencyStopService:
    while TRUE do
      await emergency_stop_operator_request[ecu] /= "none";
      operate_service("emergency_stop", ecu);
    end while;
end process;

fair process supervisor_emergency_stop_service = "supervisor_emergency_stop_service"
variables
ecu = "supervisor";
begin
  EmergencyStopService:
    while TRUE do
      await emergency_stop_operator_request[ecu] /= "none";
      operate_service("emergency_stop", ecu);
    end while;
end process;


(*process comfortable_stop_service \in ComfortableStopServices
variables
ecu =
    IF self = "main_comfortable_stop_service" THEN "main" ELSE "sub";
begin
  ComfortableStopService:
    while TRUE do
      await comfortable_stop_operator_request[ecu] /= "none";
      operate_service("comfortable_stop", ecu);
    end while;
end process;*)

fair process main_comfortable_stop_service = "main_comfortable_stop_service"
variables
ecu = "main"
begin
  ComfortableStopService:
    while TRUE do
      await comfortable_stop_operator_request[ecu] /= "none";
      operate_service("comfortable_stop", ecu);
    end while;
end process;

fair process sub_comfortable_stop_service = "sub_comfortable_stop_service"
variables
ecu = "sub"
begin
  ComfortableStopService:
    while TRUE do
      await comfortable_stop_operator_request[ecu] /= "none";
      operate_service("comfortable_stop", ecu);
    end while;
end process;


\* operate emergency_stop or comfortable_stop in each ECU
(*process emergency_stop_operator \in EmergencyStopOperators
variables
  ecu =
    IF self = "main_emergency_stop_operator" THEN "main"
    ELSE IF self = "sub_emergency_stop_operator" THEN "sub"
    ELSE "supervisor";
begin
  OperateEmergencyStop:
    while TRUE do
      if switch.state = ecu then
        if emergency_stop_operator_status[ecu] = "operating" then
          vehicle_status := "emergency_operating";
        else
          vehicle_status := "running";
        end if;
      end if;
    end while;
end process;*)

fair process main_emergency_stop_operator ="main_emergency_stop_operator"
variables
  ecu = "main"
begin
  OperateEmergencyStop:
    while TRUE do
      if switch.state = ecu then
        if vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped" then
          if emergency_stop_operator_status[ecu] = "operating" then
            vehicle_status := "emergency_operating";
          else
            vehicle_status := "running";
          end if;
        end if;
      end if;
    end while;
end process;

fair process sub_emergency_stop_operator ="sub_emergency_stop_operator"
variables
  ecu = "sub"
begin
  OperateEmergencyStop:
    while TRUE do
      if switch.state = ecu then
        if vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped" then
          if emergency_stop_operator_status[ecu] = "operating" then
            vehicle_status := "emergency_operating";
          else
            vehicle_status := "running";
          end if;
        end if;
      end if;
    end while;
end process;

fair process supervisor_emergency_stop_operator ="supervisor_emergency_stop_operator"
variables
  ecu = "supervisor"
begin
  OperateEmergencyStop:
    while TRUE do
      if switch.state = ecu then
        if vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped" then
          if emergency_stop_operator_status[ecu] = "operating" then
            vehicle_status := "emergency_operating";
          else
            vehicle_status := "running";
          end if;
        end if;
      end if;
    end while;
end process;


(*process comfortable_stop_operator \in ComfortableStopOperators
variables
  ecu =
    IF self = "main_comfortable_stop_operator" THEN "main" ELSE "sub";
begin
  OperatecomfortableStop:
    while TRUE do
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
end process;*)

fair process main_comfortable_stop_operator = "main_comfortable_stop_operator"
variables
  ecu = "main";
begin
  OperatecomfortableStop:
    while TRUE do
      if switch.state = ecu then
        if vehicle_status /= "comfortable_stopped" then
          if comfortable_stop_operator_status[ecu] = "operating" then
            if emergency_stop_operator_status[ecu] = "operating" then
              no_operation_during_emergency := FALSE;
            end if;
            vehicle_status := "comfortable_operating";
          elsif vehicle_status /= "emergency_stopped" then
            vehicle_status := "running";
          end if;
        end if;
      end if;
    end while;
end process;

fair process sub_comfortable_stop_operator = "sub_comfortable_stop_operator"
variables
  ecu = "sub";
begin
  OperatecomfortableStop:
    while TRUE do
      if switch.state = ecu then
        if vehicle_status /= "comfortable_stopped" then
          if comfortable_stop_operator_status[ecu] = "operating" then
            if emergency_stop_operator_status[ecu] = "operating" then
              no_operation_during_emergency := FALSE;
            end if;
            vehicle_status := "comfortable_operating";
          elsif vehicle_status /= "emergency_stopped" then
            vehicle_status := "running";
          end if;
        end if;
      end if;
    end while;
end process;



\* decide which ECU to operate MRM
fair process voter = "voter"
variables
  self_monitoring_count = 0,
  main_self_monitoring_int = 0,
  sub_self_monitoring_int = 0,
  supervisor_self_monitoring_int = 0,
  external_monitoring_count = 0,
  main_external_monitoring_int = 0,
  sub_external_monitoring_int = 0,
  supervisor_external_monitoring_int = 0,
  current_mrm_ecu = "none";
begin
  Voter:
    while voter_state.state /= "succeeded" do
      update_self_error_status(self_monitoring_results["main"], main_self_error_status, "main");
      update_self_error_status(self_monitoring_results["sub"], sub_self_error_status, "sub");
      update_self_error_status(self_monitoring_results["supervisor"], supervisor_self_error_status, "supervisor");
      update_external_error_status(external_monitoring_results["main"], main_external_error_status, "main");
      update_external_error_status(external_monitoring_results["sub"], sub_external_error_status, "sub");
      update_external_error_status(external_monitoring_results["supervisor"], supervisor_external_error_status, "supervisor");
      error_status_to_int(main_self_error_status, main_self_monitoring_int);
      error_status_to_int(sub_self_error_status, sub_self_monitoring_int);
      error_status_to_int(supervisor_self_error_status, supervisor_self_monitoring_int);
      error_status_to_int(main_external_error_status, main_external_monitoring_int);
      error_status_to_int(sub_external_error_status, sub_external_monitoring_int);
      error_status_to_int(supervisor_external_error_status, supervisor_external_monitoring_int);
      self_monitoring_count := main_self_monitoring_int + sub_self_monitoring_int + supervisor_self_monitoring_int;
      external_monitoring_count := main_external_monitoring_int + sub_external_monitoring_int + supervisor_external_monitoring_int;

      \* get mrm operation from external monitoring, and then get mrm operation from self monitoring
      if external_monitoring_count = 0 then
        if self_monitoring_count = 0 then
          get_no_mrm_operation();
        elsif self_monitoring_count = 1 then
          if main_self_monitoring_int = 1 then
            get_mrm_operation_internal_ecu(main_self_error_status, "main");
          elsif sub_self_monitoring_int = 1 then
            get_mrm_operation_internal_ecu(sub_self_error_status, "sub");
          else
            get_mrm_operation_internal_ecu(supervisor_self_error_status, "supervisor");
          end if;
        else
          get_mrm_operation_multiple_ecu_error();
        end if;
      else
        if external_monitoring_count = 1 then
          if main_external_monitoring_int = 1 then
            get_mrm_operation_internal_ecu(main_external_error_status, "main");
          elsif sub_external_monitoring_int = 1 then
            get_mrm_operation_internal_ecu(sub_external_error_status, "sub");
          else
            get_mrm_operation_internal_ecu(supervisor_external_error_status, "supervisor");
          end if;
        else
          get_mrm_operation_multiple_ecu_error();
        end if;
      end if;
      update_voter_state();
      operate_mrm_on_voter(current_mrm_ecu);
    end while;
end process;

fair+ process vehicle = "vehicle"
begin
  Vehicle:
    while TRUE do
      if vehicle_status = "emergency_operating" then
        vehicle_status := "emergency_stopped";
      elsif vehicle_status = "comfortable_operating" then
        vehicle_status := "comfortable_stopped";
      end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "dc25c7a8" /\ chksum(tla) = "99dbe43c")
\* Label SelfMonitoring of process main_self_monitoring at line 426 col 5 changed to SelfMonitoring_
\* Label SelfMonitoring of process sub_self_monitoring at line 436 col 5 changed to SelfMonitoring_s
\* Label ExternalMonitoring of process main_external_monitoring at line 470 col 5 changed to ExternalMonitoring_
\* Label ExternalMonitoring of process sub_external_monitoring at line 480 col 5 changed to ExternalMonitoring_s
\* Label EmergencyHandling of process main_emergency_handler at line 522 col 5 changed to EmergencyHandling_
\* Label EmergencyStopService of process main_emergency_stop_service at line 567 col 5 changed to EmergencyStopService_
\* Label EmergencyStopService of process sub_emergency_stop_service at line 578 col 5 changed to EmergencyStopService_s
\* Label ComfortableStopService of process main_comfortable_stop_service at line 613 col 5 changed to ComfortableStopService_
\* Label OperateEmergencyStop of process main_emergency_stop_operator at line 656 col 5 changed to OperateEmergencyStop_
\* Label OperateEmergencyStop of process sub_emergency_stop_operator at line 674 col 5 changed to OperateEmergencyStop_s
\* Label OperatecomfortableStop of process main_comfortable_stop_operator at line 731 col 5 changed to OperatecomfortableStop_
\* Process variable ecu of process main_self_monitoring at line 423 col 3 changed to ecu_
\* Process variable ecu of process sub_self_monitoring at line 433 col 3 changed to ecu_s
\* Process variable ecu of process supervisor_self_monitoring at line 443 col 3 changed to ecu_su
\* Process variable ecu of process main_external_monitoring at line 467 col 3 changed to ecu_m
\* Process variable ecu of process sub_external_monitoring at line 477 col 3 changed to ecu_sub
\* Process variable ecu of process supervisor_external_monitoring at line 487 col 3 changed to ecu_sup
\* Process variable is_emergency of process main_emergency_handler at line 515 col 3 changed to is_emergency_
\* Process variable current_mrm_behavior of process main_emergency_handler at line 516 col 3 changed to current_mrm_behavior_
\* Process variable mrm_state of process main_emergency_handler at line 517 col 3 changed to mrm_state_
\* Process variable mrm_behavior of process main_emergency_handler at line 518 col 3 changed to mrm_behavior_
\* Process variable ecu of process main_emergency_handler at line 519 col 3 changed to ecu_ma
\* Process variable ecu of process sub_emergency_handler at line 536 col 3 changed to ecu_sub_
\* Process variable ecu of process main_emergency_stop_service at line 564 col 1 changed to ecu_mai
\* Process variable ecu of process sub_emergency_stop_service at line 575 col 1 changed to ecu_sub_e
\* Process variable ecu of process supervisor_emergency_stop_service at line 586 col 1 changed to ecu_supe
\* Process variable ecu of process main_comfortable_stop_service at line 610 col 1 changed to ecu_main
\* Process variable ecu of process sub_comfortable_stop_service at line 621 col 1 changed to ecu_sub_c
\* Process variable ecu of process main_emergency_stop_operator at line 653 col 3 changed to ecu_main_
\* Process variable ecu of process sub_emergency_stop_operator at line 671 col 3 changed to ecu_sub_em
\* Process variable ecu of process supervisor_emergency_stop_operator at line 689 col 3 changed to ecu_super
\* Process variable ecu of process main_comfortable_stop_operator at line 728 col 3 changed to ecu_main_c
CONSTANT defaultInitValue
VARIABLES fault_ecu, s_faults, no_faults, e_faults, faults, 
          faults_and_no_faults, fault_queue, no_fault, self_faults, 
          external_faults, EmergencyHandlers, emergency_handler_status, 
          SelfMonitorings, ExternalMonitorings, self_monitoring_results, 
          external_monitoring_results, emergency_stop_operator_request, 
          comfortable_stop_operator_request, EmergencyStopServices, 
          EmergencyStopOperators, ComfortableStopServices, 
          ComfortableStopOperators, emergency_stop_operator_status, 
          comfortable_stop_operator_status, no_error, main_self_error_status, 
          sub_self_error_status, supervisor_self_error_status, 
          main_external_error_status, sub_external_error_status, 
          supervisor_external_error_status, voter_state, mrm_operation, 
          vehicle_status, initial_selected_ecu, extra_ecu, switch, 
          is_stop_operator_succeeded, self_recoverable_flag, 
          no_operation_during_emergency, pc

(* define statement *)
VehicleStopped == <>[](vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped")
NoOperationDuringEmergency == no_operation_during_emergency

VARIABLES fault, ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, ecu_sup, is_emergency_, 
          current_mrm_behavior_, mrm_state_, mrm_behavior_, ecu_ma, 
          is_emergency, current_mrm_behavior, mrm_state, mrm_behavior, 
          ecu_sub_, ecu_mai, ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
          ecu_main_, ecu_sub_em, ecu_super, ecu_main_c, ecu, 
          self_monitoring_count, main_self_monitoring_int, 
          sub_self_monitoring_int, supervisor_self_monitoring_int, 
          external_monitoring_count, main_external_monitoring_int, 
          sub_external_monitoring_int, supervisor_external_monitoring_int, 
          current_mrm_ecu

vars == << fault_ecu, s_faults, no_faults, e_faults, faults, 
           faults_and_no_faults, fault_queue, no_fault, self_faults, 
           external_faults, EmergencyHandlers, emergency_handler_status, 
           SelfMonitorings, ExternalMonitorings, self_monitoring_results, 
           external_monitoring_results, emergency_stop_operator_request, 
           comfortable_stop_operator_request, EmergencyStopServices, 
           EmergencyStopOperators, ComfortableStopServices, 
           ComfortableStopOperators, emergency_stop_operator_status, 
           comfortable_stop_operator_status, no_error, main_self_error_status, 
           sub_self_error_status, supervisor_self_error_status, 
           main_external_error_status, sub_external_error_status, 
           supervisor_external_error_status, voter_state, mrm_operation, 
           vehicle_status, initial_selected_ecu, extra_ecu, switch, 
           is_stop_operator_succeeded, self_recoverable_flag, 
           no_operation_during_emergency, pc, fault, ecu_, ecu_s, ecu_su, 
           ecu_m, ecu_sub, ecu_sup, is_emergency_, current_mrm_behavior_, 
           mrm_state_, mrm_behavior_, ecu_ma, is_emergency, 
           current_mrm_behavior, mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
           ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, ecu_main_, ecu_sub_em, 
           ecu_super, ecu_main_c, ecu, self_monitoring_count, 
           main_self_monitoring_int, sub_self_monitoring_int, 
           supervisor_self_monitoring_int, external_monitoring_count, 
           main_external_monitoring_int, sub_external_monitoring_int, 
           supervisor_external_monitoring_int, current_mrm_ecu >>

ProcSet == {"safety_mechanism"} \cup {"main_self_monitoring"} \cup {"sub_self_monitoring"} \cup {"supervisor_self_monitoring"} \cup {"main_external_monitoring"} \cup {"sub_external_monitoring"} \cup {"supervisor_external_monitoring"} \cup {"main_emergency_handler"} \cup {"sub_emergency_handler"} \cup {"main_emergency_stop_service"} \cup {"sub_emergency_stop_service"} \cup {"supervisor_emergency_stop_service"} \cup {"main_comfortable_stop_service"} \cup {"sub_comfortable_stop_service"} \cup {"main_emergency_stop_operator"} \cup {"sub_emergency_stop_operator"} \cup {"supervisor_emergency_stop_operator"} \cup {"main_comfortable_stop_operator"} \cup {"sub_comfortable_stop_operator"} \cup {"voter"} \cup {"vehicle"}

Init == (* Global variables *)
        /\ fault_ecu \in ECUs
        /\ s_faults = [fault_ecu_name : {fault_ecu}, self_recoverable : {TRUE, FALSE}, fault_behavior : FaultBehaviors, monitoring_type : {"self_monitoring"}]
        /\ no_faults = [fault_ecu_name : {"none"}, self_recoverable : {TRUE}, fault_behavior : {"none"}, monitoring_type : MonitoringTypes]
        /\ e_faults = [fault_ecu_name : {fault_ecu}, self_recoverable : {FALSE}, fault_behavior : {"comfortable_stop"}, monitoring_type : {"external_monitoring"}]
        /\ faults = (s_faults \union e_faults)
        /\ faults_and_no_faults = (faults \union no_faults)
        /\ fault_queue \in faults_and_no_faults \X faults_and_no_faults \X faults_and_no_faults \X faults
        /\ no_fault = [fault_ecu_name |-> "none", fault_behavior |-> "none"]
        /\ self_faults = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
        /\ external_faults = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
        /\ EmergencyHandlers = {"main_emergency_handler", "sub_emergency_handler"}
        /\ emergency_handler_status = [main |-> "none", sub |-> "none"]
        /\ SelfMonitorings = {"main_self_monitoring", "sub_self_monitoring", "supervisor_self_monitoring"}
        /\ ExternalMonitorings = {"main_external_monitoring", "sub_external_monitoring", "supervisor_external_monitoring"}
        /\ self_monitoring_results = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
        /\ external_monitoring_results = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
        /\ emergency_stop_operator_request = [main |-> "none", sub |-> "none", supervisor |-> "none"]
        /\ comfortable_stop_operator_request = [main |-> "none", sub |-> "none"]
        /\ EmergencyStopServices = {"main_emergency_stop_service", "sub_emergency_stop_service", "supervisor_emergency_stop_service"}
        /\ EmergencyStopOperators = {"main_emergency_stop_operator", "sub_emergency_stop_operator", "supervisor_emergency_stop_operator"}
        /\ ComfortableStopServices = {"main_comfortable_stop_service", "sub_comfortable_stop_service"}
        /\ ComfortableStopOperators = {"main_comfortable_stop_operator", "sub_comfortable_stop_operator"}
        /\ emergency_stop_operator_status = [main |-> "available", sub |-> "available", supervisor |-> "available"]
        /\ comfortable_stop_operator_status = [main |-> "available", sub |-> "available", supervisor |-> "available"]
        /\ no_error = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
        /\ main_self_error_status = no_error
        /\ sub_self_error_status = no_error
        /\ supervisor_self_error_status = no_error
        /\ main_external_error_status = no_error
        /\ sub_external_error_status = no_error
        /\ supervisor_external_error_status = no_error
        /\ voter_state = [state |-> "normal", external_detected |-> FALSE, comfortable_stop_after_switch |-> FALSE]
        /\ mrm_operation = [fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
        /\ vehicle_status = "running"
        /\ initial_selected_ecu = "main"
        /\ extra_ecu = "sub"
        /\ switch = [state |-> initial_selected_ecu]
        /\ is_stop_operator_succeeded = FALSE
        /\ self_recoverable_flag = TRUE
        /\ no_operation_during_emergency = TRUE
        (* Process safety_mechanism *)
        /\ fault = defaultInitValue
        (* Process main_self_monitoring *)
        /\ ecu_ = "main"
        (* Process sub_self_monitoring *)
        /\ ecu_s = "sub"
        (* Process supervisor_self_monitoring *)
        /\ ecu_su = "supervisor"
        (* Process main_external_monitoring *)
        /\ ecu_m = "main"
        (* Process sub_external_monitoring *)
        /\ ecu_sub = "sub"
        (* Process supervisor_external_monitoring *)
        /\ ecu_sup = "supervisor"
        (* Process main_emergency_handler *)
        /\ is_emergency_ = FALSE
        /\ current_mrm_behavior_ = "none"
        /\ mrm_state_ = "normal"
        /\ mrm_behavior_ = "none"
        /\ ecu_ma = "main"
        (* Process sub_emergency_handler *)
        /\ is_emergency = FALSE
        /\ current_mrm_behavior = "none"
        /\ mrm_state = "normal"
        /\ mrm_behavior = "none"
        /\ ecu_sub_ = "sub"
        (* Process main_emergency_stop_service *)
        /\ ecu_mai = "main"
        (* Process sub_emergency_stop_service *)
        /\ ecu_sub_e = "sub"
        (* Process supervisor_emergency_stop_service *)
        /\ ecu_supe = "supervisor"
        (* Process main_comfortable_stop_service *)
        /\ ecu_main = "main"
        (* Process sub_comfortable_stop_service *)
        /\ ecu_sub_c = "sub"
        (* Process main_emergency_stop_operator *)
        /\ ecu_main_ = "main"
        (* Process sub_emergency_stop_operator *)
        /\ ecu_sub_em = "sub"
        (* Process supervisor_emergency_stop_operator *)
        /\ ecu_super = "supervisor"
        (* Process main_comfortable_stop_operator *)
        /\ ecu_main_c = "main"
        (* Process sub_comfortable_stop_operator *)
        /\ ecu = "sub"
        (* Process voter *)
        /\ self_monitoring_count = 0
        /\ main_self_monitoring_int = 0
        /\ sub_self_monitoring_int = 0
        /\ supervisor_self_monitoring_int = 0
        /\ external_monitoring_count = 0
        /\ main_external_monitoring_int = 0
        /\ sub_external_monitoring_int = 0
        /\ supervisor_external_monitoring_int = 0
        /\ current_mrm_ecu = "none"
        /\ pc = [self \in ProcSet |-> CASE self = "safety_mechanism" -> "SafetyMechanism"
                                        [] self = "main_self_monitoring" -> "SelfMonitoring_"
                                        [] self = "sub_self_monitoring" -> "SelfMonitoring_s"
                                        [] self = "supervisor_self_monitoring" -> "SelfMonitoring"
                                        [] self = "main_external_monitoring" -> "ExternalMonitoring_"
                                        [] self = "sub_external_monitoring" -> "ExternalMonitoring_s"
                                        [] self = "supervisor_external_monitoring" -> "ExternalMonitoring"
                                        [] self = "main_emergency_handler" -> "EmergencyHandling_"
                                        [] self = "sub_emergency_handler" -> "EmergencyHandling"
                                        [] self = "main_emergency_stop_service" -> "EmergencyStopService_"
                                        [] self = "sub_emergency_stop_service" -> "EmergencyStopService_s"
                                        [] self = "supervisor_emergency_stop_service" -> "EmergencyStopService"
                                        [] self = "main_comfortable_stop_service" -> "ComfortableStopService_"
                                        [] self = "sub_comfortable_stop_service" -> "ComfortableStopService"
                                        [] self = "main_emergency_stop_operator" -> "OperateEmergencyStop_"
                                        [] self = "sub_emergency_stop_operator" -> "OperateEmergencyStop_s"
                                        [] self = "supervisor_emergency_stop_operator" -> "OperateEmergencyStop"
                                        [] self = "main_comfortable_stop_operator" -> "OperatecomfortableStop_"
                                        [] self = "sub_comfortable_stop_operator" -> "OperatecomfortableStop"
                                        [] self = "voter" -> "Voter"
                                        [] self = "vehicle" -> "Vehicle"]

SafetyMechanism == /\ pc["safety_mechanism"] = "SafetyMechanism"
                   /\ IF fault_queue /= <<>>
                         THEN /\ fault' = Head(fault_queue)
                              /\ fault_queue' = Tail(fault_queue)
                              /\ IF fault'.fault_ecu_name = "none"
                                    THEN /\ IF fault'.monitoring_type = "self_monitoring"
                                               THEN /\ self_faults' = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
                                                    /\ UNCHANGED external_faults
                                               ELSE /\ external_faults' = [main |-> no_fault, sub |-> no_fault, supervisor |-> no_fault]
                                                    /\ UNCHANGED self_faults
                                    ELSE /\ IF fault'.monitoring_type = "self_monitoring"
                                               THEN /\ self_faults' = [self_faults EXCEPT ![fault'.fault_ecu_name] = fault']
                                                    /\ UNCHANGED external_faults
                                               ELSE /\ IF fault'.monitoring_type = "external_monitoring"
                                                          THEN /\ external_faults' = [external_faults EXCEPT ![fault'.fault_ecu_name] = fault']
                                                          ELSE /\ TRUE
                                                               /\ UNCHANGED external_faults
                                                    /\ UNCHANGED self_faults
                              /\ pc' = [pc EXCEPT !["safety_mechanism"] = "SafetyMechanism"]
                         ELSE /\ pc' = [pc EXCEPT !["safety_mechanism"] = "Done"]
                              /\ UNCHANGED << fault_queue, self_faults, 
                                              external_faults, fault >>
                   /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                   faults, faults_and_no_faults, no_fault, 
                                   EmergencyHandlers, emergency_handler_status, 
                                   SelfMonitorings, ExternalMonitorings, 
                                   self_monitoring_results, 
                                   external_monitoring_results, 
                                   emergency_stop_operator_request, 
                                   comfortable_stop_operator_request, 
                                   EmergencyStopServices, 
                                   EmergencyStopOperators, 
                                   ComfortableStopServices, 
                                   ComfortableStopOperators, 
                                   emergency_stop_operator_status, 
                                   comfortable_stop_operator_status, no_error, 
                                   main_self_error_status, 
                                   sub_self_error_status, 
                                   supervisor_self_error_status, 
                                   main_external_error_status, 
                                   sub_external_error_status, 
                                   supervisor_external_error_status, 
                                   voter_state, mrm_operation, vehicle_status, 
                                   initial_selected_ecu, extra_ecu, switch, 
                                   is_stop_operator_succeeded, 
                                   self_recoverable_flag, 
                                   no_operation_during_emergency, ecu_, ecu_s, 
                                   ecu_su, ecu_m, ecu_sub, ecu_sup, 
                                   is_emergency_, current_mrm_behavior_, 
                                   mrm_state_, mrm_behavior_, ecu_ma, 
                                   is_emergency, current_mrm_behavior, 
                                   mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
                                   ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                   ecu_main_, ecu_sub_em, ecu_super, 
                                   ecu_main_c, ecu, self_monitoring_count, 
                                   main_self_monitoring_int, 
                                   sub_self_monitoring_int, 
                                   supervisor_self_monitoring_int, 
                                   external_monitoring_count, 
                                   main_external_monitoring_int, 
                                   sub_external_monitoring_int, 
                                   supervisor_external_monitoring_int, 
                                   current_mrm_ecu >>

safety_mechanism == SafetyMechanism

SelfMonitoring_ == /\ pc["main_self_monitoring"] = "SelfMonitoring_"
                   /\ IF self_faults[ecu_].fault_ecu_name = "none"
                         THEN /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_] = no_fault]
                         ELSE /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_] = self_faults[ecu_]]
                   /\ pc' = [pc EXCEPT !["main_self_monitoring"] = "SelfMonitoring_"]
                   /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                   faults, faults_and_no_faults, fault_queue, 
                                   no_fault, self_faults, external_faults, 
                                   EmergencyHandlers, emergency_handler_status, 
                                   SelfMonitorings, ExternalMonitorings, 
                                   external_monitoring_results, 
                                   emergency_stop_operator_request, 
                                   comfortable_stop_operator_request, 
                                   EmergencyStopServices, 
                                   EmergencyStopOperators, 
                                   ComfortableStopServices, 
                                   ComfortableStopOperators, 
                                   emergency_stop_operator_status, 
                                   comfortable_stop_operator_status, no_error, 
                                   main_self_error_status, 
                                   sub_self_error_status, 
                                   supervisor_self_error_status, 
                                   main_external_error_status, 
                                   sub_external_error_status, 
                                   supervisor_external_error_status, 
                                   voter_state, mrm_operation, vehicle_status, 
                                   initial_selected_ecu, extra_ecu, switch, 
                                   is_stop_operator_succeeded, 
                                   self_recoverable_flag, 
                                   no_operation_during_emergency, fault, ecu_, 
                                   ecu_s, ecu_su, ecu_m, ecu_sub, ecu_sup, 
                                   is_emergency_, current_mrm_behavior_, 
                                   mrm_state_, mrm_behavior_, ecu_ma, 
                                   is_emergency, current_mrm_behavior, 
                                   mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
                                   ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                   ecu_main_, ecu_sub_em, ecu_super, 
                                   ecu_main_c, ecu, self_monitoring_count, 
                                   main_self_monitoring_int, 
                                   sub_self_monitoring_int, 
                                   supervisor_self_monitoring_int, 
                                   external_monitoring_count, 
                                   main_external_monitoring_int, 
                                   sub_external_monitoring_int, 
                                   supervisor_external_monitoring_int, 
                                   current_mrm_ecu >>

main_self_monitoring == SelfMonitoring_

SelfMonitoring_s == /\ pc["sub_self_monitoring"] = "SelfMonitoring_s"
                    /\ IF self_faults[ecu_s].fault_ecu_name = "none"
                          THEN /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_s] = no_fault]
                          ELSE /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_s] = self_faults[ecu_s]]
                    /\ pc' = [pc EXCEPT !["sub_self_monitoring"] = "SelfMonitoring_s"]
                    /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                    faults, faults_and_no_faults, fault_queue, 
                                    no_fault, self_faults, external_faults, 
                                    EmergencyHandlers, 
                                    emergency_handler_status, SelfMonitorings, 
                                    ExternalMonitorings, 
                                    external_monitoring_results, 
                                    emergency_stop_operator_request, 
                                    comfortable_stop_operator_request, 
                                    EmergencyStopServices, 
                                    EmergencyStopOperators, 
                                    ComfortableStopServices, 
                                    ComfortableStopOperators, 
                                    emergency_stop_operator_status, 
                                    comfortable_stop_operator_status, no_error, 
                                    main_self_error_status, 
                                    sub_self_error_status, 
                                    supervisor_self_error_status, 
                                    main_external_error_status, 
                                    sub_external_error_status, 
                                    supervisor_external_error_status, 
                                    voter_state, mrm_operation, vehicle_status, 
                                    initial_selected_ecu, extra_ecu, switch, 
                                    is_stop_operator_succeeded, 
                                    self_recoverable_flag, 
                                    no_operation_during_emergency, fault, ecu_, 
                                    ecu_s, ecu_su, ecu_m, ecu_sub, ecu_sup, 
                                    is_emergency_, current_mrm_behavior_, 
                                    mrm_state_, mrm_behavior_, ecu_ma, 
                                    is_emergency, current_mrm_behavior, 
                                    mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
                                    ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                    ecu_main_, ecu_sub_em, ecu_super, 
                                    ecu_main_c, ecu, self_monitoring_count, 
                                    main_self_monitoring_int, 
                                    sub_self_monitoring_int, 
                                    supervisor_self_monitoring_int, 
                                    external_monitoring_count, 
                                    main_external_monitoring_int, 
                                    sub_external_monitoring_int, 
                                    supervisor_external_monitoring_int, 
                                    current_mrm_ecu >>

sub_self_monitoring == SelfMonitoring_s

SelfMonitoring == /\ pc["supervisor_self_monitoring"] = "SelfMonitoring"
                  /\ IF self_faults[ecu_su].fault_ecu_name = "none"
                        THEN /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_su] = no_fault]
                        ELSE /\ self_monitoring_results' = [self_monitoring_results EXCEPT ![ecu_su] = self_faults[ecu_su]]
                  /\ pc' = [pc EXCEPT !["supervisor_self_monitoring"] = "SelfMonitoring"]
                  /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                  faults, faults_and_no_faults, fault_queue, 
                                  no_fault, self_faults, external_faults, 
                                  EmergencyHandlers, emergency_handler_status, 
                                  SelfMonitorings, ExternalMonitorings, 
                                  external_monitoring_results, 
                                  emergency_stop_operator_request, 
                                  comfortable_stop_operator_request, 
                                  EmergencyStopServices, 
                                  EmergencyStopOperators, 
                                  ComfortableStopServices, 
                                  ComfortableStopOperators, 
                                  emergency_stop_operator_status, 
                                  comfortable_stop_operator_status, no_error, 
                                  main_self_error_status, 
                                  sub_self_error_status, 
                                  supervisor_self_error_status, 
                                  main_external_error_status, 
                                  sub_external_error_status, 
                                  supervisor_external_error_status, 
                                  voter_state, mrm_operation, vehicle_status, 
                                  initial_selected_ecu, extra_ecu, switch, 
                                  is_stop_operator_succeeded, 
                                  self_recoverable_flag, 
                                  no_operation_during_emergency, fault, ecu_, 
                                  ecu_s, ecu_su, ecu_m, ecu_sub, ecu_sup, 
                                  is_emergency_, current_mrm_behavior_, 
                                  mrm_state_, mrm_behavior_, ecu_ma, 
                                  is_emergency, current_mrm_behavior, 
                                  mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
                                  ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                  ecu_main_, ecu_sub_em, ecu_super, ecu_main_c, 
                                  ecu, self_monitoring_count, 
                                  main_self_monitoring_int, 
                                  sub_self_monitoring_int, 
                                  supervisor_self_monitoring_int, 
                                  external_monitoring_count, 
                                  main_external_monitoring_int, 
                                  sub_external_monitoring_int, 
                                  supervisor_external_monitoring_int, 
                                  current_mrm_ecu >>

supervisor_self_monitoring == SelfMonitoring

ExternalMonitoring_ == /\ pc["main_external_monitoring"] = "ExternalMonitoring_"
                       /\ IF external_faults[ecu_m].fault_ecu_name = "none"
                             THEN /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_m] = no_fault]
                             ELSE /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_m] = external_faults[ecu_m]]
                       /\ pc' = [pc EXCEPT !["main_external_monitoring"] = "ExternalMonitoring_"]
                       /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                       e_faults, faults, faults_and_no_faults, 
                                       fault_queue, no_fault, self_faults, 
                                       external_faults, EmergencyHandlers, 
                                       emergency_handler_status, 
                                       SelfMonitorings, ExternalMonitorings, 
                                       self_monitoring_results, 
                                       emergency_stop_operator_request, 
                                       comfortable_stop_operator_request, 
                                       EmergencyStopServices, 
                                       EmergencyStopOperators, 
                                       ComfortableStopServices, 
                                       ComfortableStopOperators, 
                                       emergency_stop_operator_status, 
                                       comfortable_stop_operator_status, 
                                       no_error, main_self_error_status, 
                                       sub_self_error_status, 
                                       supervisor_self_error_status, 
                                       main_external_error_status, 
                                       sub_external_error_status, 
                                       supervisor_external_error_status, 
                                       voter_state, mrm_operation, 
                                       vehicle_status, initial_selected_ecu, 
                                       extra_ecu, switch, 
                                       is_stop_operator_succeeded, 
                                       self_recoverable_flag, 
                                       no_operation_during_emergency, fault, 
                                       ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                       ecu_sup, is_emergency_, 
                                       current_mrm_behavior_, mrm_state_, 
                                       mrm_behavior_, ecu_ma, is_emergency, 
                                       current_mrm_behavior, mrm_state, 
                                       mrm_behavior, ecu_sub_, ecu_mai, 
                                       ecu_sub_e, ecu_supe, ecu_main, 
                                       ecu_sub_c, ecu_main_, ecu_sub_em, 
                                       ecu_super, ecu_main_c, ecu, 
                                       self_monitoring_count, 
                                       main_self_monitoring_int, 
                                       sub_self_monitoring_int, 
                                       supervisor_self_monitoring_int, 
                                       external_monitoring_count, 
                                       main_external_monitoring_int, 
                                       sub_external_monitoring_int, 
                                       supervisor_external_monitoring_int, 
                                       current_mrm_ecu >>

main_external_monitoring == ExternalMonitoring_

ExternalMonitoring_s == /\ pc["sub_external_monitoring"] = "ExternalMonitoring_s"
                        /\ IF external_faults[ecu_sub].fault_ecu_name = "none"
                              THEN /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_sub] = no_fault]
                              ELSE /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_sub] = external_faults[ecu_sub]]
                        /\ pc' = [pc EXCEPT !["sub_external_monitoring"] = "ExternalMonitoring_s"]
                        /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                        e_faults, faults, faults_and_no_faults, 
                                        fault_queue, no_fault, self_faults, 
                                        external_faults, EmergencyHandlers, 
                                        emergency_handler_status, 
                                        SelfMonitorings, ExternalMonitorings, 
                                        self_monitoring_results, 
                                        emergency_stop_operator_request, 
                                        comfortable_stop_operator_request, 
                                        EmergencyStopServices, 
                                        EmergencyStopOperators, 
                                        ComfortableStopServices, 
                                        ComfortableStopOperators, 
                                        emergency_stop_operator_status, 
                                        comfortable_stop_operator_status, 
                                        no_error, main_self_error_status, 
                                        sub_self_error_status, 
                                        supervisor_self_error_status, 
                                        main_external_error_status, 
                                        sub_external_error_status, 
                                        supervisor_external_error_status, 
                                        voter_state, mrm_operation, 
                                        vehicle_status, initial_selected_ecu, 
                                        extra_ecu, switch, 
                                        is_stop_operator_succeeded, 
                                        self_recoverable_flag, 
                                        no_operation_during_emergency, fault, 
                                        ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                        ecu_sup, is_emergency_, 
                                        current_mrm_behavior_, mrm_state_, 
                                        mrm_behavior_, ecu_ma, is_emergency, 
                                        current_mrm_behavior, mrm_state, 
                                        mrm_behavior, ecu_sub_, ecu_mai, 
                                        ecu_sub_e, ecu_supe, ecu_main, 
                                        ecu_sub_c, ecu_main_, ecu_sub_em, 
                                        ecu_super, ecu_main_c, ecu, 
                                        self_monitoring_count, 
                                        main_self_monitoring_int, 
                                        sub_self_monitoring_int, 
                                        supervisor_self_monitoring_int, 
                                        external_monitoring_count, 
                                        main_external_monitoring_int, 
                                        sub_external_monitoring_int, 
                                        supervisor_external_monitoring_int, 
                                        current_mrm_ecu >>

sub_external_monitoring == ExternalMonitoring_s

ExternalMonitoring == /\ pc["supervisor_external_monitoring"] = "ExternalMonitoring"
                      /\ IF external_faults[ecu_sup].fault_ecu_name = "none"
                            THEN /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_sup] = no_fault]
                            ELSE /\ external_monitoring_results' = [external_monitoring_results EXCEPT ![ecu_sup] = external_faults[ecu_sup]]
                      /\ pc' = [pc EXCEPT !["supervisor_external_monitoring"] = "ExternalMonitoring"]
                      /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                      faults, faults_and_no_faults, 
                                      fault_queue, no_fault, self_faults, 
                                      external_faults, EmergencyHandlers, 
                                      emergency_handler_status, 
                                      SelfMonitorings, ExternalMonitorings, 
                                      self_monitoring_results, 
                                      emergency_stop_operator_request, 
                                      comfortable_stop_operator_request, 
                                      EmergencyStopServices, 
                                      EmergencyStopOperators, 
                                      ComfortableStopServices, 
                                      ComfortableStopOperators, 
                                      emergency_stop_operator_status, 
                                      comfortable_stop_operator_status, 
                                      no_error, main_self_error_status, 
                                      sub_self_error_status, 
                                      supervisor_self_error_status, 
                                      main_external_error_status, 
                                      sub_external_error_status, 
                                      supervisor_external_error_status, 
                                      voter_state, mrm_operation, 
                                      vehicle_status, initial_selected_ecu, 
                                      extra_ecu, switch, 
                                      is_stop_operator_succeeded, 
                                      self_recoverable_flag, 
                                      no_operation_during_emergency, fault, 
                                      ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                      ecu_sup, is_emergency_, 
                                      current_mrm_behavior_, mrm_state_, 
                                      mrm_behavior_, ecu_ma, is_emergency, 
                                      current_mrm_behavior, mrm_state, 
                                      mrm_behavior, ecu_sub_, ecu_mai, 
                                      ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                      ecu_main_, ecu_sub_em, ecu_super, 
                                      ecu_main_c, ecu, self_monitoring_count, 
                                      main_self_monitoring_int, 
                                      sub_self_monitoring_int, 
                                      supervisor_self_monitoring_int, 
                                      external_monitoring_count, 
                                      main_external_monitoring_int, 
                                      sub_external_monitoring_int, 
                                      supervisor_external_monitoring_int, 
                                      current_mrm_ecu >>

supervisor_external_monitoring == ExternalMonitoring

EmergencyHandling_ == /\ pc["main_emergency_handler"] = "EmergencyHandling_"
                      /\ IF mrm_state_ /= "succeeded"
                            THEN /\ is_emergency_' = (self_monitoring_results[ecu_ma] /= no_fault)
                                 /\ IF mrm_state_ = "normal"
                                       THEN /\ IF is_emergency_'
                                                  THEN /\ mrm_state_' = "operating"
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED mrm_state_
                                       ELSE /\ IF ~is_emergency_'
                                                  THEN /\ mrm_state_' = "normal"
                                                  ELSE /\ IF mrm_state_ = "operating"
                                                             THEN /\ IF vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped"
                                                                        THEN /\ mrm_state_' = "succeeded"
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED mrm_state_
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED mrm_state_
                                 /\ IF mrm_behavior_ = "none"
                                       THEN /\ IF (self_monitoring_results[ecu_ma]).fault_behavior = "comfortable_stop"
                                                  THEN /\ current_mrm_behavior_' = "comfortable_stop"
                                                  ELSE /\ IF (self_monitoring_results[ecu_ma]).fault_behavior = "emergency_stop"
                                                             THEN /\ current_mrm_behavior_' = "emergency_stop"
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED current_mrm_behavior_
                                       ELSE /\ IF mrm_behavior_ = "comfortable_stop"
                                                  THEN /\ IF (self_monitoring_results[ecu_ma]).fault_behavior = "emergency_stop"
                                                             THEN /\ current_mrm_behavior_' = "emergency_stop"
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED current_mrm_behavior_
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED current_mrm_behavior_
                                 /\ IF mrm_state_' = "normal"
                                       THEN /\ IF mrm_behavior_ /= "none"
                                                  THEN /\ IF mrm_behavior_ = "emergency_stop"
                                                             THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_ma] = "cancel"]
                                                                  /\ UNCHANGED comfortable_stop_operator_request
                                                             ELSE /\ IF mrm_behavior_ = "comfortable_stop"
                                                                        THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_ma] = "cancel"]
                                                                        ELSE /\ TRUE
                                                                             /\ UNCHANGED comfortable_stop_operator_request
                                                                  /\ UNCHANGED emergency_stop_operator_request
                                                       /\ mrm_behavior_' = "none"
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << emergency_stop_operator_request, 
                                                                       comfortable_stop_operator_request, 
                                                                       mrm_behavior_ >>
                                       ELSE /\ IF mrm_state_' = "operating"
                                                  THEN /\ IF current_mrm_behavior_' /= mrm_behavior_
                                                             THEN /\ IF mrm_behavior_ = "emergency_stop"
                                                                        THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_ma] = "cancel"]
                                                                             /\ IF current_mrm_behavior_' = "comfortable_stop"
                                                                                   THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_ma] = "operate"]
                                                                                   ELSE /\ TRUE
                                                                                        /\ UNCHANGED comfortable_stop_operator_request
                                                                        ELSE /\ IF mrm_behavior_ = "comfortable_stop"
                                                                                   THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_ma] = "cancel"]
                                                                                        /\ IF current_mrm_behavior_' = "emergency_stop"
                                                                                              THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_ma] = "operate"]
                                                                                              ELSE /\ TRUE
                                                                                                   /\ UNCHANGED emergency_stop_operator_request
                                                                                   ELSE /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_ma] = "operate"]
                                                                                        /\ UNCHANGED comfortable_stop_operator_request
                                                                  /\ mrm_behavior_' = current_mrm_behavior_'
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED << emergency_stop_operator_request, 
                                                                                  comfortable_stop_operator_request, 
                                                                                  mrm_behavior_ >>
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << emergency_stop_operator_request, 
                                                                       comfortable_stop_operator_request, 
                                                                       mrm_behavior_ >>
                                 /\ pc' = [pc EXCEPT !["main_emergency_handler"] = "EmergencyHandling_"]
                            ELSE /\ pc' = [pc EXCEPT !["main_emergency_handler"] = "Done"]
                                 /\ UNCHANGED << emergency_stop_operator_request, 
                                                 comfortable_stop_operator_request, 
                                                 is_emergency_, 
                                                 current_mrm_behavior_, 
                                                 mrm_state_, mrm_behavior_ >>
                      /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                      faults, faults_and_no_faults, 
                                      fault_queue, no_fault, self_faults, 
                                      external_faults, EmergencyHandlers, 
                                      emergency_handler_status, 
                                      SelfMonitorings, ExternalMonitorings, 
                                      self_monitoring_results, 
                                      external_monitoring_results, 
                                      EmergencyStopServices, 
                                      EmergencyStopOperators, 
                                      ComfortableStopServices, 
                                      ComfortableStopOperators, 
                                      emergency_stop_operator_status, 
                                      comfortable_stop_operator_status, 
                                      no_error, main_self_error_status, 
                                      sub_self_error_status, 
                                      supervisor_self_error_status, 
                                      main_external_error_status, 
                                      sub_external_error_status, 
                                      supervisor_external_error_status, 
                                      voter_state, mrm_operation, 
                                      vehicle_status, initial_selected_ecu, 
                                      extra_ecu, switch, 
                                      is_stop_operator_succeeded, 
                                      self_recoverable_flag, 
                                      no_operation_during_emergency, fault, 
                                      ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                      ecu_sup, ecu_ma, is_emergency, 
                                      current_mrm_behavior, mrm_state, 
                                      mrm_behavior, ecu_sub_, ecu_mai, 
                                      ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                      ecu_main_, ecu_sub_em, ecu_super, 
                                      ecu_main_c, ecu, self_monitoring_count, 
                                      main_self_monitoring_int, 
                                      sub_self_monitoring_int, 
                                      supervisor_self_monitoring_int, 
                                      external_monitoring_count, 
                                      main_external_monitoring_int, 
                                      sub_external_monitoring_int, 
                                      supervisor_external_monitoring_int, 
                                      current_mrm_ecu >>

main_emergency_handler == EmergencyHandling_

EmergencyHandling == /\ pc["sub_emergency_handler"] = "EmergencyHandling"
                     /\ IF mrm_state /= "succeeded"
                           THEN /\ is_emergency' = (self_monitoring_results[ecu_sub_] /= no_fault)
                                /\ IF mrm_state = "normal"
                                      THEN /\ IF is_emergency'
                                                 THEN /\ mrm_state' = "operating"
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED mrm_state
                                      ELSE /\ IF ~is_emergency'
                                                 THEN /\ mrm_state' = "normal"
                                                 ELSE /\ IF mrm_state = "operating"
                                                            THEN /\ IF vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped"
                                                                       THEN /\ mrm_state' = "succeeded"
                                                                       ELSE /\ TRUE
                                                                            /\ UNCHANGED mrm_state
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED mrm_state
                                /\ IF mrm_behavior = "none"
                                      THEN /\ IF (self_monitoring_results[ecu_sub_]).fault_behavior = "comfortable_stop"
                                                 THEN /\ current_mrm_behavior' = "comfortable_stop"
                                                 ELSE /\ IF (self_monitoring_results[ecu_sub_]).fault_behavior = "emergency_stop"
                                                            THEN /\ current_mrm_behavior' = "emergency_stop"
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED current_mrm_behavior
                                      ELSE /\ IF mrm_behavior = "comfortable_stop"
                                                 THEN /\ IF (self_monitoring_results[ecu_sub_]).fault_behavior = "emergency_stop"
                                                            THEN /\ current_mrm_behavior' = "emergency_stop"
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED current_mrm_behavior
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED current_mrm_behavior
                                /\ IF mrm_state' = "normal"
                                      THEN /\ IF mrm_behavior /= "none"
                                                 THEN /\ IF mrm_behavior = "emergency_stop"
                                                            THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_] = "cancel"]
                                                                 /\ UNCHANGED comfortable_stop_operator_request
                                                            ELSE /\ IF mrm_behavior = "comfortable_stop"
                                                                       THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_sub_] = "cancel"]
                                                                       ELSE /\ TRUE
                                                                            /\ UNCHANGED comfortable_stop_operator_request
                                                                 /\ UNCHANGED emergency_stop_operator_request
                                                      /\ mrm_behavior' = "none"
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << emergency_stop_operator_request, 
                                                                      comfortable_stop_operator_request, 
                                                                      mrm_behavior >>
                                      ELSE /\ IF mrm_state' = "operating"
                                                 THEN /\ IF current_mrm_behavior' /= mrm_behavior
                                                            THEN /\ IF mrm_behavior = "emergency_stop"
                                                                       THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_] = "cancel"]
                                                                            /\ IF current_mrm_behavior' = "comfortable_stop"
                                                                                  THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_sub_] = "operate"]
                                                                                  ELSE /\ TRUE
                                                                                       /\ UNCHANGED comfortable_stop_operator_request
                                                                       ELSE /\ IF mrm_behavior = "comfortable_stop"
                                                                                  THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_sub_] = "cancel"]
                                                                                       /\ IF current_mrm_behavior' = "emergency_stop"
                                                                                             THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_] = "operate"]
                                                                                             ELSE /\ TRUE
                                                                                                  /\ UNCHANGED emergency_stop_operator_request
                                                                                  ELSE /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_] = "operate"]
                                                                                       /\ UNCHANGED comfortable_stop_operator_request
                                                                 /\ mrm_behavior' = current_mrm_behavior'
                                                            ELSE /\ TRUE
                                                                 /\ UNCHANGED << emergency_stop_operator_request, 
                                                                                 comfortable_stop_operator_request, 
                                                                                 mrm_behavior >>
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED << emergency_stop_operator_request, 
                                                                      comfortable_stop_operator_request, 
                                                                      mrm_behavior >>
                                /\ pc' = [pc EXCEPT !["sub_emergency_handler"] = "EmergencyHandling"]
                           ELSE /\ pc' = [pc EXCEPT !["sub_emergency_handler"] = "Done"]
                                /\ UNCHANGED << emergency_stop_operator_request, 
                                                comfortable_stop_operator_request, 
                                                is_emergency, 
                                                current_mrm_behavior, 
                                                mrm_state, mrm_behavior >>
                     /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, 
                                     faults, faults_and_no_faults, fault_queue, 
                                     no_fault, self_faults, external_faults, 
                                     EmergencyHandlers, 
                                     emergency_handler_status, SelfMonitorings, 
                                     ExternalMonitorings, 
                                     self_monitoring_results, 
                                     external_monitoring_results, 
                                     EmergencyStopServices, 
                                     EmergencyStopOperators, 
                                     ComfortableStopServices, 
                                     ComfortableStopOperators, 
                                     emergency_stop_operator_status, 
                                     comfortable_stop_operator_status, 
                                     no_error, main_self_error_status, 
                                     sub_self_error_status, 
                                     supervisor_self_error_status, 
                                     main_external_error_status, 
                                     sub_external_error_status, 
                                     supervisor_external_error_status, 
                                     voter_state, mrm_operation, 
                                     vehicle_status, initial_selected_ecu, 
                                     extra_ecu, switch, 
                                     is_stop_operator_succeeded, 
                                     self_recoverable_flag, 
                                     no_operation_during_emergency, fault, 
                                     ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                     ecu_sup, is_emergency_, 
                                     current_mrm_behavior_, mrm_state_, 
                                     mrm_behavior_, ecu_ma, ecu_sub_, ecu_mai, 
                                     ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, 
                                     ecu_main_, ecu_sub_em, ecu_super, 
                                     ecu_main_c, ecu, self_monitoring_count, 
                                     main_self_monitoring_int, 
                                     sub_self_monitoring_int, 
                                     supervisor_self_monitoring_int, 
                                     external_monitoring_count, 
                                     main_external_monitoring_int, 
                                     sub_external_monitoring_int, 
                                     supervisor_external_monitoring_int, 
                                     current_mrm_ecu >>

sub_emergency_handler == EmergencyHandling

EmergencyStopService_ == /\ pc["main_emergency_stop_service"] = "EmergencyStopService_"
                         /\ emergency_stop_operator_request[ecu_mai] /= "none"
                         /\ IF "emergency_stop" = "emergency_stop"
                               THEN /\ IF emergency_stop_operator_request[ecu_mai] = "operate"
                                          THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_mai] = "operating"]
                                          ELSE /\ IF emergency_stop_operator_request[ecu_mai] = "cancel"
                                                     THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_mai] = "available"]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED emergency_stop_operator_status
                                    /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_mai] = "none"]
                                    /\ UNCHANGED << comfortable_stop_operator_request, 
                                                    comfortable_stop_operator_status >>
                               ELSE /\ IF "emergency_stop" = "comfortable_stop"
                                          THEN /\ IF comfortable_stop_operator_request[ecu_mai] = "operate"
                                                     THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_mai] = "operating"]
                                                     ELSE /\ IF comfortable_stop_operator_request[ecu_mai] = "cancel"
                                                                THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_mai] = "available"]
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED comfortable_stop_operator_status
                                               /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_mai] = "none"]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << comfortable_stop_operator_request, 
                                                               comfortable_stop_operator_status >>
                                    /\ UNCHANGED << emergency_stop_operator_request, 
                                                    emergency_stop_operator_status >>
                         /\ pc' = [pc EXCEPT !["main_emergency_stop_service"] = "EmergencyStopService_"]
                         /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                         e_faults, faults, 
                                         faults_and_no_faults, fault_queue, 
                                         no_fault, self_faults, 
                                         external_faults, EmergencyHandlers, 
                                         emergency_handler_status, 
                                         SelfMonitorings, ExternalMonitorings, 
                                         self_monitoring_results, 
                                         external_monitoring_results, 
                                         EmergencyStopServices, 
                                         EmergencyStopOperators, 
                                         ComfortableStopServices, 
                                         ComfortableStopOperators, no_error, 
                                         main_self_error_status, 
                                         sub_self_error_status, 
                                         supervisor_self_error_status, 
                                         main_external_error_status, 
                                         sub_external_error_status, 
                                         supervisor_external_error_status, 
                                         voter_state, mrm_operation, 
                                         vehicle_status, initial_selected_ecu, 
                                         extra_ecu, switch, 
                                         is_stop_operator_succeeded, 
                                         self_recoverable_flag, 
                                         no_operation_during_emergency, fault, 
                                         ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                         ecu_sup, is_emergency_, 
                                         current_mrm_behavior_, mrm_state_, 
                                         mrm_behavior_, ecu_ma, is_emergency, 
                                         current_mrm_behavior, mrm_state, 
                                         mrm_behavior, ecu_sub_, ecu_mai, 
                                         ecu_sub_e, ecu_supe, ecu_main, 
                                         ecu_sub_c, ecu_main_, ecu_sub_em, 
                                         ecu_super, ecu_main_c, ecu, 
                                         self_monitoring_count, 
                                         main_self_monitoring_int, 
                                         sub_self_monitoring_int, 
                                         supervisor_self_monitoring_int, 
                                         external_monitoring_count, 
                                         main_external_monitoring_int, 
                                         sub_external_monitoring_int, 
                                         supervisor_external_monitoring_int, 
                                         current_mrm_ecu >>

main_emergency_stop_service == EmergencyStopService_

EmergencyStopService_s == /\ pc["sub_emergency_stop_service"] = "EmergencyStopService_s"
                          /\ emergency_stop_operator_request[ecu_sub_e] /= "none"
                          /\ IF "emergency_stop" = "emergency_stop"
                                THEN /\ IF emergency_stop_operator_request[ecu_sub_e] = "operate"
                                           THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_sub_e] = "operating"]
                                           ELSE /\ IF emergency_stop_operator_request[ecu_sub_e] = "cancel"
                                                      THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_sub_e] = "available"]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED emergency_stop_operator_status
                                     /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_e] = "none"]
                                     /\ UNCHANGED << comfortable_stop_operator_request, 
                                                     comfortable_stop_operator_status >>
                                ELSE /\ IF "emergency_stop" = "comfortable_stop"
                                           THEN /\ IF comfortable_stop_operator_request[ecu_sub_e] = "operate"
                                                      THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_sub_e] = "operating"]
                                                      ELSE /\ IF comfortable_stop_operator_request[ecu_sub_e] = "cancel"
                                                                 THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_sub_e] = "available"]
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED comfortable_stop_operator_status
                                                /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_sub_e] = "none"]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << comfortable_stop_operator_request, 
                                                                comfortable_stop_operator_status >>
                                     /\ UNCHANGED << emergency_stop_operator_request, 
                                                     emergency_stop_operator_status >>
                          /\ pc' = [pc EXCEPT !["sub_emergency_stop_service"] = "EmergencyStopService_s"]
                          /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                          e_faults, faults, 
                                          faults_and_no_faults, fault_queue, 
                                          no_fault, self_faults, 
                                          external_faults, EmergencyHandlers, 
                                          emergency_handler_status, 
                                          SelfMonitorings, ExternalMonitorings, 
                                          self_monitoring_results, 
                                          external_monitoring_results, 
                                          EmergencyStopServices, 
                                          EmergencyStopOperators, 
                                          ComfortableStopServices, 
                                          ComfortableStopOperators, no_error, 
                                          main_self_error_status, 
                                          sub_self_error_status, 
                                          supervisor_self_error_status, 
                                          main_external_error_status, 
                                          sub_external_error_status, 
                                          supervisor_external_error_status, 
                                          voter_state, mrm_operation, 
                                          vehicle_status, initial_selected_ecu, 
                                          extra_ecu, switch, 
                                          is_stop_operator_succeeded, 
                                          self_recoverable_flag, 
                                          no_operation_during_emergency, fault, 
                                          ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                          ecu_sup, is_emergency_, 
                                          current_mrm_behavior_, mrm_state_, 
                                          mrm_behavior_, ecu_ma, is_emergency, 
                                          current_mrm_behavior, mrm_state, 
                                          mrm_behavior, ecu_sub_, ecu_mai, 
                                          ecu_sub_e, ecu_supe, ecu_main, 
                                          ecu_sub_c, ecu_main_, ecu_sub_em, 
                                          ecu_super, ecu_main_c, ecu, 
                                          self_monitoring_count, 
                                          main_self_monitoring_int, 
                                          sub_self_monitoring_int, 
                                          supervisor_self_monitoring_int, 
                                          external_monitoring_count, 
                                          main_external_monitoring_int, 
                                          sub_external_monitoring_int, 
                                          supervisor_external_monitoring_int, 
                                          current_mrm_ecu >>

sub_emergency_stop_service == EmergencyStopService_s

EmergencyStopService == /\ pc["supervisor_emergency_stop_service"] = "EmergencyStopService"
                        /\ emergency_stop_operator_request[ecu_supe] /= "none"
                        /\ IF "emergency_stop" = "emergency_stop"
                              THEN /\ IF emergency_stop_operator_request[ecu_supe] = "operate"
                                         THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_supe] = "operating"]
                                         ELSE /\ IF emergency_stop_operator_request[ecu_supe] = "cancel"
                                                    THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_supe] = "available"]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED emergency_stop_operator_status
                                   /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_supe] = "none"]
                                   /\ UNCHANGED << comfortable_stop_operator_request, 
                                                   comfortable_stop_operator_status >>
                              ELSE /\ IF "emergency_stop" = "comfortable_stop"
                                         THEN /\ IF comfortable_stop_operator_request[ecu_supe] = "operate"
                                                    THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_supe] = "operating"]
                                                    ELSE /\ IF comfortable_stop_operator_request[ecu_supe] = "cancel"
                                                               THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_supe] = "available"]
                                                               ELSE /\ TRUE
                                                                    /\ UNCHANGED comfortable_stop_operator_status
                                              /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_supe] = "none"]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << comfortable_stop_operator_request, 
                                                              comfortable_stop_operator_status >>
                                   /\ UNCHANGED << emergency_stop_operator_request, 
                                                   emergency_stop_operator_status >>
                        /\ pc' = [pc EXCEPT !["supervisor_emergency_stop_service"] = "EmergencyStopService"]
                        /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                        e_faults, faults, faults_and_no_faults, 
                                        fault_queue, no_fault, self_faults, 
                                        external_faults, EmergencyHandlers, 
                                        emergency_handler_status, 
                                        SelfMonitorings, ExternalMonitorings, 
                                        self_monitoring_results, 
                                        external_monitoring_results, 
                                        EmergencyStopServices, 
                                        EmergencyStopOperators, 
                                        ComfortableStopServices, 
                                        ComfortableStopOperators, no_error, 
                                        main_self_error_status, 
                                        sub_self_error_status, 
                                        supervisor_self_error_status, 
                                        main_external_error_status, 
                                        sub_external_error_status, 
                                        supervisor_external_error_status, 
                                        voter_state, mrm_operation, 
                                        vehicle_status, initial_selected_ecu, 
                                        extra_ecu, switch, 
                                        is_stop_operator_succeeded, 
                                        self_recoverable_flag, 
                                        no_operation_during_emergency, fault, 
                                        ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                        ecu_sup, is_emergency_, 
                                        current_mrm_behavior_, mrm_state_, 
                                        mrm_behavior_, ecu_ma, is_emergency, 
                                        current_mrm_behavior, mrm_state, 
                                        mrm_behavior, ecu_sub_, ecu_mai, 
                                        ecu_sub_e, ecu_supe, ecu_main, 
                                        ecu_sub_c, ecu_main_, ecu_sub_em, 
                                        ecu_super, ecu_main_c, ecu, 
                                        self_monitoring_count, 
                                        main_self_monitoring_int, 
                                        sub_self_monitoring_int, 
                                        supervisor_self_monitoring_int, 
                                        external_monitoring_count, 
                                        main_external_monitoring_int, 
                                        sub_external_monitoring_int, 
                                        supervisor_external_monitoring_int, 
                                        current_mrm_ecu >>

supervisor_emergency_stop_service == EmergencyStopService

ComfortableStopService_ == /\ pc["main_comfortable_stop_service"] = "ComfortableStopService_"
                           /\ comfortable_stop_operator_request[ecu_main] /= "none"
                           /\ IF "comfortable_stop" = "emergency_stop"
                                 THEN /\ IF emergency_stop_operator_request[ecu_main] = "operate"
                                            THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_main] = "operating"]
                                            ELSE /\ IF emergency_stop_operator_request[ecu_main] = "cancel"
                                                       THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_main] = "available"]
                                                       ELSE /\ TRUE
                                                            /\ UNCHANGED emergency_stop_operator_status
                                      /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_main] = "none"]
                                      /\ UNCHANGED << comfortable_stop_operator_request, 
                                                      comfortable_stop_operator_status >>
                                 ELSE /\ IF "comfortable_stop" = "comfortable_stop"
                                            THEN /\ IF comfortable_stop_operator_request[ecu_main] = "operate"
                                                       THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_main] = "operating"]
                                                       ELSE /\ IF comfortable_stop_operator_request[ecu_main] = "cancel"
                                                                  THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_main] = "available"]
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED comfortable_stop_operator_status
                                                 /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_main] = "none"]
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << comfortable_stop_operator_request, 
                                                                 comfortable_stop_operator_status >>
                                      /\ UNCHANGED << emergency_stop_operator_request, 
                                                      emergency_stop_operator_status >>
                           /\ pc' = [pc EXCEPT !["main_comfortable_stop_service"] = "ComfortableStopService_"]
                           /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                           e_faults, faults, 
                                           faults_and_no_faults, fault_queue, 
                                           no_fault, self_faults, 
                                           external_faults, EmergencyHandlers, 
                                           emergency_handler_status, 
                                           SelfMonitorings, 
                                           ExternalMonitorings, 
                                           self_monitoring_results, 
                                           external_monitoring_results, 
                                           EmergencyStopServices, 
                                           EmergencyStopOperators, 
                                           ComfortableStopServices, 
                                           ComfortableStopOperators, no_error, 
                                           main_self_error_status, 
                                           sub_self_error_status, 
                                           supervisor_self_error_status, 
                                           main_external_error_status, 
                                           sub_external_error_status, 
                                           supervisor_external_error_status, 
                                           voter_state, mrm_operation, 
                                           vehicle_status, 
                                           initial_selected_ecu, extra_ecu, 
                                           switch, is_stop_operator_succeeded, 
                                           self_recoverable_flag, 
                                           no_operation_during_emergency, 
                                           fault, ecu_, ecu_s, ecu_su, ecu_m, 
                                           ecu_sub, ecu_sup, is_emergency_, 
                                           current_mrm_behavior_, mrm_state_, 
                                           mrm_behavior_, ecu_ma, is_emergency, 
                                           current_mrm_behavior, mrm_state, 
                                           mrm_behavior, ecu_sub_, ecu_mai, 
                                           ecu_sub_e, ecu_supe, ecu_main, 
                                           ecu_sub_c, ecu_main_, ecu_sub_em, 
                                           ecu_super, ecu_main_c, ecu, 
                                           self_monitoring_count, 
                                           main_self_monitoring_int, 
                                           sub_self_monitoring_int, 
                                           supervisor_self_monitoring_int, 
                                           external_monitoring_count, 
                                           main_external_monitoring_int, 
                                           sub_external_monitoring_int, 
                                           supervisor_external_monitoring_int, 
                                           current_mrm_ecu >>

main_comfortable_stop_service == ComfortableStopService_

ComfortableStopService == /\ pc["sub_comfortable_stop_service"] = "ComfortableStopService"
                          /\ comfortable_stop_operator_request[ecu_sub_c] /= "none"
                          /\ IF "comfortable_stop" = "emergency_stop"
                                THEN /\ IF emergency_stop_operator_request[ecu_sub_c] = "operate"
                                           THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_sub_c] = "operating"]
                                           ELSE /\ IF emergency_stop_operator_request[ecu_sub_c] = "cancel"
                                                      THEN /\ emergency_stop_operator_status' = [emergency_stop_operator_status EXCEPT ![ecu_sub_c] = "available"]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED emergency_stop_operator_status
                                     /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![ecu_sub_c] = "none"]
                                     /\ UNCHANGED << comfortable_stop_operator_request, 
                                                     comfortable_stop_operator_status >>
                                ELSE /\ IF "comfortable_stop" = "comfortable_stop"
                                           THEN /\ IF comfortable_stop_operator_request[ecu_sub_c] = "operate"
                                                      THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_sub_c] = "operating"]
                                                      ELSE /\ IF comfortable_stop_operator_request[ecu_sub_c] = "cancel"
                                                                 THEN /\ comfortable_stop_operator_status' = [comfortable_stop_operator_status EXCEPT ![ecu_sub_c] = "available"]
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED comfortable_stop_operator_status
                                                /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![ecu_sub_c] = "none"]
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << comfortable_stop_operator_request, 
                                                                comfortable_stop_operator_status >>
                                     /\ UNCHANGED << emergency_stop_operator_request, 
                                                     emergency_stop_operator_status >>
                          /\ pc' = [pc EXCEPT !["sub_comfortable_stop_service"] = "ComfortableStopService"]
                          /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                          e_faults, faults, 
                                          faults_and_no_faults, fault_queue, 
                                          no_fault, self_faults, 
                                          external_faults, EmergencyHandlers, 
                                          emergency_handler_status, 
                                          SelfMonitorings, ExternalMonitorings, 
                                          self_monitoring_results, 
                                          external_monitoring_results, 
                                          EmergencyStopServices, 
                                          EmergencyStopOperators, 
                                          ComfortableStopServices, 
                                          ComfortableStopOperators, no_error, 
                                          main_self_error_status, 
                                          sub_self_error_status, 
                                          supervisor_self_error_status, 
                                          main_external_error_status, 
                                          sub_external_error_status, 
                                          supervisor_external_error_status, 
                                          voter_state, mrm_operation, 
                                          vehicle_status, initial_selected_ecu, 
                                          extra_ecu, switch, 
                                          is_stop_operator_succeeded, 
                                          self_recoverable_flag, 
                                          no_operation_during_emergency, fault, 
                                          ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                          ecu_sup, is_emergency_, 
                                          current_mrm_behavior_, mrm_state_, 
                                          mrm_behavior_, ecu_ma, is_emergency, 
                                          current_mrm_behavior, mrm_state, 
                                          mrm_behavior, ecu_sub_, ecu_mai, 
                                          ecu_sub_e, ecu_supe, ecu_main, 
                                          ecu_sub_c, ecu_main_, ecu_sub_em, 
                                          ecu_super, ecu_main_c, ecu, 
                                          self_monitoring_count, 
                                          main_self_monitoring_int, 
                                          sub_self_monitoring_int, 
                                          supervisor_self_monitoring_int, 
                                          external_monitoring_count, 
                                          main_external_monitoring_int, 
                                          sub_external_monitoring_int, 
                                          supervisor_external_monitoring_int, 
                                          current_mrm_ecu >>

sub_comfortable_stop_service == ComfortableStopService

OperateEmergencyStop_ == /\ pc["main_emergency_stop_operator"] = "OperateEmergencyStop_"
                         /\ IF switch.state = ecu_main_
                               THEN /\ IF vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"
                                          THEN /\ IF emergency_stop_operator_status[ecu_main_] = "operating"
                                                     THEN /\ vehicle_status' = "emergency_operating"
                                                     ELSE /\ vehicle_status' = "running"
                                          ELSE /\ TRUE
                                               /\ UNCHANGED vehicle_status
                               ELSE /\ TRUE
                                    /\ UNCHANGED vehicle_status
                         /\ pc' = [pc EXCEPT !["main_emergency_stop_operator"] = "OperateEmergencyStop_"]
                         /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                         e_faults, faults, 
                                         faults_and_no_faults, fault_queue, 
                                         no_fault, self_faults, 
                                         external_faults, EmergencyHandlers, 
                                         emergency_handler_status, 
                                         SelfMonitorings, ExternalMonitorings, 
                                         self_monitoring_results, 
                                         external_monitoring_results, 
                                         emergency_stop_operator_request, 
                                         comfortable_stop_operator_request, 
                                         EmergencyStopServices, 
                                         EmergencyStopOperators, 
                                         ComfortableStopServices, 
                                         ComfortableStopOperators, 
                                         emergency_stop_operator_status, 
                                         comfortable_stop_operator_status, 
                                         no_error, main_self_error_status, 
                                         sub_self_error_status, 
                                         supervisor_self_error_status, 
                                         main_external_error_status, 
                                         sub_external_error_status, 
                                         supervisor_external_error_status, 
                                         voter_state, mrm_operation, 
                                         initial_selected_ecu, extra_ecu, 
                                         switch, is_stop_operator_succeeded, 
                                         self_recoverable_flag, 
                                         no_operation_during_emergency, fault, 
                                         ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                         ecu_sup, is_emergency_, 
                                         current_mrm_behavior_, mrm_state_, 
                                         mrm_behavior_, ecu_ma, is_emergency, 
                                         current_mrm_behavior, mrm_state, 
                                         mrm_behavior, ecu_sub_, ecu_mai, 
                                         ecu_sub_e, ecu_supe, ecu_main, 
                                         ecu_sub_c, ecu_main_, ecu_sub_em, 
                                         ecu_super, ecu_main_c, ecu, 
                                         self_monitoring_count, 
                                         main_self_monitoring_int, 
                                         sub_self_monitoring_int, 
                                         supervisor_self_monitoring_int, 
                                         external_monitoring_count, 
                                         main_external_monitoring_int, 
                                         sub_external_monitoring_int, 
                                         supervisor_external_monitoring_int, 
                                         current_mrm_ecu >>

main_emergency_stop_operator == OperateEmergencyStop_

OperateEmergencyStop_s == /\ pc["sub_emergency_stop_operator"] = "OperateEmergencyStop_s"
                          /\ IF switch.state = ecu_sub_em
                                THEN /\ IF vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"
                                           THEN /\ IF emergency_stop_operator_status[ecu_sub_em] = "operating"
                                                      THEN /\ vehicle_status' = "emergency_operating"
                                                      ELSE /\ vehicle_status' = "running"
                                           ELSE /\ TRUE
                                                /\ UNCHANGED vehicle_status
                                ELSE /\ TRUE
                                     /\ UNCHANGED vehicle_status
                          /\ pc' = [pc EXCEPT !["sub_emergency_stop_operator"] = "OperateEmergencyStop_s"]
                          /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                          e_faults, faults, 
                                          faults_and_no_faults, fault_queue, 
                                          no_fault, self_faults, 
                                          external_faults, EmergencyHandlers, 
                                          emergency_handler_status, 
                                          SelfMonitorings, ExternalMonitorings, 
                                          self_monitoring_results, 
                                          external_monitoring_results, 
                                          emergency_stop_operator_request, 
                                          comfortable_stop_operator_request, 
                                          EmergencyStopServices, 
                                          EmergencyStopOperators, 
                                          ComfortableStopServices, 
                                          ComfortableStopOperators, 
                                          emergency_stop_operator_status, 
                                          comfortable_stop_operator_status, 
                                          no_error, main_self_error_status, 
                                          sub_self_error_status, 
                                          supervisor_self_error_status, 
                                          main_external_error_status, 
                                          sub_external_error_status, 
                                          supervisor_external_error_status, 
                                          voter_state, mrm_operation, 
                                          initial_selected_ecu, extra_ecu, 
                                          switch, is_stop_operator_succeeded, 
                                          self_recoverable_flag, 
                                          no_operation_during_emergency, fault, 
                                          ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                          ecu_sup, is_emergency_, 
                                          current_mrm_behavior_, mrm_state_, 
                                          mrm_behavior_, ecu_ma, is_emergency, 
                                          current_mrm_behavior, mrm_state, 
                                          mrm_behavior, ecu_sub_, ecu_mai, 
                                          ecu_sub_e, ecu_supe, ecu_main, 
                                          ecu_sub_c, ecu_main_, ecu_sub_em, 
                                          ecu_super, ecu_main_c, ecu, 
                                          self_monitoring_count, 
                                          main_self_monitoring_int, 
                                          sub_self_monitoring_int, 
                                          supervisor_self_monitoring_int, 
                                          external_monitoring_count, 
                                          main_external_monitoring_int, 
                                          sub_external_monitoring_int, 
                                          supervisor_external_monitoring_int, 
                                          current_mrm_ecu >>

sub_emergency_stop_operator == OperateEmergencyStop_s

OperateEmergencyStop == /\ pc["supervisor_emergency_stop_operator"] = "OperateEmergencyStop"
                        /\ IF switch.state = ecu_super
                              THEN /\ IF vehicle_status /= "emergency_stopped" /\ vehicle_status /= "comfortable_stopped"
                                         THEN /\ IF emergency_stop_operator_status[ecu_super] = "operating"
                                                    THEN /\ vehicle_status' = "emergency_operating"
                                                    ELSE /\ vehicle_status' = "running"
                                         ELSE /\ TRUE
                                              /\ UNCHANGED vehicle_status
                              ELSE /\ TRUE
                                   /\ UNCHANGED vehicle_status
                        /\ pc' = [pc EXCEPT !["supervisor_emergency_stop_operator"] = "OperateEmergencyStop"]
                        /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                        e_faults, faults, faults_and_no_faults, 
                                        fault_queue, no_fault, self_faults, 
                                        external_faults, EmergencyHandlers, 
                                        emergency_handler_status, 
                                        SelfMonitorings, ExternalMonitorings, 
                                        self_monitoring_results, 
                                        external_monitoring_results, 
                                        emergency_stop_operator_request, 
                                        comfortable_stop_operator_request, 
                                        EmergencyStopServices, 
                                        EmergencyStopOperators, 
                                        ComfortableStopServices, 
                                        ComfortableStopOperators, 
                                        emergency_stop_operator_status, 
                                        comfortable_stop_operator_status, 
                                        no_error, main_self_error_status, 
                                        sub_self_error_status, 
                                        supervisor_self_error_status, 
                                        main_external_error_status, 
                                        sub_external_error_status, 
                                        supervisor_external_error_status, 
                                        voter_state, mrm_operation, 
                                        initial_selected_ecu, extra_ecu, 
                                        switch, is_stop_operator_succeeded, 
                                        self_recoverable_flag, 
                                        no_operation_during_emergency, fault, 
                                        ecu_, ecu_s, ecu_su, ecu_m, ecu_sub, 
                                        ecu_sup, is_emergency_, 
                                        current_mrm_behavior_, mrm_state_, 
                                        mrm_behavior_, ecu_ma, is_emergency, 
                                        current_mrm_behavior, mrm_state, 
                                        mrm_behavior, ecu_sub_, ecu_mai, 
                                        ecu_sub_e, ecu_supe, ecu_main, 
                                        ecu_sub_c, ecu_main_, ecu_sub_em, 
                                        ecu_super, ecu_main_c, ecu, 
                                        self_monitoring_count, 
                                        main_self_monitoring_int, 
                                        sub_self_monitoring_int, 
                                        supervisor_self_monitoring_int, 
                                        external_monitoring_count, 
                                        main_external_monitoring_int, 
                                        sub_external_monitoring_int, 
                                        supervisor_external_monitoring_int, 
                                        current_mrm_ecu >>

supervisor_emergency_stop_operator == OperateEmergencyStop

OperatecomfortableStop_ == /\ pc["main_comfortable_stop_operator"] = "OperatecomfortableStop_"
                           /\ IF switch.state = ecu_main_c
                                 THEN /\ IF vehicle_status /= "comfortable_stopped"
                                            THEN /\ IF comfortable_stop_operator_status[ecu_main_c] = "operating"
                                                       THEN /\ IF emergency_stop_operator_status[ecu_main_c] = "operating"
                                                                  THEN /\ no_operation_during_emergency' = FALSE
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED no_operation_during_emergency
                                                            /\ vehicle_status' = "comfortable_operating"
                                                       ELSE /\ IF vehicle_status /= "emergency_stopped"
                                                                  THEN /\ vehicle_status' = "running"
                                                                  ELSE /\ TRUE
                                                                       /\ UNCHANGED vehicle_status
                                                            /\ UNCHANGED no_operation_during_emergency
                                            ELSE /\ TRUE
                                                 /\ UNCHANGED << vehicle_status, 
                                                                 no_operation_during_emergency >>
                                 ELSE /\ TRUE
                                      /\ UNCHANGED << vehicle_status, 
                                                      no_operation_during_emergency >>
                           /\ pc' = [pc EXCEPT !["main_comfortable_stop_operator"] = "OperatecomfortableStop_"]
                           /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                           e_faults, faults, 
                                           faults_and_no_faults, fault_queue, 
                                           no_fault, self_faults, 
                                           external_faults, EmergencyHandlers, 
                                           emergency_handler_status, 
                                           SelfMonitorings, 
                                           ExternalMonitorings, 
                                           self_monitoring_results, 
                                           external_monitoring_results, 
                                           emergency_stop_operator_request, 
                                           comfortable_stop_operator_request, 
                                           EmergencyStopServices, 
                                           EmergencyStopOperators, 
                                           ComfortableStopServices, 
                                           ComfortableStopOperators, 
                                           emergency_stop_operator_status, 
                                           comfortable_stop_operator_status, 
                                           no_error, main_self_error_status, 
                                           sub_self_error_status, 
                                           supervisor_self_error_status, 
                                           main_external_error_status, 
                                           sub_external_error_status, 
                                           supervisor_external_error_status, 
                                           voter_state, mrm_operation, 
                                           initial_selected_ecu, extra_ecu, 
                                           switch, is_stop_operator_succeeded, 
                                           self_recoverable_flag, fault, ecu_, 
                                           ecu_s, ecu_su, ecu_m, ecu_sub, 
                                           ecu_sup, is_emergency_, 
                                           current_mrm_behavior_, mrm_state_, 
                                           mrm_behavior_, ecu_ma, is_emergency, 
                                           current_mrm_behavior, mrm_state, 
                                           mrm_behavior, ecu_sub_, ecu_mai, 
                                           ecu_sub_e, ecu_supe, ecu_main, 
                                           ecu_sub_c, ecu_main_, ecu_sub_em, 
                                           ecu_super, ecu_main_c, ecu, 
                                           self_monitoring_count, 
                                           main_self_monitoring_int, 
                                           sub_self_monitoring_int, 
                                           supervisor_self_monitoring_int, 
                                           external_monitoring_count, 
                                           main_external_monitoring_int, 
                                           sub_external_monitoring_int, 
                                           supervisor_external_monitoring_int, 
                                           current_mrm_ecu >>

main_comfortable_stop_operator == OperatecomfortableStop_

OperatecomfortableStop == /\ pc["sub_comfortable_stop_operator"] = "OperatecomfortableStop"
                          /\ IF switch.state = ecu
                                THEN /\ IF vehicle_status /= "comfortable_stopped"
                                           THEN /\ IF comfortable_stop_operator_status[ecu] = "operating"
                                                      THEN /\ IF emergency_stop_operator_status[ecu] = "operating"
                                                                 THEN /\ no_operation_during_emergency' = FALSE
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED no_operation_during_emergency
                                                           /\ vehicle_status' = "comfortable_operating"
                                                      ELSE /\ IF vehicle_status /= "emergency_stopped"
                                                                 THEN /\ vehicle_status' = "running"
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED vehicle_status
                                                           /\ UNCHANGED no_operation_during_emergency
                                           ELSE /\ TRUE
                                                /\ UNCHANGED << vehicle_status, 
                                                                no_operation_during_emergency >>
                                ELSE /\ TRUE
                                     /\ UNCHANGED << vehicle_status, 
                                                     no_operation_during_emergency >>
                          /\ pc' = [pc EXCEPT !["sub_comfortable_stop_operator"] = "OperatecomfortableStop"]
                          /\ UNCHANGED << fault_ecu, s_faults, no_faults, 
                                          e_faults, faults, 
                                          faults_and_no_faults, fault_queue, 
                                          no_fault, self_faults, 
                                          external_faults, EmergencyHandlers, 
                                          emergency_handler_status, 
                                          SelfMonitorings, ExternalMonitorings, 
                                          self_monitoring_results, 
                                          external_monitoring_results, 
                                          emergency_stop_operator_request, 
                                          comfortable_stop_operator_request, 
                                          EmergencyStopServices, 
                                          EmergencyStopOperators, 
                                          ComfortableStopServices, 
                                          ComfortableStopOperators, 
                                          emergency_stop_operator_status, 
                                          comfortable_stop_operator_status, 
                                          no_error, main_self_error_status, 
                                          sub_self_error_status, 
                                          supervisor_self_error_status, 
                                          main_external_error_status, 
                                          sub_external_error_status, 
                                          supervisor_external_error_status, 
                                          voter_state, mrm_operation, 
                                          initial_selected_ecu, extra_ecu, 
                                          switch, is_stop_operator_succeeded, 
                                          self_recoverable_flag, fault, ecu_, 
                                          ecu_s, ecu_su, ecu_m, ecu_sub, 
                                          ecu_sup, is_emergency_, 
                                          current_mrm_behavior_, mrm_state_, 
                                          mrm_behavior_, ecu_ma, is_emergency, 
                                          current_mrm_behavior, mrm_state, 
                                          mrm_behavior, ecu_sub_, ecu_mai, 
                                          ecu_sub_e, ecu_supe, ecu_main, 
                                          ecu_sub_c, ecu_main_, ecu_sub_em, 
                                          ecu_super, ecu_main_c, ecu, 
                                          self_monitoring_count, 
                                          main_self_monitoring_int, 
                                          sub_self_monitoring_int, 
                                          supervisor_self_monitoring_int, 
                                          external_monitoring_count, 
                                          main_external_monitoring_int, 
                                          sub_external_monitoring_int, 
                                          supervisor_external_monitoring_int, 
                                          current_mrm_ecu >>

sub_comfortable_stop_operator == OperatecomfortableStop

Voter == /\ pc["voter"] = "Voter"
         /\ IF voter_state.state /= "succeeded"
               THEN /\ IF (self_monitoring_results["main"]) = no_fault
                          THEN /\ main_self_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "main"
                                     THEN /\ IF (self_monitoring_results["main"]).self_recoverable
                                                THEN /\ main_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ main_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ main_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ main_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF (self_monitoring_results["sub"]) = no_fault
                          THEN /\ sub_self_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "sub"
                                     THEN /\ IF (self_monitoring_results["sub"]).self_recoverable
                                                THEN /\ sub_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ sub_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ sub_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ sub_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF (self_monitoring_results["supervisor"]) = no_fault
                          THEN /\ supervisor_self_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "supervisor"
                                     THEN /\ IF (self_monitoring_results["supervisor"]).self_recoverable
                                                THEN /\ supervisor_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ supervisor_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ supervisor_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ supervisor_self_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF (external_monitoring_results["main"]) = no_fault
                          THEN /\ main_external_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "main"
                                     THEN /\ main_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ main_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ main_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF (external_monitoring_results["sub"]) = no_fault
                          THEN /\ sub_external_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "sub"
                                     THEN /\ sub_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ sub_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ sub_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF (external_monitoring_results["supervisor"]) = no_fault
                          THEN /\ supervisor_external_error_status' = [is_emergency |-> FALSE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                          ELSE /\ IF switch.state = "supervisor"
                                     THEN /\ supervisor_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE , switch_needed |-> TRUE]
                                     ELSE /\ IF switch.state /= initial_selected_ecu
                                                THEN /\ supervisor_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> FALSE, switch_needed |-> FALSE]
                                                ELSE /\ supervisor_external_error_status' = [is_emergency |-> TRUE, stop_operation_needed |-> TRUE, switch_needed |-> FALSE]
                    /\ IF main_self_error_status' = no_error
                          THEN /\ main_self_monitoring_int' = 0
                          ELSE /\ main_self_monitoring_int' = 1
                    /\ IF sub_self_error_status' = no_error
                          THEN /\ sub_self_monitoring_int' = 0
                          ELSE /\ sub_self_monitoring_int' = 1
                    /\ IF supervisor_self_error_status' = no_error
                          THEN /\ supervisor_self_monitoring_int' = 0
                          ELSE /\ supervisor_self_monitoring_int' = 1
                    /\ IF main_external_error_status' = no_error
                          THEN /\ main_external_monitoring_int' = 0
                          ELSE /\ main_external_monitoring_int' = 1
                    /\ IF sub_external_error_status' = no_error
                          THEN /\ sub_external_monitoring_int' = 0
                          ELSE /\ sub_external_monitoring_int' = 1
                    /\ IF supervisor_external_error_status' = no_error
                          THEN /\ supervisor_external_monitoring_int' = 0
                          ELSE /\ supervisor_external_monitoring_int' = 1
                    /\ self_monitoring_count' = main_self_monitoring_int' + sub_self_monitoring_int' + supervisor_self_monitoring_int'
                    /\ external_monitoring_count' = main_external_monitoring_int' + sub_external_monitoring_int' + supervisor_external_monitoring_int'
                    /\ IF external_monitoring_count' = 0
                          THEN /\ IF self_monitoring_count' = 0
                                     THEN /\ mrm_operation' = [fault_ecu |-> "none", mrm_ecu |->"none", comfortable_stop_after_switch |-> FALSE]
                                     ELSE /\ IF self_monitoring_count' = 1
                                                THEN /\ IF main_self_monitoring_int' = 1
                                                           THEN /\ IF main_self_error_status'.is_emergency
                                                                      THEN /\ IF main_self_error_status'.stop_operation_needed
                                                                                 THEN /\ IF main_self_error_status'.switch_needed
                                                                                            THEN /\ mrm_operation' = [fault_ecu |-> "main", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                            ELSE /\ mrm_operation' = [fault_ecu |-> "main", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ mrm_operation' = [fault_ecu |-> "main",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED mrm_operation
                                                           ELSE /\ IF sub_self_monitoring_int' = 1
                                                                      THEN /\ IF sub_self_error_status'.is_emergency
                                                                                 THEN /\ IF sub_self_error_status'.stop_operation_needed
                                                                                            THEN /\ IF sub_self_error_status'.switch_needed
                                                                                                       THEN /\ mrm_operation' = [fault_ecu |-> "sub", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                                       ELSE /\ mrm_operation' = [fault_ecu |-> "sub", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                                            ELSE /\ mrm_operation' = [fault_ecu |-> "sub",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED mrm_operation
                                                                      ELSE /\ IF supervisor_self_error_status'.is_emergency
                                                                                 THEN /\ IF supervisor_self_error_status'.stop_operation_needed
                                                                                            THEN /\ IF supervisor_self_error_status'.switch_needed
                                                                                                       THEN /\ mrm_operation' = [fault_ecu |-> "supervisor", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                                       ELSE /\ mrm_operation' = [fault_ecu |-> "supervisor", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                                            ELSE /\ mrm_operation' = [fault_ecu |-> "supervisor",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED mrm_operation
                                                ELSE /\ mrm_operation' = [fault_ecu |-> "unknown", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                          ELSE /\ IF external_monitoring_count' = 1
                                     THEN /\ IF main_external_monitoring_int' = 1
                                                THEN /\ IF main_external_error_status'.is_emergency
                                                           THEN /\ IF main_external_error_status'.stop_operation_needed
                                                                      THEN /\ IF main_external_error_status'.switch_needed
                                                                                 THEN /\ mrm_operation' = [fault_ecu |-> "main", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                 ELSE /\ mrm_operation' = [fault_ecu |-> "main", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ mrm_operation' = [fault_ecu |-> "main",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED mrm_operation
                                                ELSE /\ IF sub_external_monitoring_int' = 1
                                                           THEN /\ IF sub_external_error_status'.is_emergency
                                                                      THEN /\ IF sub_external_error_status'.stop_operation_needed
                                                                                 THEN /\ IF sub_external_error_status'.switch_needed
                                                                                            THEN /\ mrm_operation' = [fault_ecu |-> "sub", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                            ELSE /\ mrm_operation' = [fault_ecu |-> "sub", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ mrm_operation' = [fault_ecu |-> "sub",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED mrm_operation
                                                           ELSE /\ IF supervisor_external_error_status'.is_emergency
                                                                      THEN /\ IF supervisor_external_error_status'.stop_operation_needed
                                                                                 THEN /\ IF supervisor_external_error_status'.switch_needed
                                                                                            THEN /\ mrm_operation' = [fault_ecu |-> "supervisor", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> TRUE]
                                                                                            ELSE /\ mrm_operation' = [fault_ecu |-> "supervisor", mrm_ecu |-> switch.state, comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ mrm_operation' = [fault_ecu |-> "supervisor",  mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED mrm_operation
                                     ELSE /\ mrm_operation' = [fault_ecu |-> "unknown", mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                    /\ IF voter_state.state = "normal"
                          THEN /\ IF mrm_operation'.fault_ecu /= "none"
                                     THEN /\ IF mrm_operation'.mrm_ecu = "supervisor"
                                                THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> mrm_operation'.comfortable_stop_after_switch]
                                                ELSE /\ IF mrm_operation'.mrm_ecu = "unknown"
                                                           THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                                                           ELSE /\ IF mrm_operation'.mrm_ecu /= "none"
                                                                      THEN /\ IF mrm_operation'.mrm_ecu /= initial_selected_ecu
                                                                                 THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ voter_state' = [state |-> "comfortable_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> mrm_operation'.mrm_ecu, comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED voter_state
                                     ELSE /\ TRUE
                                          /\ UNCHANGED voter_state
                          ELSE /\ IF voter_state.state = "supervisor_stop"
                                     THEN /\ IF vehicle_status = "emergency_stopped" \/ vehicle_status = "comfortable_stopped"
                                                THEN /\ IF voter_state.comfortable_stop_after_switch
                                                           THEN /\ IF voter_state.fault_ecu = "main"
                                                                      THEN /\ voter_state' = [state |-> "comfortable_stop", fault_ecu |-> "main", mrm_ecu |-> "sub", comfortable_stop_after_switch |-> TRUE]
                                                                      ELSE /\ IF voter_state.fault_ecu = "sub"
                                                                                 THEN /\ voter_state' = [state |-> "comfortable_stop", fault_ecu |-> "sub", mrm_ecu |-> "main", comfortable_stop_after_switch |-> TRUE]
                                                                                 ELSE /\ voter_state' = [state |-> "failed", fault_ecu |-> "unknown", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                           ELSE /\ voter_state' = [state |-> "succeeded", fault_ecu |-> voter_state.fault_ecu, mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                ELSE /\ IF mrm_operation'.fault_ecu = "none"
                                                           THEN /\ voter_state' = [state |-> "normal", fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                           ELSE /\ IF mrm_operation'.mrm_ecu /= "supervisor" /\ mrm_operation'.mrm_ecu /= "none"
                                                                      THEN /\ IF mrm_operation'.mrm_ecu /= initial_selected_ecu
                                                                                 THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                                                                                 ELSE /\ voter_state' = [state |-> "comfortable_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> mrm_operation'.mrm_ecu, comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ IF mrm_operation'.mrm_ecu = "supervisor"
                                                                                 THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> mrm_operation'.comfortable_stop_after_switch]
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED voter_state
                                     ELSE /\ IF voter_state.state = "comfortable_stop"
                                                THEN /\ IF vehicle_status = "comfortable_stopped"
                                                           THEN /\ voter_state' = [state |-> "succeeded", fault_ecu |-> voter_state.fault_ecu, mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                           ELSE /\ IF mrm_operation'.fault_ecu = "none"
                                                                      THEN /\ voter_state' = [state |-> "normal", fault_ecu |-> "none", mrm_ecu |-> "none", comfortable_stop_after_switch |-> FALSE]
                                                                      ELSE /\ IF mrm_operation'.mrm_ecu = "supervisor"
                                                                                 THEN /\ IF ~voter_state.comfortable_stop_after_switch
                                                                                            THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> mrm_operation'.comfortable_stop_after_switch]
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED voter_state
                                                                                 ELSE /\ IF mrm_operation'.mrm_ecu /= "none"
                                                                                            THEN /\ IF mrm_operation'.mrm_ecu /= voter_state.mrm_ecu
                                                                                                       THEN /\ IF mrm_operation'.mrm_ecu /= initial_selected_ecu
                                                                                                                  THEN /\ voter_state' = [state |-> "supervisor_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> "supervisor", comfortable_stop_after_switch |-> FALSE]
                                                                                                                  ELSE /\ voter_state' = [state |-> "comfortable_stop", fault_ecu |-> mrm_operation'.fault_ecu, mrm_ecu |-> mrm_operation'.mrm_ecu, comfortable_stop_after_switch |-> FALSE]
                                                                                                       ELSE /\ TRUE
                                                                                                            /\ UNCHANGED voter_state
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED voter_state
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED voter_state
                    /\ IF voter_state'.state = "normal"
                          THEN /\ IF current_mrm_ecu /= "none"
                                     THEN /\ IF current_mrm_ecu = "supervisor"
                                                THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT ![current_mrm_ecu] = "cancel"]
                                                     /\ UNCHANGED comfortable_stop_operator_request
                                                ELSE /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![current_mrm_ecu] = "cancel"]
                                                     /\ UNCHANGED emergency_stop_operator_request
                                          /\ switch' = [switch EXCEPT !.state = initial_selected_ecu]
                                          /\ current_mrm_ecu' = "none"
                                     ELSE /\ TRUE
                                          /\ UNCHANGED << emergency_stop_operator_request, 
                                                          comfortable_stop_operator_request, 
                                                          switch, 
                                                          current_mrm_ecu >>
                          ELSE /\ IF voter_state'.state = "supervisor_stop"
                                     THEN /\ IF current_mrm_ecu /= "supervisor"
                                                THEN /\ IF current_mrm_ecu /= "none"
                                                           THEN /\ IF comfortable_stop_operator_status[current_mrm_ecu] = "operating"
                                                                      THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![current_mrm_ecu] = "cancel"]
                                                                      ELSE /\ TRUE
                                                                           /\ UNCHANGED comfortable_stop_operator_request
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED comfortable_stop_operator_request
                                                     /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT !["supervisor"] = "operate"]
                                                     /\ IF emergency_stop_operator_status["supervisor"] = "operating"
                                                           THEN /\ switch' = [switch EXCEPT !.state = "supervisor"]
                                                                /\ current_mrm_ecu' = "supervisor"
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << switch, 
                                                                                current_mrm_ecu >>
                                                ELSE /\ TRUE
                                                     /\ UNCHANGED << emergency_stop_operator_request, 
                                                                     comfortable_stop_operator_request, 
                                                                     switch, 
                                                                     current_mrm_ecu >>
                                     ELSE /\ IF voter_state'.state = "comfortable_stop"
                                                THEN /\ IF current_mrm_ecu /= voter_state'.mrm_ecu
                                                           THEN /\ IF voter_state'.mrm_ecu = initial_selected_ecu
                                                                      THEN /\ IF emergency_stop_operator_status["supervisor"] = "operating"
                                                                                 THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT !["supervisor"] = "cancel"]
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED emergency_stop_operator_request
                                                                           /\ IF comfortable_stop_operator_status[extra_ecu] = "operating"
                                                                                 THEN /\ IF emergency_stop_operator_status[initial_selected_ecu] /= "operating"
                                                                                            THEN /\ comfortable_stop_operator_request' = [main |-> "operate", sub |-> "cancel"]
                                                                                                 /\ IF comfortable_stop_operator_status[initial_selected_ecu] = "operating"
                                                                                                       THEN /\ switch' = [switch EXCEPT !.state = initial_selected_ecu]
                                                                                                            /\ current_mrm_ecu' = initial_selected_ecu
                                                                                                       ELSE /\ TRUE
                                                                                                            /\ UNCHANGED << switch, 
                                                                                                                            current_mrm_ecu >>
                                                                                            ELSE /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![extra_ecu] = "cancel"]
                                                                                                 /\ switch' = [switch EXCEPT !.state = initial_selected_ecu]
                                                                                                 /\ current_mrm_ecu' = initial_selected_ecu
                                                                                 ELSE /\ IF emergency_stop_operator_status[initial_selected_ecu] /= "operating"
                                                                                            THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![initial_selected_ecu] = "operate"]
                                                                                                 /\ IF comfortable_stop_operator_status[initial_selected_ecu] = "operating"
                                                                                                       THEN /\ switch' = [switch EXCEPT !.state = initial_selected_ecu]
                                                                                                            /\ current_mrm_ecu' = initial_selected_ecu
                                                                                                       ELSE /\ TRUE
                                                                                                            /\ UNCHANGED << switch, 
                                                                                                                            current_mrm_ecu >>
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED << comfortable_stop_operator_request, 
                                                                                                                 switch, 
                                                                                                                 current_mrm_ecu >>
                                                                      ELSE /\ IF voter_state'.mrm_ecu = extra_ecu
                                                                                 THEN /\ IF emergency_stop_operator_status["supervisor"] = "operating"
                                                                                            THEN /\ emergency_stop_operator_request' = [emergency_stop_operator_request EXCEPT !["supervisor"] = "cancel"]
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED emergency_stop_operator_request
                                                                                      /\ IF emergency_stop_operator_status[extra_ecu] /= "operating"
                                                                                            THEN /\ comfortable_stop_operator_request' = [comfortable_stop_operator_request EXCEPT ![extra_ecu] = "operate"]
                                                                                                 /\ IF comfortable_stop_operator_status[extra_ecu] = "operating"
                                                                                                       THEN /\ switch' = [switch EXCEPT !.state = extra_ecu]
                                                                                                            /\ current_mrm_ecu' = extra_ecu
                                                                                                       ELSE /\ TRUE
                                                                                                            /\ UNCHANGED << switch, 
                                                                                                                            current_mrm_ecu >>
                                                                                            ELSE /\ TRUE
                                                                                                 /\ UNCHANGED << comfortable_stop_operator_request, 
                                                                                                                 switch, 
                                                                                                                 current_mrm_ecu >>
                                                                                 ELSE /\ TRUE
                                                                                      /\ UNCHANGED << emergency_stop_operator_request, 
                                                                                                      comfortable_stop_operator_request, 
                                                                                                      switch, 
                                                                                                      current_mrm_ecu >>
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << emergency_stop_operator_request, 
                                                                                comfortable_stop_operator_request, 
                                                                                switch, 
                                                                                current_mrm_ecu >>
                                                ELSE /\ IF voter_state'.state = "succeeded"
                                                           THEN /\ emergency_stop_operator_request' = [main |-> "cancel", sub |-> "cancel", supervisor |-> "cancel"]
                                                                /\ comfortable_stop_operator_request' = [main |-> "cancel", sub |-> "cancel"]
                                                                /\ current_mrm_ecu' = "none"
                                                           ELSE /\ TRUE
                                                                /\ UNCHANGED << emergency_stop_operator_request, 
                                                                                comfortable_stop_operator_request, 
                                                                                current_mrm_ecu >>
                                                     /\ UNCHANGED switch
                    /\ pc' = [pc EXCEPT !["voter"] = "Voter"]
               ELSE /\ pc' = [pc EXCEPT !["voter"] = "Done"]
                    /\ UNCHANGED << emergency_stop_operator_request, 
                                    comfortable_stop_operator_request, 
                                    main_self_error_status, 
                                    sub_self_error_status, 
                                    supervisor_self_error_status, 
                                    main_external_error_status, 
                                    sub_external_error_status, 
                                    supervisor_external_error_status, 
                                    voter_state, mrm_operation, switch, 
                                    self_monitoring_count, 
                                    main_self_monitoring_int, 
                                    sub_self_monitoring_int, 
                                    supervisor_self_monitoring_int, 
                                    external_monitoring_count, 
                                    main_external_monitoring_int, 
                                    sub_external_monitoring_int, 
                                    supervisor_external_monitoring_int, 
                                    current_mrm_ecu >>
         /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, faults, 
                         faults_and_no_faults, fault_queue, no_fault, 
                         self_faults, external_faults, EmergencyHandlers, 
                         emergency_handler_status, SelfMonitorings, 
                         ExternalMonitorings, self_monitoring_results, 
                         external_monitoring_results, EmergencyStopServices, 
                         EmergencyStopOperators, ComfortableStopServices, 
                         ComfortableStopOperators, 
                         emergency_stop_operator_status, 
                         comfortable_stop_operator_status, no_error, 
                         vehicle_status, initial_selected_ecu, extra_ecu, 
                         is_stop_operator_succeeded, self_recoverable_flag, 
                         no_operation_during_emergency, fault, ecu_, ecu_s, 
                         ecu_su, ecu_m, ecu_sub, ecu_sup, is_emergency_, 
                         current_mrm_behavior_, mrm_state_, mrm_behavior_, 
                         ecu_ma, is_emergency, current_mrm_behavior, mrm_state, 
                         mrm_behavior, ecu_sub_, ecu_mai, ecu_sub_e, ecu_supe, 
                         ecu_main, ecu_sub_c, ecu_main_, ecu_sub_em, ecu_super, 
                         ecu_main_c, ecu >>

voter == Voter

Vehicle == /\ pc["vehicle"] = "Vehicle"
           /\ IF vehicle_status = "emergency_operating"
                 THEN /\ vehicle_status' = "emergency_stopped"
                 ELSE /\ IF vehicle_status = "comfortable_operating"
                            THEN /\ vehicle_status' = "comfortable_stopped"
                            ELSE /\ TRUE
                                 /\ UNCHANGED vehicle_status
           /\ pc' = [pc EXCEPT !["vehicle"] = "Vehicle"]
           /\ UNCHANGED << fault_ecu, s_faults, no_faults, e_faults, faults, 
                           faults_and_no_faults, fault_queue, no_fault, 
                           self_faults, external_faults, EmergencyHandlers, 
                           emergency_handler_status, SelfMonitorings, 
                           ExternalMonitorings, self_monitoring_results, 
                           external_monitoring_results, 
                           emergency_stop_operator_request, 
                           comfortable_stop_operator_request, 
                           EmergencyStopServices, EmergencyStopOperators, 
                           ComfortableStopServices, ComfortableStopOperators, 
                           emergency_stop_operator_status, 
                           comfortable_stop_operator_status, no_error, 
                           main_self_error_status, sub_self_error_status, 
                           supervisor_self_error_status, 
                           main_external_error_status, 
                           sub_external_error_status, 
                           supervisor_external_error_status, voter_state, 
                           mrm_operation, initial_selected_ecu, extra_ecu, 
                           switch, is_stop_operator_succeeded, 
                           self_recoverable_flag, 
                           no_operation_during_emergency, fault, ecu_, ecu_s, 
                           ecu_su, ecu_m, ecu_sub, ecu_sup, is_emergency_, 
                           current_mrm_behavior_, mrm_state_, mrm_behavior_, 
                           ecu_ma, is_emergency, current_mrm_behavior, 
                           mrm_state, mrm_behavior, ecu_sub_, ecu_mai, 
                           ecu_sub_e, ecu_supe, ecu_main, ecu_sub_c, ecu_main_, 
                           ecu_sub_em, ecu_super, ecu_main_c, ecu, 
                           self_monitoring_count, main_self_monitoring_int, 
                           sub_self_monitoring_int, 
                           supervisor_self_monitoring_int, 
                           external_monitoring_count, 
                           main_external_monitoring_int, 
                           sub_external_monitoring_int, 
                           supervisor_external_monitoring_int, current_mrm_ecu >>

vehicle == Vehicle

Next == safety_mechanism \/ main_self_monitoring \/ sub_self_monitoring
           \/ supervisor_self_monitoring \/ main_external_monitoring
           \/ sub_external_monitoring \/ supervisor_external_monitoring
           \/ main_emergency_handler \/ sub_emergency_handler
           \/ main_emergency_stop_service \/ sub_emergency_stop_service
           \/ supervisor_emergency_stop_service \/ main_comfortable_stop_service
           \/ sub_comfortable_stop_service \/ main_emergency_stop_operator
           \/ sub_emergency_stop_operator \/ supervisor_emergency_stop_operator
           \/ main_comfortable_stop_operator \/ sub_comfortable_stop_operator
           \/ voter \/ vehicle

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ WF_vars(safety_mechanism)
        /\ WF_vars(main_self_monitoring)
        /\ WF_vars(sub_self_monitoring)
        /\ WF_vars(supervisor_self_monitoring)
        /\ WF_vars(main_external_monitoring)
        /\ WF_vars(sub_external_monitoring)
        /\ WF_vars(supervisor_external_monitoring)
        /\ WF_vars(main_emergency_handler)
        /\ WF_vars(sub_emergency_handler)
        /\ WF_vars(main_emergency_stop_service)
        /\ WF_vars(sub_emergency_stop_service)
        /\ WF_vars(supervisor_emergency_stop_service)
        /\ WF_vars(main_comfortable_stop_service)
        /\ WF_vars(sub_comfortable_stop_service)
        /\ WF_vars(main_emergency_stop_operator)
        /\ WF_vars(sub_emergency_stop_operator)
        /\ WF_vars(supervisor_emergency_stop_operator)
        /\ WF_vars(main_comfortable_stop_operator)
        /\ WF_vars(sub_comfortable_stop_operator)
        /\ WF_vars(voter)
        /\ SF_vars(vehicle)

\* END TRANSLATION
====
