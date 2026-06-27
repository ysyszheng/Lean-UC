import LeanCryptoProtocols.UC.Security

/-!
# Static UC audit reports

This module provides lightweight renderers for protocol and ideal-functionality
objects.  The renderers are intentionally proof-free: the structural
well-formedness proofs stay in the Lean objects, while the report exposes the
parts that are useful for human review.
-/

universe u

namespace LeanCryptoProtocols.UC.Audit

open LeanCryptoProtocols.UC

/-- Human-readable names for machine identities in audit reports. -/
structure AuditNames where
  machine_name : MachineId → String

/-- A fallback naming table that prints raw machine identities. -/
def default_audit_names : AuditNames where
  machine_name := fun mid => "machine#" ++ toString mid

def join_with (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ join_with sep xs

def render_machine_id (names : AuditNames) (mid : MachineId) : String :=
  names.machine_name mid ++ " (#" ++ toString mid ++ ")"

def render_port_label : PortLabel → String
  | .input => "input"
  | .subroutineOutput => "subroutineOutput"
  | .backdoor => "backdoor"

def render_comm_port (names : AuditNames) (p : CommPort) : String :=
  render_machine_id names p.owner ++ " --" ++ render_port_label p.label ++ "--> " ++
    render_machine_id names p.dest

noncomputable def render_port_list (names : AuditNames) (ports : Finset CommPort) : String :=
  match ports.toList.map (fun p => "    - " ++ render_comm_port names p) with
  | [] => "    - <none>"
  | lines => join_with "\n" lines

noncomputable def render_machine_role {Payload : Type u}
    (π : Protocol Payload) (mid : MachineId) : String := by
  classical
  exact if π.is_main_machine mid then "main" else "internal"

noncomputable def external_destinations_of {Payload : Type u}
    (π : Protocol Payload) (m : AnyMachine Payload) : List MachineId := by
  classical
  let internal_ids := (machine_ids π.machines).toFinset
  exact m.2.communication_set.toList.filterMap fun p =>
    if p.label = .subroutineOutput ∧ p.dest ∉ internal_ids then
      some p.dest
    else
      none

noncomputable def render_external_destinations {Payload : Type u}
    (names : AuditNames) (π : Protocol Payload) (m : AnyMachine Payload) : String :=
  match external_destinations_of π m with
  | [] => "    external identities: <none>"
  | ids =>
      "    external identities: " ++
        join_with ", " (ids.map (render_machine_id names))

noncomputable def render_protocol_machine {Payload : Type u}
    (names : AuditNames) (π : Protocol Payload) (m : AnyMachine Payload) : String :=
  let mid := AnyMachine.id m
  "- " ++ render_machine_id names mid ++ " [" ++ render_machine_role π mid ++ "]\n" ++
    render_external_destinations names π m ++ "\n" ++
    "    ports:\n" ++ render_port_list names m.2.communication_set

noncomputable def render_machine_id_finset
    (names : AuditNames) (ids : Finset MachineId) : String :=
  match ids.toList.map (render_machine_id names) with
  | [] => "<none>"
  | lines => join_with ", " lines

def render_adversarial_control_target (names : AuditNames) (mid : MachineId) : String :=
  "- " ++ render_machine_id names adv_id ++ " <--backdoor--> " ++
    render_machine_id names mid

/--
Controller 在运行时为 adversary 与每台 protocol machine 添加双向 backdoor 端口。
该报告直接从 protocol machine 列表推导控制面，不接受额外的控制目标列表。
-/
def render_adversarial_control_surface {Payload : Type u}
    (names : AuditNames) (π : Protocol Payload) : String :=
  match π.machines.map (fun m =>
      render_adversarial_control_target names (AnyMachine.id m)) with
  | [] => "Adversarial control surface:\n- <none>"
  | lines => "Adversarial control surface:\n" ++ join_with "\n" lines

noncomputable def render_protocol {Payload : Type u}
    (names : AuditNames) (π : Protocol Payload) : String :=
  "Protocol audit\n\n" ++
    "Main machines: " ++ render_machine_id_finset names π.main_machine_ids ++ "\n" ++
    "Internal machines: " ++ render_machine_id_finset names π.internal_machine_ids ++ "\n\n" ++
    "Machines and ports:\n" ++
    join_with "\n\n" (π.machines.map (render_protocol_machine names π)) ++
    "\n\n" ++ render_adversarial_control_surface names π

noncomputable def render_party_interface {Payload : Type u}
    (names : AuditNames) (f : IdealFunctionality Payload) (pid : MachineId) : String :=
  "- " ++ render_machine_id names pid ++
    " external identities: " ++
      render_machine_id_finset names (f.party_external_ids pid)

noncomputable def render_ideal_functionality {Payload : Type u}
    (names : AuditNames) (f : IdealFunctionality Payload) : String :=
  "Ideal functionality audit\n\n" ++
    "Functionality: " ++ render_machine_id names f.functionality_id ++ "\n" ++
    "Parties: " ++ join_with ", " (f.party_ids.map (render_machine_id names)) ++ "\n\n" ++
    "Party interfaces:\n" ++
    join_with "\n" (f.party_ids.map (render_party_interface names f)) ++ "\n\n" ++
    "Functionality ports:\n" ++ render_port_list names f.machine.communication_set

def render_security_goal (goal : String) : String :=
  "Security goal\n" ++ goal

/-- Computable port row used by executable audit reports. -/
structure PortAuditView where
  owner : MachineId
  dest : MachineId
  label : PortLabel
  deriving Repr, DecidableEq

def PortAuditView.of_comm_port (p : CommPort) : PortAuditView where
  owner := p.owner
  dest := p.dest
  label := p.label

/-- Computable machine row used by executable audit reports. -/
structure MachineAuditView where
  id : MachineId
  role : String
  external_ids : List MachineId
  ports : List PortAuditView
  deriving Repr, DecidableEq

/-- Computable protocol view used when a case study wants terminal output. -/
structure ProtocolAuditView where
  main_ids : List MachineId
  internal_ids : List MachineId
  machines : List MachineAuditView
  deriving Repr, DecidableEq

/-- Computable ideal-functionality view used when a case study wants terminal output. -/
structure IdealFunctionalityAuditView where
  functionality_id : MachineId
  party_ids : List MachineId
  party_external_ids : List (MachineId × List MachineId)
  functionality_ports : List PortAuditView
  deriving Repr, DecidableEq

def render_port_view (names : AuditNames) (p : PortAuditView) : String :=
  render_machine_id names p.owner ++ " --" ++ render_port_label p.label ++ "--> " ++
    render_machine_id names p.dest

def render_port_view_list (names : AuditNames) : List PortAuditView → String
  | [] => "    - <none>"
  | ports => join_with "\n" (ports.map fun p => "    - " ++ render_port_view names p)

def render_machine_id_list (names : AuditNames) : List MachineId → String
  | [] => "<none>"
  | ids => join_with ", " (ids.map (render_machine_id names))

def render_machine_view (names : AuditNames) (m : MachineAuditView) : String :=
  "- " ++ render_machine_id names m.id ++ " [" ++ m.role ++ "]\n" ++
    "    external identities: " ++ render_machine_id_list names m.external_ids ++ "\n" ++
    "    ports:\n" ++ render_port_view_list names m.ports

def render_protocol_view
    (names : AuditNames) (view : ProtocolAuditView) : String :=
  "Protocol audit\n\n" ++
    "Main machines: " ++ render_machine_id_list names view.main_ids ++ "\n" ++
    "Internal machines: " ++ render_machine_id_list names view.internal_ids ++ "\n\n" ++
    "Machines and ports:\n" ++
    join_with "\n\n" (view.machines.map (render_machine_view names)) ++
    "\n\nAdversarial control surface:\n" ++
    join_with "\n"
      (view.machines.map fun m => render_adversarial_control_target names m.id)

def render_party_interface_view
    (names : AuditNames) (row : MachineId × List MachineId) : String :=
  "- " ++ render_machine_id names row.1 ++
    " external identities: " ++ render_machine_id_list names row.2

def render_ideal_functionality_view
    (names : AuditNames) (view : IdealFunctionalityAuditView) : String :=
  "Ideal functionality audit\n\n" ++
    "Functionality: " ++ render_machine_id names view.functionality_id ++ "\n" ++
    "Parties: " ++ render_machine_id_list names view.party_ids ++ "\n\n" ++
    "Party interfaces:\n" ++
    join_with "\n" (view.party_external_ids.map (render_party_interface_view names)) ++
    "\n\nFunctionality ports:\n" ++
    render_port_view_list names view.functionality_ports

end LeanCryptoProtocols.UC.Audit
