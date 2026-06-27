import LeanCryptoProtocols.CaseStudy.SMCEasyUC.Certificate.Certificate
import LeanCryptoProtocols.UC.Audit.Static

/-!
# SMC EasyUC audit reports

This file contains case-study specific audit views.  The certificate objects and
their well-formedness proofs live under `Certificate/`; this module only renders
the static structure in a compact form.
-/

namespace LeanCryptoProtocols.CaseStudy.SMCEasyUC

open LeanCryptoProtocols.UC
open LeanCryptoProtocols.UC.Audit
open LeanCryptoProtocols.UC.Functionality

/-- Human-readable names used by the SMC EasyUC audit reports. -/
def audit_names : AuditNames where
  machine_name := fun
    | 0 => "environment"
    | 1 => "adversary"
    | 10 => "SMC.sender"
    | 11 => "SMC.receiver"
    | 12 => "KE.sender"
    | 13 => "KE.receiver"
    | 14 => "Forw.ke.forward"
    | 15 => "Forw.ke.return"
    | 16 => "Forw.smc"
    | 17 => "Ideal.SMC"
    | 18 => "external.sender"
    | 19 => "external.receiver"
    | mid => "machine#" ++ toString mid

/-- Compact port row constructor for the executable audit view. -/
def port_view (p : CommPort) : PortAuditView :=
  PortAuditView.of_comm_port p

def machine_view
    (id : MachineId) (role : String) (external_ids : List MachineId)
    (ports : List CommPort) : MachineAuditView where
  id := id
  role := role
  external_ids := external_ids
  ports := ports.map port_view

/-- Executable static protocol view for terminal audit output. -/
def real_protocol_audit_view : ProtocolAuditView where
  main_ids := [smc_sender_id, smc_receiver_id]
  internal_ids :=
    [ ke_sender_id
    , ke_receiver_id
    , forw_ke_forward_id
    , forw_ke_return_id
    , forw_smc_id
    ]
  machines :=
    [ machine_view smc_sender_id "main"
        [sender_external_id]
        [ smc_sender_to_ke_sender_port
        , smc_sender_to_forw_smc_port
        , smc_sender_to_external_port
        ]
    , machine_view smc_receiver_id "main"
        [receiver_external_id]
        [ smc_receiver_to_ke_receiver_port
        , smc_receiver_to_forw_smc_port
        , smc_receiver_to_external_port
        ]
    , machine_view ke_sender_id "internal"
        []
        [ ke_sender_to_smc_sender_port
        , ke_sender_to_forw_ke_forward_port
        , ke_sender_to_forw_ke_return_port
        ]
    , machine_view ke_receiver_id "internal"
        []
        [ ke_receiver_to_smc_receiver_port
        , ke_receiver_to_forw_ke_forward_port
        , ke_receiver_to_forw_ke_return_port
        ]
    , machine_view forw_ke_forward_id "internal"
        []
        [ forw_sender_port forw_ke_forward_ids
        , forw_receiver_port forw_ke_forward_ids
        , forw_adversary_port forw_ke_forward_ids
        ]
    , machine_view forw_ke_return_id "internal"
        []
        [ forw_sender_port forw_ke_return_ids
        , forw_receiver_port forw_ke_return_ids
        , forw_adversary_port forw_ke_return_ids
        ]
    , machine_view forw_smc_id "internal"
        []
        [ forw_sender_port forw_smc_ids
        , forw_receiver_port forw_smc_ids
        , forw_adversary_port forw_smc_ids
        ]
    ]

/-- Executable static ideal-functionality view for terminal audit output. -/
def ideal_functionality_audit_view : IdealFunctionalityAuditView where
  functionality_id := ideal_smc_id
  party_ids := [smc_sender_id, smc_receiver_id]
  party_external_ids :=
    [ (smc_sender_id, [sender_external_id])
    , (smc_receiver_id, [receiver_external_id])
    ]
  functionality_ports :=
    [ port_view (smc_sender_port smc_ids)
    , port_view (smc_receiver_port smc_ids)
    , port_view (smc_adversary_port smc_ids)
    ]

/-- Static report for terminal audit output. -/
def static_report : String :=
  render_protocol_view audit_names real_protocol_audit_view ++
    "\n\n" ++
    render_ideal_functionality_view audit_names
      ideal_functionality_audit_view ++
    "\n\n" ++
    render_security_goal
      "For every PPT adversary, assuming DDH for the group generator, the real \
      SMC protocol should computationally UC-realize the SMC ideal functionality."

end LeanCryptoProtocols.CaseStudy.SMCEasyUC
