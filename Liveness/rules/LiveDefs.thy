theory LiveDefs
  imports "AllFixes.BasicInvariants"
begin

text \<open>Six rules that remove reachable deadlocks of @{const allTransitions'}. They are added next to the
  existing rules; no existing rule and not the invariant @{const SWMR_state_machine} changes. In a bounded
  exhaustive search (every program of up to three instructions per device) the extended model reaches exactly
  the states of the original one: the new rules only add transitions out of states in which it is stuck.

  \<^item> @{text HostIDDataLate'}, @{text HostSBDataLate'}, @{text HostIBDataLate'}, @{text HostMBDataLate'}:
    the host takes the data that answers its GO_WritePull although the sender, or the other device, has
    already issued a new request (ISAD or IMAD; for I^D also SIAC). The original rules require the sender to
    be Invalid (and, for I^D and I^B, restrict the other device), and the host accepts no request while it
    waits for the data, so the new request and the data block each other forever.
  \<^item> @{text HostSharedRdOwnSMAD'}: the host in S serves an RdOwn while the other device is upgrading too
    (SMAD, its own RdOwn still queued): it snoops that device like any sharer.
  \<^item> @{text HostSharedRdOwnIMAD'}: the host in S serves an RdOwn while the other device holds no copy and
    waits for its own RdOwn (IMAD): it grants ownership at once, like @{const HostSharedRdOwnSelf'}.
    Without these two, two concurrent RdOwns at a host in S wait for each other forever.\<close>

definition "HostIDDataLate' T i = (if HSTATE ID T \<and> nextDTHDataFrom i T
    \<and> (CSTATE Invalid T i \<or> CSTATE ISAD T i \<or> CSTATE IMAD T i)
    \<and> (CSTATE IIA T ((i + 1) mod 2) \<or> CSTATE Invalid T ((i + 1) mod 2) \<or> CSTATE SIA T ((i + 1) mod 2)
       \<or> CSTATE ISAD T ((i + 1) mod 2) \<or> CSTATE IMAD T ((i + 1) mod 2) \<or> CSTATE SIAC T ((i + 1) mod 2))
  then [clearBuffer (copyInDataHost i InvalidM T)] else [])"

definition "HostSBDataLate' T i = (if HSTATE SB T \<and> nextDTHDataFrom i T
    \<and> (CSTATE Invalid T i \<or> CSTATE ISAD T i \<or> CSTATE IMAD T i)
  then [clearBuffer (discardDataHost i SharedM T)] else [])"

definition "HostIBDataLate' T i = (if HSTATE IB T \<and> nextDTHDataFrom i T
    \<and> (CSTATE Invalid T i \<or> CSTATE ISAD T i \<or> CSTATE IMAD T i)
    \<and> (CSTATE Invalid T ((i + 1) mod 2) \<or> CSTATE ISAD T ((i + 1) mod 2) \<or> CSTATE IMAD T ((i + 1) mod 2))
  then [clearBuffer (discardDataHost i InvalidM T)] else [])"

definition "HostMBDataLate' T i = (if HSTATE MB T \<and> nextDTHDataFrom i T
    \<and> (CSTATE Invalid T i \<or> CSTATE ISAD T i \<or> CSTATE IMAD T i)
  then [clearBuffer (discardDataHost i ModifiedM T)] else [])"

definition "HostSharedRdOwnSMAD' T i = (if HSTATE SharedM T \<and> nextReqIs RdOwn T i
    \<and> CSTATE SMAD T ((i + 1) mod 2) \<and> nextReqIs RdOwn T ((i + 1) mod 2)
  then [clearBuffer (invalidateSharers (nextReqID T i) i T)] else [])"

definition "HostSharedRdOwnIMAD' T i = (if HSTATE SharedM T \<and> nextReqIs RdOwn T i
    \<and> CSTATE IMAD T ((i + 1) mod 2) \<and> nextReqIs RdOwn T ((i + 1) mod 2)
  then [clearBuffer (noInvalidateSharers (nextReqID T i) i T)] else [])"

lemma Lall_single_if: "(G \<Longrightarrow> P x) \<Longrightarrow> Lall (if G then [x] else []) P"
  by simp

end
