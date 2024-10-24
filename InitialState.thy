theory InitialState imports BasicInvariants 
begin

sledgehammer_params[timeout = 10]
definition"evict_test = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = ModifiedM\<rparr>,
    Type1State.devcache1         = \<lparr>CLEntry.content = Some 1, CLEntry.block_state = Modified\<rparr>,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Evict ],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"

definition GTSConfig :: "Type1State"
  where 
  "GTSConfig = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = SharedM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = \<lparr>CLEntry.content = Some 0, CLEntry.block_state = Shared\<rparr>, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Write  1],
    program2                     = [Write  2],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"

value "SWMR_state_machine evict_test"
value "SWMR_state_machine GTSConfig"
value "nat_to_id 3"

definition  initial_state:: "Type1State \<Rightarrow> bool"  where [simp]: 
  "initial_state T = (reqs1 T = [] \<and> reqs2 T = [] \<and> snps1 T = [] \<and> snps2 T = [] \<and> reqresps1 T = [] \<and> reqresps2 T = [] \<and>
    snpresps1 T = [] \<and> snpresps2 T = [] \<and> dthdatas1 T = [] \<and> dthdatas2 T = [] \<and> htddatas1 T = [] \<and> htddatas2 T = [] \<and> CSTATE Invalid T 0 \<and> CSTATE Invalid T 1 \<and> HSTATE InvalidM T)"

theorem initial_valid: assumes "initial_state T" shows " SWMR_state_machine T"
proof -
  have i0: "reqs1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i1: "reqs2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i2: "snps1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i3: "snps2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i4: "reqresps1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i5: "reqresps2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i6: "snpresps1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i7: "snpresps2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i8: "dthdatas1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i9: "dthdatas2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i10: "htddatas1 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i11: "htddatas2 T = []" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i12: "CSTATE Invalid T 0" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i13: "CSTATE Invalid T 1" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  have i14: "HSTATE InvalidM T" by(insert assms; unfold initial_state_def; elim conjE; assumption)
  show ?thesis
  unfolding SWMR_state_machine_def 

  (* super_sketch3 (intro conjI) (simp) (unfold  SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def) (cases "reqs1 T") (auto) *)
  proof (intro conjI)
  show goal1: "SWMR T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_various_forms1 MESI_State.distinct(5) MESI_State.distinct(95) i12) done
  show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(5) i13) done
  show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) MESI_State.distinct(5) i13) done
  show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) MESI_State.distinct(5) i13) done
  show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) MESI_State.distinct(5) i13) done
  show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) MESI_State.distinct(5) i13) done
  show goal15: "C_H_state Invalid nextStore Modified SAD T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal16: "C_H_state Invalid nextStore Modified SA T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal17: "C_H_state Invalid nextStore Modified SD T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal18: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal19: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal20: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal21: "C_msg_not RdShared IMAD T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(147) i12 i13) done
  show goal22: "C_msg_not RdShared Invalid T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant4 i14) done
  show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal27: "C_state_not MIA RdShared T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal37: "C_msg_state RdShared ISAD T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal38: "C_not_C_msg Modified ISAD nextGOPending T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) MESI_State.distinct(5) i13) done
  show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i10) 
apply (smt (verit) i11) 
apply (smt (verit) i10) 
apply (smt (verit) i11) 
 done

  show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i2 startsSnp.simps(1)) 
apply (smt (verit) i3 startsSnp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(143) i12 i13) done
  show goal42: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal43: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal44: "length (reqs1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i0 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal45: "length (reqs2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i1 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal46: "length (snps2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i3 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal47: "length (snps1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i2 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i3) 
apply (smt (verit) i2) 
apply (smt (verit) i3) 
apply (smt (verit) i2) 
 done

  show goal51: "CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i4 i7) done
  show goal52: "CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i5 i6) done
  show goal53: "CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i4 i7) done
  show goal54: "CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i5 i6) done
  show goal55: "CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i7) done
  show goal56: "CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i6) done
  show goal57: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal58: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal59: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal60: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal61: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal62: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE Modified T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal63: "CSTATE ISD T 0 \<longrightarrow> \<not> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal64: "CSTATE ISD T 1 \<longrightarrow> \<not> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal65: "CSTATE ISD T 0 \<longrightarrow> nextLoad T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal66: "CSTATE ISD T 1 \<longrightarrow> nextLoad T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(139) i12 i13) done
  show goal68: "length (htddatas1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i10 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal69: "length (htddatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i11 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal70: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i4 i7) done
  show goal71: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i5 i6) done
  show goal72: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal73: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal74: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal75: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal76: "length (reqresps1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i4 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal77: "length (reqresps2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i5 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal78: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal79: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal80: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i7) done
  show goal81: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i6) done
  show goal82: "CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12)done
  show goal83: "CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal85: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal86: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal87: "reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal88: "reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal89: "reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal90: "reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal91: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant4 i14) done
  show goal92: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant4 i14) done
  show goal93: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal94: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal95: "HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(163) i12) done
  show goal96: "HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(163) i13) done
  show goal97: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal98: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal99: "HSTATE SAD T \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant4 i14) done
  show goal100: "HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal101: "HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal102: "HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal103: "length (dthdatas1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i8 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal104: "length (dthdatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i9 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal105: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant4 i14) done
  show goal106: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant4 i14) done
  show goal107: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(113) HSTATE_invariant4 i14) done
  show goal108: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(113) HSTATE_invariant4 i14) done
  show goal109: "nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0"
    apply  (insert assms)(**)apply (smt (verit) i12) done
  show goal110: "nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i13) done
  show goal111: "nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or> CSTATE SIA T 0 \<or> CSTATE IIA T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal112: "nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or> CSTATE SIA T 1 \<or> CSTATE IIA T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal113: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal114: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal115: "length (snpresps1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i6 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal116: "length (snpresps2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i7 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal117: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant4 i14) done
  show goal118: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant4 i14) done
  show goal119: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6 nextSnpRespIs_invariant1) done
  show goal120: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7 nextSnpRespIs_invariant2) done
  show goal121: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal122: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal123: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal124: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal125: "HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal126: "HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal127: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal128: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal129: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal130: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal131: "dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal132: "dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal133: "CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal134: "CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal136: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal137: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal138: "CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal139: "CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal140: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal141: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal142: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal143: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal144: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal145: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal146: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant4 i14) done
  show goal147: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant4 i14) done
  show goal148: "HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6 i7) done
  show goal149: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant4 i14) done
  show goal150: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant4 i14) done
  show goal151: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal152: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal153: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal154: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal155: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal156: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal157: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal158: "HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal159: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal160: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal161: "CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(163) i12) done
  show goal162: "CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(163) i13) done
  show goal163: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal164: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal165: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal166: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal167: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal168: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal169: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal170: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal171: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal172: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal173: "HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal174: "CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal175: "CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal176: "HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal177: "HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal178: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) i8 nextDTHDataFrom_def) done
  show goal179: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) i10 i11 nextHTDDataPending_def) done
  show goal180: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i8) 
apply (smt (verit) i8) 
 done

  show goal181: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i8) 
apply (smt (verit) i8) 
 done

  show goal182: "HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal183: "HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal184: "HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(163) i12 i13) done
  show goal185: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal186: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal187: "CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal188: "CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal189: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal190: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal191: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal192: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal193: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal194: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal195: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant3 i14) done
  show goal196: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant3 i14) done
  show goal197: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant3 i14) done
  show goal198: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant3 i14) done
  show goal199: "HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal202: "CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i7) done
  show goal203: "CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i6) done
  show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal205: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal206: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal208: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal209: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal213: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal214: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal216: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal217: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal218: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal219: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal220: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal221: "C_not_C_msg Modified IMAD nextGOPending T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) MESI_State.distinct(5) i13) done
  show goal222: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal223: "CSTATE IMAD T 0 \<longrightarrow> nextStore T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal224: "CSTATE IMAD T 1 \<longrightarrow> nextStore T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal225: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal226: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal227: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal228: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal229: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal230: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal231: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal232: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal233: "CSTATE SMAD T 0 \<longrightarrow> nextStore T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal234: "CSTATE SMAD T 1 \<longrightarrow> nextStore T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal235: "C_msg_P_same IMA nextGOPending nextStore T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(149) i12 i13) done
  show goal236: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) MESI_State.distinct(149) MESI_State.distinct(169) i12) done
  show goal237: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) MESI_State.distinct(149) MESI_State.distinct(169) i13) done
  show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(149) i12 i13) done
  show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(169) i12 i13) done
  show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(141) i12 i13) done
  show goal241: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal242: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal243: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not> ((CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1 \<and> \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1 \<or> nextSnoopIs SnpInv T 1"
    apply  (insert assms)(**)apply (metis CSTATE_different1 MESI_State.distinct(147) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(171) i12) done
  show goal244: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not> ((CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0 \<or> nextSnoopIs SnpInv T 0"
    apply  (insert assms)(**)apply (metis CSTATE_disj1 INVALID_ROW_def MEM_RDS_COL_def MESI_State.distinct(147) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(171) i13) done
  show goal245: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal246: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal247: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal248: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal249: "C_msg_P_same SMA nextGOPending nextStore T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(169) i12 i13) done
  show goal250: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) MESI_State.distinct(169) MESI_State.distinct(171) i12) done
  show goal251: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) MESI_State.distinct(169) MESI_State.distinct(171) i13) done
  show goal252: "CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(141) MESI_State.distinct(143) MESI_State.distinct(145) i12) done
  show goal253: "CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(141) MESI_State.distinct(143) MESI_State.distinct(145) i13) done
  show goal254: "CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0 \<longrightarrow> nextStore T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(169) MESI_State.distinct(171) i12) done
  show goal255: "CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1 \<longrightarrow> nextStore T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(169) MESI_State.distinct(171) i13) done
  show goal256: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<or> CSTATE ISA T 0 \<or> nextHTDDataPending T 0 \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13 i8) done
  show goal257: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<or> CSTATE ISA T 1 \<or> nextHTDDataPending T 1 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12 i9) done
  show goal258: "CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) i12) done
  show goal259: "CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) i13) done
  show goal260: "CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal261: "CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal262: "CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3 i4 i7) done
  show goal263: "CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3 i5 i6) done
  show goal264: "CSTATE ISDI T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 1 \<or> \<not> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal265: "CSTATE ISDI T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 0 \<or> \<not> HSTATE ModifiedM T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal266: "CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal267: "CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal268: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i12) done
  show goal269: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal270: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i12) done
  show goal271: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal272: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal273: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal274: "CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal275: "CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal276: "nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal277: "nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal278: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal279: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal280: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal281: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal282: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal283: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal284: "HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6 i7) done
  show goal285: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant4 i14) done
  show goal286: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant4 i14) done
  show goal287: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant3 i14) done
  show goal288: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant3 i14) done
  show goal289: "HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant3 i14) done
  show goal290: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HSTATE_invariant4 i14) done
  show goal291: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HSTATE_invariant4 i14) done
  show goal292: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal293: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal294: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HSTATE_invariant3 i14) done
  show goal295: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HSTATE_invariant3 i14) done
  show goal296: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i1 i12) done
  show goal297: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i0 i13) done
  show goal298: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal299: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal300: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal301: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal302: "nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i6 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal303: "nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i7 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal304: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal305: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal306: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal307: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal308: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal309: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal310: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal311: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal312: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal313: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal314: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal315: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal316: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal317: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal318: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal319: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal320: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal321: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal322: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal323: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal324: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal325: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal326: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal327: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal328: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal329: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal330: "CSTATE Modified T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal331: "CSTATE Modified T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal332: "CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i4 i7) done
  show goal333: "CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i5 i6) done
  show goal334: "HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal335: "HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal336: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i12 i13) done
  show goal337: "nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal338: "nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal339: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal340: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal341: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal342: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal343: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal344: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal345: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal346: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal347: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal348: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal349: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal350: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal351: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal352: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal353: "HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i12 i13) done
  show goal354: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i12 i13) done
  show goal355: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i12 i13) done
  show goal356: "HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal357: "HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal358: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal359: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(167) i12 i13) done
  show goal361: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal362: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal363: "nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal364: "nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal365: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal366: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal367: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal368: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal369: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal370: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal371: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal372: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal373: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal374: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal375: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal376: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal377: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i12) done
  show goal378: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal379: "nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal380: "nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) i1 reqs2_empty_not_nextReqIs_general_invariant) done
  show goal381: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i9) 
  show goal382: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i8) 
apply (smt (verit) i8) 
 done

  show goal383: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal384: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal385: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal386: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal387: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<or> nextHTDDataPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(171) i12) done
  show goal388: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<or> nextHTDDataPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal389: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(171) i12) done
  show goal390: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal391: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(171) i12) done
  show goal392: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal393: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i4 i7) done
  show goal394: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i5 i6) done
  show goal395: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(171) i12) done
  show goal396: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal397: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal398: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal399: "CSTATE Shared T 0 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> HSTATE MD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal400: "CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i12) done
  show goal401: "CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal402: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal403: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal404: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal405: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal406: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal407: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal408: "CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal409: "CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal410: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(169) MESI_State.distinct(171) i12 i13) done
  show goal411: "HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(167) i12 i13) done
  show goal412: "nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i5 nextReqRespIs.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
 done

  show goal413: "CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal414: "CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal415: "nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal416: "nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal417: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(167) MESI_State.distinct(169) i12) done
  show goal418: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(167) MESI_State.distinct(169) i13) done
  show goal419: "CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i7) done
  show goal420: "CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i6) done
  show goal421: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal422: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal423: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal424: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal425: "HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i5 nextReqRespIs.simps(1)) 
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i5 nextReqRespIs.simps(1)) 
apply (smt (verit) i4 nextReqRespIs.simps(1)) 
apply (smt (verit) i5 nextReqRespIs.simps(1)) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) i0 list.discI) 
apply (smt (verit) HOST_State.distinct(75) HSTATE_def i14) 
apply (smt (verit) HOST_State.distinct(75) HSTATE_def i14) 
apply (smt (verit) HOST_State.distinct(5) HSTATE_def i14) 
apply (smt (verit) HOST_State.distinct(5) HSTATE_def i14) 
 done

  show goal426: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal427: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T"
    apply  (insert assms)(**)apply (smt (verit) i14) done
  show goal428: "HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8 i9) done
  show goal429: "CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i2 startsSnp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal430: "CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i3 startsSnp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal431: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal432: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal433: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) empty_no_snoop_variant i2) done
  show goal434: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) empty_no_snoop_variant2 i3) done
  show goal435: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal436: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal437: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal438: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal439: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(141) i12) done
  show goal440: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(141) i13) done
  show goal441: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(169) MESI_State.distinct(171) i12) done
  show goal442: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) MESI_State.distinct(171) i13) done
  show goal443: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(151) i12) done
  show goal444: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(151) i13) done
  show goal445: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal446: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal447: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal448: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal449: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal450: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal451: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal452: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal453: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) i12) done
  show goal454: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) i13) done
  show goal455: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal456: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal457: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal458: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal459: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal460: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal461: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal462: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal463: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal464: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal465: "CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(171) i12) done
  show goal466: "CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal467: "CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(169) i12) done
  show goal468: "CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal469: "CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(141) i12) done
  show goal470: "CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(141) i13) done
  show goal471: "CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal472: "CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal473: "CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal474: "CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal475: "CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) i12) done
  show goal476: "CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) i13) done
  show goal477: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal478: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal479: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal480: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal481: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal482: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal483: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i12) done
  show goal484: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal485: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) i12) done
  show goal486: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) i13) done
  show goal487: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal488: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal489: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal490: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal491: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(169) i12) done
  show goal492: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(169) i13) done
  show goal493: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) MESI_State.distinct(171) i12) done
  show goal494: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) MESI_State.distinct(171) i13) done
  show goal495: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal496: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal497: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal498: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal499: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal500: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal501: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(151) MESI_State.distinct(171) i12) done
  show goal502: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(151) MESI_State.distinct(171) i13) done
  show goal503: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal504: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal505: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal506: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal507: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal508: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal509: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(141) MESI_State.distinct(149) MESI_State.distinct(169) i12) done
  show goal510: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) MESI_State.distinct(149) MESI_State.distinct(169) i13) done
  show goal511: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i10) 
apply (smt (verit) i10) 
 done

  show goal512: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i11) 
apply (smt (verit) i11) 
 done

  show goal513: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(95) i12) done
  show goal514: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(95) i13) done
  show goal515: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal516: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal517: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i4 i7) done
  show goal518: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i5 i6) done
  show goal519: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal520: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal521: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal522: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal523: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal524: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal525: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal526: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal527: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) i12) done
  show goal528: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal529: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal530: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal531: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(147) i12) done
  show goal532: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal533: "HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i12 i13) done
  show goal534: "HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal535: "HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal536: "HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(5) i12 i13) done
  show goal537: "HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i8 i9 list.size(3) zero_less_one_class.zero_le_one) done
  show goal538: "HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i8 i9 list.size(3) zero_less_one_class.zero_le_one) done
  show goal539: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal540: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal541: "HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i8 i9 list.size(3) zero_less_one_class.zero_le_one) done
  show goal542: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal543: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal544: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal545: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal546: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal547: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal548: "HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3) done
  show goal549: "HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3) done
  show goal550: "HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3) done
  show goal551: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal552: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal553: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal554: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal555: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal556: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal557: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) MESI_State.distinct(171) i12) done
  show goal558: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) MESI_State.distinct(171) i13) done
  show goal559: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(151) MESI_State.distinct(171) i12) done
  show goal560: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) MESI_State.distinct(171) i13) done
  show goal561: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal562: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal563: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal564: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal565: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal566: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal567: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal568: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal569: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(143) i12) done
  show goal570: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal571: "HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal572: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal573: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal574: "HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal575: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal576: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal577: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal578: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal579: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal580: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(5) HSTATE_invariant3 i14) done
  show goal581: "HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(141) i12 i13) done
  show goal582: "HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(141) i12 i13) done
  show goal583: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal584: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal585: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) MESI_State.distinct(171) i13) done
  show goal586: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal587: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(151) i13) done
  show goal588: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal589: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal590: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal591: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal592: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal593: "CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal594: "CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal595: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal596: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal597: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) MESI_State.distinct(141) i12) done
  show goal598: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) MESI_State.distinct(141) i13) done
  show goal599: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(169) MESI_State.distinct(171) i12) done
  show goal600: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) MESI_State.distinct(171) i13) done
  show goal601: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(151) i12) done
  show goal602: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(151) i13) done
  show goal603: "HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal604: "HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal605: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal606: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal607: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal608: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal609: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal610: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal611: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(145) i13) done
  show goal612: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(145) i12) done
  show goal613: "HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal614: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal615: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal616: "HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal617: "snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal618: "snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal619: "CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i5 i6) done
  show goal620: "CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i4 i7) done
  show goal621: "nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant3 i14) done
  show goal622: "nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(121) HSTATE_invariant3 i14) done
  show goal623: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal624: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal625: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) MESI_State.distinct(95) i13) done
  show goal626: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal627: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal628: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal629: "HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(113) HSTATE_invariant3 i14) done
  show goal630: "HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(75) HSTATE_invariant3 i14) done
  show goal631: "CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal632: "CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal633: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal634: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal635: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(139) i12 i13) done
  show goal636: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) i12) done
  show goal637: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) i13) done
  show goal638: "HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal639: "HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6 i7) done
  show goal640: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal641: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal642: "HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal643: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal644: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(135) HSTATE_invariant3 i14) done
  show goal645: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(141) i12 i13) done
  show goal646: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal647: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal648: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal649: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(139) HSTATE_invariant3 i14) done
  show goal650: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(137) HSTATE_invariant3 i14) done
  show goal651: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(137) HSTATE_invariant3 i14) done
  show goal652: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal653: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal654: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal655: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(115) HSTATE_invariant3 i14) done
  show goal656: "CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(5) i12) done
  show goal657: "CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal658: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(139) i13) done
  show goal659: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal660: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal661: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal662: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal663: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal664: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) i13) done
  show goal665: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal666: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<or> CSTATE ISA T 0 \<or> nextHTDDataPending T 0 \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal667: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<or> CSTATE ISA T 1 \<or> nextHTDDataPending T 1 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) i12) done
  show goal668: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal669: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal670: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 Invalid_not_eq_MIA i12) done
  show goal671: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal672: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal673: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal674: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(169) i11 i13) done
  show goal675: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal676: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal677: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal678: "CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal679: "CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal680: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(143) i13) done
  show goal681: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal682: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(141) MESI_State.distinct(95) i13) done
  show goal683: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal684: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal685: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal686: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal687: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal688: "CSTATE Invalid T 0 \<longrightarrow> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal689: "CSTATE Invalid T 1 \<longrightarrow> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal690: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant4 i14) done
  show goal691: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(111) HSTATE_invariant4 i14) done
  show goal692: "HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(109) HSTATE_invariant3 i14) done
  show goal693: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal694: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal695: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal696: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal697: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal698: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i7) done
  show goal699: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i6) done
  show goal700: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal701: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal702: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal703: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal704: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal705: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal706: "HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(175) i12 i13) done
  show goal707: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal708: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant4 i14) done
  show goal709: "length (dthdatas1 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i8 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal710: "length (dthdatas2 T) \<le> 1"
    apply  (insert assms)(**)apply (smt (verit) i9 linordered_nonzero_semiring_class.zero_le_one list.size(3)) done
  show goal711: "HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i12) done
  show goal712: "HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(163) i13) done
  show goal713: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal714: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(95) i12 i13) done
  show goal715: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) i6) done
  show goal716: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    apply  (insert assms)(**)apply (smt (verit) i7) done
  show goal717: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i5 i6) done
  show goal718: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3 i4 i7) done
  show goal719: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(169) i11 i13) done
  show goal720: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal721: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(169) i11 i13) done
  show goal722: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal723: "CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i8) done
  show goal724: "CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i9) done
  show goal725: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(149) MESI_State.distinct(169) i12) done
  show goal726: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) MESI_State.distinct(169) i13) done
  show goal727: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal728: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(151) i13) done
  show goal729: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal730: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(171) i13) done
  show goal731: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal732: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(149) i13) done
  show goal733: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal734: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal735: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal736: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(147) i13) done
  show goal737: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal738: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal739: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal740: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal741: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(167) i12 i13) done
  show goal742: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(167) i12 i13) done
  show goal743: "HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 MESI_State.distinct(167) i12 i13) done
  show goal744: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant3 i14) done
  show goal745: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant3 i14) done
  show goal746: "CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11) done
  show goal747: "CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10) done
  show goal748: "HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2 i3) done
  show goal749: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) empty_no_snoop_variant i2) done
  show goal750: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) empty_no_snoop_variant2 i3) done
  show goal751: "CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(167) i13) done
  show goal752: "CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(167) i12) done
  show goal753: "CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(5) i13) done
  show goal754: "CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal755: "CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i12) done
  show goal756: "CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal757: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i10 i3 i7) done
  show goal758: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i11 i2 i6) done
  show goal759: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(179) i12) done
  show goal760: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(179) i13) done
  show goal761: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i12) done
  show goal762: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal763: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i12) done
  show goal764: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal765: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal766: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal767: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> reqs1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i0) done
  show goal768: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> reqs2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i1) done
  show goal769: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant3 i14) done
  show goal770: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(119) HSTATE_invariant3 i14) done
  show goal771: "HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_different2 Invalid_not_eq_MIA i12 i13) done
  show goal772: "nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal773: "nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i1 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal774: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i8) 
apply (smt (verit) i8) 
 done

  show goal775: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    apply  (insert assms)(**)apply (smt (verit) i7 nextSnpRespIs_invariant2) done
  show goal776: "nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0"
     apply  (cases "reqs1 T") apply  (auto)
by (smt (verit) i0 list.discI) 
  show goal777: "nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1"
     apply  (cases "reqs1 T") apply  (auto)
apply (smt (verit) i7 startsWithProp.simps(1)) 
apply (smt (verit) i0 list.discI) 
 done

  show goal778: "CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(169) i12) done
  show goal779: "CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(169) i13) done
  show goal780: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(175) i12) done
  show goal781: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(175) i13) done
  show goal782: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(179) i12) done
  show goal783: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_disj1 MESI_State.distinct(179) i13) done
  show goal784: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i12) done
  show goal785: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal786: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i12) done
  show goal787: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(179) i13) done
  show goal788: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i3) done
  show goal789: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i2) done
  show goal790: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    apply  (insert assms)(**)apply (smt (verit) i4) done
  show goal791: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    apply  (insert assms)(**)apply (smt (verit) i5) done
  show goal792: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal793: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i12) done
  show goal794: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> \<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 MESI_State.distinct(175) i13) done
  show goal795: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> \<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0"
    apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 Invalid_not_eq_MIA i13) done
  show goal796: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    using i14 by auto
qed
qed


end