theory Toggle imports BasicInvariants begin

text \<open>Swapping the two devices.  The invariant \<open>SWMR_state_machine\<close> is symmetric under this swap,
which is what allows the rule lemmas (stated for device index 0) to be transferred to index 1.\<close>

definition toggle :: "Type1State \<Rightarrow> Type1State" where [simp]:
  "toggle T = T \<lparr>
     devcache1   := devcache2 T,     devcache2   := devcache1 T,
     reqs1       := reqs2 T,         reqs2       := reqs1 T,
     snpresps1   := snpresps2 T,     snpresps2   := snpresps1 T,
     dthdatas1   := dthdatas2 T,     dthdatas2   := dthdatas1 T,
     snps1       := snps2 T,         snps2       := snps1 T,
     reqresps1   := reqresps2 T,     reqresps2   := reqresps1 T,
     htddatas1   := htddatas2 T,     htddatas2   := htddatas1 T,
     program1    := program2 T,      program2    := program1 T,
     registers11 := registers21 T,   registers21 := registers11 T,
     registers12 := registers22 T,   registers22 := registers12 T,
     buffer1     := buffer2 T,       buffer2     := buffer1 T
   \<rparr>"

lemma toggle_toggle [simp]: "toggle (toggle T) = T"
  by simp

subsection \<open>Record fields\<close>

lemma devcache1_toggle: "devcache1 (toggle T) = devcache2 T" by simp
lemma devcache2_toggle: "devcache2 (toggle T) = devcache1 T" by simp
lemma hostcache_toggle: "hostcache (toggle T) = hostcache T" by simp
lemma reqs1_toggle: "reqs1 (toggle T) = reqs2 T" by simp
lemma reqs2_toggle: "reqs2 (toggle T) = reqs1 T" by simp
lemma snpresps1_toggle: "snpresps1 (toggle T) = snpresps2 T" by simp
lemma snpresps2_toggle: "snpresps2 (toggle T) = snpresps1 T" by simp
lemma dthdatas1_toggle: "dthdatas1 (toggle T) = dthdatas2 T" by simp
lemma dthdatas2_toggle: "dthdatas2 (toggle T) = dthdatas1 T" by simp
lemma snps1_toggle: "snps1 (toggle T) = snps2 T" by simp
lemma snps2_toggle: "snps2 (toggle T) = snps1 T" by simp
lemma reqresps1_toggle: "reqresps1 (toggle T) = reqresps2 T" by simp
lemma reqresps2_toggle: "reqresps2 (toggle T) = reqresps1 T" by simp
lemma htddatas1_toggle: "htddatas1 (toggle T) = htddatas2 T" by simp
lemma htddatas2_toggle: "htddatas2 (toggle T) = htddatas1 T" by simp
lemma program1_toggle: "program1 (toggle T) = program2 T" by simp
lemma program2_toggle: "program2 (toggle T) = program1 T" by simp
lemma buffer1_toggle: "buffer1 (toggle T) = buffer2 T" by simp
lemma buffer2_toggle: "buffer2 (toggle T) = buffer1 T" by simp
lemma counter_toggle: "counter (toggle T) = counter T" by simp
lemma clock_toggle: "clock (toggle T) = clock T" by simp

subsection \<open>State predicates\<close>

lemma CSTATE_toggle0: "CSTATE x (toggle T) 0 = CSTATE x T 1" by simp
lemma CSTATE_toggle1: "CSTATE x (toggle T) 1 = CSTATE x T 0" by simp
lemma HSTATE_toggle: "HSTATE x (toggle T) = HSTATE x T" by simp
lemma lastSharer_toggle: "lastSharer (toggle T) = lastSharer T" by auto

lemma nextDTHDataFrom_toggle0: "nextDTHDataFrom 0 (toggle T) = nextDTHDataFrom 1 T" by simp
lemma nextDTHDataFrom_toggle1: "nextDTHDataFrom 1 (toggle T) = nextDTHDataFrom 0 T" by simp
lemma nextDTHDataPending_toggle0: "nextDTHDataPending (toggle T) 0 = nextDTHDataPending T 1" by simp
lemma nextDTHDataPending_toggle1: "nextDTHDataPending (toggle T) 1 = nextDTHDataPending T 0" by simp
lemma nextEvict_toggle0: "nextEvict (toggle T) 0 = nextEvict T 1" by simp
lemma nextEvict_toggle1: "nextEvict (toggle T) 1 = nextEvict T 0" by simp
lemma nextLoad_toggle0: "nextLoad (toggle T) 0 = nextLoad T 1" by simp
lemma nextLoad_toggle1: "nextLoad (toggle T) 1 = nextLoad T 0" by simp
lemma nextStore_toggle0: "nextStore (toggle T) 0 = nextStore T 1" by simp
lemma nextStore_toggle1: "nextStore (toggle T) 1 = nextStore T 0" by simp
lemma nextGOPending_toggle0: "nextGOPending (toggle T) 0 = nextGOPending T 1" by simp
lemma nextGOPending_toggle1: "nextGOPending (toggle T) 1 = nextGOPending T 0" by simp
lemma nextGOPendingIs_toggle0: "nextGOPendingIs r (toggle T) 0 = nextGOPendingIs r T 1" by simp
lemma nextGOPendingIs_toggle1: "nextGOPendingIs r (toggle T) 1 = nextGOPendingIs r T 0" by simp
lemma nextGOPendingState_toggle0: "nextGOPendingState m (toggle T) 0 = nextGOPendingState m T 1" by simp
lemma nextGOPendingState_toggle1: "nextGOPendingState m (toggle T) 1 = nextGOPendingState m T 0" by simp
lemma nextHTDDataPending_toggle0: "nextHTDDataPending (toggle T) 0 = nextHTDDataPending T 1" by simp
lemma nextHTDDataPending_toggle1: "nextHTDDataPending (toggle T) 1 = nextHTDDataPending T 0" by simp
lemma nextSnpRespPending_toggle0: "nextSnpRespPending (toggle T) 0 = nextSnpRespPending T 1" by simp
lemma nextSnpRespPending_toggle1: "nextSnpRespPending (toggle T) 1 = nextSnpRespPending T 0" by simp
lemma nextReqPending_toggle0: "nextReqPending (toggle T) 0 = nextReqPending T 1" by simp
lemma nextReqPending_toggle1: "nextReqPending (toggle T) 1 = nextReqPending T 0" by simp
lemma nextReqIs_toggle0: "nextReqIs r (toggle T) 0 = nextReqIs r T 1" by simp
lemma nextReqIs_toggle1: "nextReqIs r (toggle T) 1 = nextReqIs r T 0" by simp
lemma nextSnpRespIs_toggle0: "nextSnpRespIs r (toggle T) 0 = nextSnpRespIs r T 1" by simp
lemma nextSnpRespIs_toggle1: "nextSnpRespIs r (toggle T) 1 = nextSnpRespIs r T 0" by simp
lemma nextSnoopIs_toggle0: "nextSnoopIs s (toggle T) 0 = nextSnoopIs s T 1" by simp
lemma nextSnoopIs_toggle1: "nextSnoopIs s (toggle T) 1 = nextSnoopIs s T 0" by simp
lemma nextSnoopPending_toggle0: "nextSnoopPending (toggle T) 0 = nextSnoopPending T 1" by simp
lemma nextSnoopPending_toggle1: "nextSnoopPending (toggle T) 1 = nextSnoopPending T 0" by simp
lemma CXL_SPG_used_toggle0: "CXL_SPG_used (toggle T) 0 = CXL_SPG_used T 1" by simp
lemma CXL_SPG_used_toggle1: "CXL_SPG_used (toggle T) 1 = CXL_SPG_used T 0" by simp
lemma GTS_toggle0: "GTS (toggle T) 0 = GTS T 1" by simp
lemma GTS_toggle1: "GTS (toggle T) 1 = GTS T 0" by simp

lemmas toggle_eqs =
  devcache1_toggle devcache2_toggle hostcache_toggle
  reqs1_toggle reqs2_toggle snpresps1_toggle snpresps2_toggle dthdatas1_toggle dthdatas2_toggle
  snps1_toggle snps2_toggle reqresps1_toggle reqresps2_toggle htddatas1_toggle htddatas2_toggle
  program1_toggle program2_toggle buffer1_toggle buffer2_toggle counter_toggle clock_toggle
  CSTATE_toggle0 CSTATE_toggle1 HSTATE_toggle lastSharer_toggle
  nextDTHDataFrom_toggle0 nextDTHDataFrom_toggle1 nextDTHDataPending_toggle0 nextDTHDataPending_toggle1
  nextEvict_toggle0 nextEvict_toggle1 nextLoad_toggle0 nextLoad_toggle1 nextStore_toggle0 nextStore_toggle1
  nextGOPending_toggle0 nextGOPending_toggle1 nextGOPendingIs_toggle0 nextGOPendingIs_toggle1
  nextGOPendingState_toggle0 nextGOPendingState_toggle1 nextHTDDataPending_toggle0 nextHTDDataPending_toggle1
  nextSnpRespPending_toggle0 nextSnpRespPending_toggle1 nextReqPending_toggle0 nextReqPending_toggle1
  nextReqIs_toggle0 nextReqIs_toggle1 nextSnpRespIs_toggle0 nextSnpRespIs_toggle1
  nextSnoopIs_toggle0 nextSnoopIs_toggle1 nextSnoopPending_toggle0 nextSnoopPending_toggle1
  CXL_SPG_used_toggle0 CXL_SPG_used_toggle1 GTS_toggle0 GTS_toggle1

lemmas invariant_wrappers =
  SWMR_def C_msg_P_oppo_def C_msg_P_same_def C_msg_P_host_def C_not_C_msg_def
  H_msg_P_same_def H_msg_P_oppo_def C_H_state_def C_msg_not_def C_msg_state_def C_state_not_def
  H_C_state_msg_same_def H_C_state_msg_oppo_def C_m_h_C_def C_m_h_m_def

subsection \<open>Symmetry of the invariant\<close>

text \<open>Each conjunct of \<open>SWMR_state_machine (toggle T)\<close>, after rewriting with the
equations above, is a conjunct of \<open>SWMR_state_machine T\<close> for the other device (up to the order
of conjuncts and disjuncts).\<close>

lemma symmetry: assumes "SWMR_state_machine T" shows "SWMR_state_machine (toggle T)"
proof -
  have i1: "SWMR T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i15: "C_H_state Invalid nextStore Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i16: "C_H_state Invalid nextStore Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i17: "C_H_state Invalid nextStore Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i18: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i19: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i20: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i21: "C_msg_not RdShared IMAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i22: "C_msg_not RdShared Invalid T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i27: "C_state_not MIA RdShared T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i37: "C_msg_state RdShared ISAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i38: "C_not_C_msg Modified ISAD nextGOPending T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i42: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i43: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i44: "length (reqs1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i45: "length (reqs2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i46: "length (snps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i47: "length (snps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i51: "CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i52: "CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i53: "CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i54: "CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i55: "CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i56: "CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i57: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i58: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i59: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i60: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i61: "CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i62: "CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i63: "CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i64: "CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i65: "CSTATE ISD T 0 \<longrightarrow> nextLoad T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i66: "CSTATE ISD T 1 \<longrightarrow> nextLoad T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i68: "length (htddatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i69: "length (htddatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i70: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i71: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i72: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i73: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i74: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i75: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i76: "length (reqresps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i77: "length (reqresps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i78: "CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i79: "CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i80: "CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i81: "CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i82: "CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i83: "CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i84: "C_msg_P_same MIA (nextReqIs DirtyEvict) (nextEvict) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i85: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i86: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i87: "reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i88: "reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i89: "reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i90: "reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i91: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i92: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i93: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i94: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i95: "HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i96: "HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i97: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i98: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i99: "HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i100: "HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i101: "HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i102: "HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i103: "length (dthdatas1 T ) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i104: "length (dthdatas2 T ) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i105: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i106: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i107: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i108: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i109: "(nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i110: "(nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i111: "nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or> CSTATE SIA T 0 \<or> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i112: "nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or> CSTATE SIA T 1 \<or> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i113: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i114: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i115: "length (snpresps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i116: "length (snpresps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i117: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i118: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i119: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i120: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i121: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i122: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i123: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i124: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i125: "HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i126: "HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i127: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i128: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i129: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i130: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i131: "dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i132: "dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i133: "CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i134: "CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i136: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i137: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i138: "CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i139: "CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i140: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i141: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i142: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i143: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i144: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i145: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i146: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i147: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i148: "HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i149: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i150: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i151: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i152: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i153: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i154: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i155: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i156: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i157: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i158: "HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i159: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i160: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i161: "CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i162: "CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i163: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i164: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i165: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i166: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i167: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i168: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i169: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i170: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i171: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i172: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i173: "HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i174: "CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i175: "CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i176: "HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i177: "HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i178: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i179: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i180: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i181: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i182: "HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i183: "HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i184: "HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i185: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i186: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i187: "CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i188: "CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i189: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i190: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i191: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i192: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i193: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i194: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i195: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i196: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i197: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i198: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i199: "HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i202: "CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i203: "CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i205: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i206: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i208: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i209: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i213: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i214: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i216: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i217: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i218: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i219: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i220: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i221: "C_not_C_msg Modified IMAD nextGOPending T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i222: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i223: "CSTATE IMAD T 0 \<longrightarrow> nextStore T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i224: "CSTATE IMAD T 1 \<longrightarrow> nextStore T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i225: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i226: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i227: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i228: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i229: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i230: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i231: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i232: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i233: "CSTATE SMAD T 0 \<longrightarrow> nextStore T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i234: "CSTATE SMAD T 1 \<longrightarrow> nextStore T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i235: "C_msg_P_same IMA (nextGOPending) nextStore T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i236: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i237: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i238: "C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i239: "C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i240: "C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i241: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i242: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i243: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> ( nextHTDDataPending T 1) \<and> \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i244: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> ( nextHTDDataPending T 0) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i245: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i246: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i247: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i248: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i249: "C_msg_P_same SMA (nextGOPending) nextStore T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i250: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i251: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i252: "CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i253: "CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i254: "CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0 \<longrightarrow> nextStore T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i255: "CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1 \<longrightarrow> nextStore T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i256: "(CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i257: "(CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i258: "CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i259: "CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i260: "CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i261: "CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i262: "CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i263: "CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i264: "CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i265: "CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i266: "CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i267: "CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i268: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i269: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i270: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i271: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i272: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i273: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i274: "CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i275: "CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i276: "nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i277: "nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i278: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i279: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i280: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i281: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i282: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i283: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i284: "HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i285: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i286: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i287: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i288: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i289: "HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i290: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i291: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i292: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i293: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i294: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i295: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i296: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i297: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i298: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i299: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i300: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i301: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i302: "nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i303: "nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i304: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i305: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i306: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i307: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i308: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i309: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i310: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i311: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i312: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i313: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i314: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i315: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i316: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i317: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i318: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i319: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i320: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i321: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i322: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i323: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i324: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i325: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i326: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i327: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i328: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i329: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i330: "CSTATE Modified T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i331: "CSTATE Modified T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i332: "CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i333: "CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i334: "HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i335: "HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i336: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i337: "nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i338: "nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i339: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i340: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i341: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i342: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i343: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i344: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i345: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i346: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i347: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i348: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i349: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i350: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i351: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i352: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i353: "HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i354: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i355: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i356: "HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i357: "HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i358: "CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i359: "CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i361: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i362: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i363: "nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i364: "nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i365: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i366: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i367: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i368: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i369: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i370: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i371: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i372: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i373: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i374: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i375: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i376: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i377: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i378: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i379: "nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i380: "nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i381: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i382: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i383: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i384: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i385: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i386: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i387: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i388: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i389: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i390: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i391: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i392: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i393: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i394: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i395: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i396: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i397: "(nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i398: "(nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i399: "(CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i400: "CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i401: "CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i402: "(nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i403: "(nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i404: "(nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i405: "(nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i406: "(nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i407: "(nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i408: "CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i409: "CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i410: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i411: "HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i412: "nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i413: "CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i414: "CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i415: "nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i416: "nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i417: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i418: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i419: "CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i420: "CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i421: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i422: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i423: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i424: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i425: "(HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i426: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i427: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i428: "HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i429: "CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i430: "CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i431: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i432: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i433: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i434: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i435: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i436: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i437: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i438: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i439: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i440: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i441: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i442: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i443: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i444: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i445: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i446: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i447: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i448: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i449: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i450: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i451: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i452: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i453: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i454: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i455: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i456: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i457: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i458: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i459: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i460: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i461: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i462: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i463: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i464: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i465: "CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i466: "CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i467: "CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i468: "CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i469: "CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i470: "CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i471: "CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i472: "CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i473: "CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i474: "CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i475: "CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i476: "CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i477: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i478: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i479: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i480: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i481: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i482: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i483: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i484: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i485: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i486: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i487: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i488: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i489: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i490: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i491: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i492: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i493: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i494: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i495: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i496: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i497: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i498: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i499: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i500: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i501: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i502: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i503: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i504: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i505: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i506: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i507: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i508: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i509: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i510: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i511: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i512: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i513: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i514: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i515: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i516: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i517: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i518: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i519: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i520: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i521: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i522: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i523: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i524: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i525: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i526: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i527: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i528: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i529: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i530: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i531: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i532: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i533: "HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i534: "HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i535: "HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i536: "HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i537: "HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i538: "HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i539: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i540: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i541: "HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i542: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i543: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i544: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i545: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i546: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i547: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i548: "HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i549: "HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i550: "HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i551: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i552: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i553: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i554: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i555: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i556: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i557: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i558: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i559: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i560: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i561: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i562: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i563: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i564: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i565: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i566: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i567: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i568: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i569: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i570: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i571: "HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i572: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i573: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i574: "HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i575: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i576: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i577: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i578: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i579: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i580: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i581: "HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i582: "HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i583: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i584: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i585: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i586: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i587: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i588: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i589: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i590: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i591: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i592: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i593: "CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i594: "CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i595: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i596: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i597: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i598: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i599: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i600: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i601: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i602: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i603: "HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i604: "HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i605: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i606: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i607: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i608: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i609: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i610: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i611: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i612: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i613: "HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i614: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i615: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i616: "HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i617: "snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i618: "snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i619: "CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i620: "CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i621: "nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i622: "nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i623: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i624: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i625: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i626: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i627: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i628: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i629: "HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i630: "HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i631: "CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i632: "CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i633: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i634: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i635: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i636: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i637: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i638: "HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i639: "HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i640: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i641: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i642: "HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i643: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i644: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i645: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i646: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i647: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i648: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i649: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i650: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i651: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i652: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i653: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i654: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i655: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i656: "CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i657: "CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i658: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i659: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i660: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i661: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i662: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i663: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i664: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i665: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i666: "(CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i667: "(CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i668: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i669: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i670: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i671: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i672: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i673: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i674: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i675: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i676: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i677: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i678: "CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i679: "CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i680: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i681: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i682: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i683: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i684: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i685: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i686: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i687: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i688: "CSTATE Invalid T 0 \<longrightarrow> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i689: "CSTATE Invalid T 1 \<longrightarrow> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i690: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i691: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i692: "HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i693: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i694: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i695: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i696: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i697: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i698: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i699: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i700: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i701: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i702: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i703: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i704: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i705: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i706: "HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i707: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i708: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i709: "length (dthdatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i710: "length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i711: "HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i712: "HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i713: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i714: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i715: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i716: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i717: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i718: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i719: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i720: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i721: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i722: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i723: "CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i724: "CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i725: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i726: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i727: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i728: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i729: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i730: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i731: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i732: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i733: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i734: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i735: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i736: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i737: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i738: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i739: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i740: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i741: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i742: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i743: "HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i744: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i745: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i746: "CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i747: "CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i748: "HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i749: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i750: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i751: "CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i752: "CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i753: "CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i754: "CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i755: "CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i756: "CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i757: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i758: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i759: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i760: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i761: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i762: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i763: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i764: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i765: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i766: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i767: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i768: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i769: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i770: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i771: "HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i772: "nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i773: "nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i774: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i775: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i776: "nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i777: "nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i778: "CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i779: "CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i780: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i781: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i782: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i783: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i784: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i785: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i786: "(CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i787: "(CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i788: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i789: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i790: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i791: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i792: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i793: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i794: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i795: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i796: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis
    unfolding SWMR_state_machine_def
  proof (intro conjI)
    show "SWMR (toggle T)"
      apply (insert i1) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i2) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i3) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i4) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i5) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i6) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i7) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (toggle T)"
      apply (insert i8) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) (toggle T)"
      apply (insert i9) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) (toggle T)"
      apply (insert i10) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) (toggle T)"
      apply (insert i11) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state IMAD (nextReqIs RdOwn) Modified SD (toggle T)"
      apply (insert i12) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state IMAD (nextReqIs RdOwn) Modified SAD (toggle T)"
      apply (insert i13) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state IMAD (nextReqIs RdOwn) Modified SA (toggle T)"
      apply (insert i14) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state Invalid nextStore Modified SAD (toggle T)"
      apply (insert i15) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state Invalid nextStore Modified SA (toggle T)"
      apply (insert i16) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_H_state Invalid nextStore Modified SD (toggle T)"
      apply (insert i17) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i18) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i19) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i20) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_not RdShared IMAD (toggle T)"
      apply (insert i21) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_not RdShared Invalid (toggle T)"
      apply (insert i22) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) (toggle T)"
      apply (insert i23) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) (toggle T)"
      apply (insert i24) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict (toggle T)"
      apply (insert i25) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) (toggle T)"
      apply (insert i26) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_state_not MIA RdShared (toggle T)"
      apply (insert i27) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict (toggle T)"
      apply (insert i28) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i29) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) (toggle T)"
      apply (insert i30) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i31) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict (toggle T)"
      apply (insert i32) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i33) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) (toggle T)"
      apply (insert i34) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i35) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) (toggle T)"
      apply (insert i36) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_state RdShared ISAD (toggle T)"
      apply (insert i37) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_not_C_msg Modified ISAD nextGOPending (toggle T)"
      apply (insert i38) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) (toggle T)"
      apply (insert i39) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) (toggle T)"
      apply (insert i40) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i41) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snps2 (toggle T) \<noteq> [] \<longrightarrow> reqs1 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> dthdatas2 (toggle T) = [] \<and> reqresps1 (toggle T) = []"
      apply (insert i43) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snps1 (toggle T) \<noteq> [] \<longrightarrow> reqs2 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> dthdatas1 (toggle T) = [] \<and> reqresps2 (toggle T) = []"
      apply (insert i42) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (reqs1 (toggle T)) \<le> 1"
      apply (insert i45) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (reqs2 (toggle T)) \<le> 1"
      apply (insert i44) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (snps2 (toggle T)) \<le> 1"
      apply (insert i47) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (snps1 (toggle T)) \<le> 1"
      apply (insert i46) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) (toggle T)"
      apply (insert i48) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i49) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) (toggle T)"
      apply (insert i50) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i52) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i51) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i54) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i53) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i56) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i55) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 0 \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i58) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 1 \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i57) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i60) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i59) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> \<not>CSTATE Modified (toggle T) 1"
      apply (insert i62) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> \<not>CSTATE Modified (toggle T) 0"
      apply (insert i61) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<longrightarrow> \<not>HSTATE ModifiedM (toggle T)"
      apply (insert i64) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<longrightarrow> \<not>HSTATE ModifiedM (toggle T)"
      apply (insert i63) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<longrightarrow> nextLoad (toggle T) 0"
      apply (insert i66) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<longrightarrow> nextLoad (toggle T) 1"
      apply (insert i65) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) (toggle T)"
      apply (insert i67) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (htddatas1 (toggle T)) \<le> 1"
      apply (insert i69) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (htddatas2 (toggle T)) \<le> 1"
      apply (insert i68) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = []"
      apply (insert i71) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = []"
      apply (insert i70) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i73) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i72) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i75) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i74) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (reqresps1 (toggle T)) \<le> 1"
      apply (insert i77) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (reqresps2 (toggle T)) \<le> 1"
      apply (insert i76) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> (nextGOPendingIs GO_WritePull (toggle T) 0) \<longrightarrow> snps1 (toggle T) = []"
      apply (insert i79) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> (nextGOPendingIs GO_WritePull (toggle T) 1) \<longrightarrow> snps2 (toggle T) = []"
      apply (insert i78) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> (nextGOPendingIs GO_WritePull (toggle T) 0) \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i81) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> (nextGOPendingIs GO_WritePull (toggle T) 1) \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i80) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i83) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i82) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same MIA (nextReqIs DirtyEvict) (nextEvict) (toggle T)"
      apply (insert i84) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs1 (toggle T) \<noteq> [] \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i86) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs2 (toggle T) \<noteq> [] \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i85) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs1 (toggle T) \<noteq> [] \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i88) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs2 (toggle T) \<noteq> [] \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i87) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs1 (toggle T) \<noteq> [] \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i90) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs2 (toggle T) \<noteq> [] \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i89) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> (CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1)"
      apply (insert i92) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> (CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0)"
      apply (insert i91) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> (CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1)"
      apply (insert i94) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> (CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0)"
      apply (insert i93) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> CSTATE IIA (toggle T) 0 \<longrightarrow> (CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1)"
      apply (insert i96) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> CSTATE IIA (toggle T) 1 \<longrightarrow> (CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0)"
      apply (insert i95) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs1 (toggle T) \<noteq> [] \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i86) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "reqs2 (toggle T) \<noteq> [] \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i85) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<longrightarrow> (CSTATE ISAD (toggle T) 0 \<or> CSTATE ISAD (toggle T) 1)"
      apply (insert i99) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> \<not>CSTATE Shared (toggle T) 0 \<and> \<not>CSTATE Shared (toggle T) 1"
      apply (insert i100) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> dthdatas1 (toggle T) \<noteq> [] \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i102) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> dthdatas2 (toggle T) \<noteq> [] \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i101) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (dthdatas1 (toggle T) ) \<le> 1"
      apply (insert i104) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (dthdatas2 (toggle T) ) \<le> 1"
      apply (insert i103) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> (CSTATE ISAD (toggle T) 1 \<or> CSTATE ISD (toggle T) 1)"
      apply (insert i106) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> (CSTATE ISAD (toggle T) 0 \<or> CSTATE ISD (toggle T) 0)"
      apply (insert i105) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SA (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 0 \<or> nextSnpRespIs RspSFwdM (toggle T) 0) \<longrightarrow> CSTATE ISAD (toggle T) 1 \<or> CSTATE ISA (toggle T) 1"
      apply (insert i108) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SA (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 1 \<or> nextSnpRespIs RspSFwdM (toggle T) 1) \<longrightarrow> CSTATE ISAD (toggle T) 0 \<or> CSTATE ISA (toggle T) 0"
      apply (insert i107) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextSnpRespIs RspIFwdM (toggle T) 0 \<or> nextSnpRespIs RspIHitSE (toggle T) 0) \<longrightarrow> CSTATE Invalid (toggle T) 0 \<or> CSTATE ISDI (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0 \<or> CSTATE IIA (toggle T) 0"
      apply (insert i110) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextSnpRespIs RspIFwdM (toggle T) 1 \<or> nextSnpRespIs RspIHitSE (toggle T) 1) \<longrightarrow> CSTATE Invalid (toggle T) 1 \<or> CSTATE ISDI (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1 \<or> CSTATE IIA (toggle T) 1"
      apply (insert i109) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 0 \<longrightarrow> CSTATE MIA (toggle T) 0 \<or> CSTATE SIA (toggle T) 0 \<or> CSTATE IIA (toggle T) 0"
      apply (insert i112) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 1 \<longrightarrow> CSTATE MIA (toggle T) 1 \<or> CSTATE SIA (toggle T) 1 \<or> CSTATE IIA (toggle T) 1"
      apply (insert i111) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps1 (toggle T) \<noteq> [] \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i114) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps2 (toggle T) \<noteq> [] \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i113) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (snpresps1 (toggle T)) \<le> 1"
      apply (insert i116) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (snpresps2 (toggle T)) \<le> 1"
      apply (insert i115) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 0 \<or> nextSnpRespIs RspSFwdM (toggle T) 0) \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i118) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 1 \<or> nextSnpRespIs RspSFwdM (toggle T) 1) \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i117) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 0 \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> dthdatas1 (toggle T) \<noteq> [] \<and> htddatas2 (toggle T) = []"
      apply (insert i120) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 1 \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> dthdatas2 (toggle T) \<noteq> [] \<and> htddatas1 (toggle T) = []"
      apply (insert i119) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = []"
      apply (insert i122) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = []"
      apply (insert i121) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i124) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i123) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> reqs1 (toggle T) \<noteq> [] \<longrightarrow> dthdatas1 (toggle T) \<noteq> []"
      apply (insert i126) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> reqs2 (toggle T) \<noteq> [] \<longrightarrow> dthdatas2 (toggle T) \<noteq> []"
      apply (insert i125) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> dthdatas1 (toggle T) \<noteq> [] \<longrightarrow> CSTATE Invalid (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0"
      apply (insert i128) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> dthdatas2 (toggle T) \<noteq> [] \<longrightarrow> CSTATE Invalid (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1"
      apply (insert i127) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> dthdatas1 (toggle T) \<noteq> [] \<longrightarrow> \<not>CSTATE MIA (toggle T) 1"
      apply (insert i130) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> dthdatas2 (toggle T) \<noteq> [] \<longrightarrow> \<not>CSTATE MIA (toggle T) 0"
      apply (insert i129) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "dthdatas1 (toggle T) \<noteq> [] \<and> HSTATE SD (toggle T) \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i132) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "dthdatas2 (toggle T) \<noteq> [] \<and> HSTATE SD (toggle T) \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i131) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> nextLoad (toggle T) 0"
      apply (insert i134) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> nextLoad (toggle T) 1"
      apply (insert i133) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i135) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE SD (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i137) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE SD (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i136) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<longrightarrow> nextLoad (toggle T) 0"
      apply (insert i139) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<longrightarrow> nextLoad (toggle T) 1"
      apply (insert i138) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i141) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i140) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i143) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i142) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 0 \<or> CSTATE ISDI (toggle T) 0) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1"
      apply (insert i145) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 1 \<or> CSTATE ISDI (toggle T) 1) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0"
      apply (insert i144) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 0 \<or> CSTATE ISDI (toggle T) 0) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas1 (toggle T) \<noteq> []"
      apply (insert i147) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 1 \<or> CSTATE ISDI (toggle T) 1) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas2 (toggle T) \<noteq> []"
      apply (insert i146) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> snpresps2 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i148) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i150) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i149) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i152) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i151) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i154) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i153) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i156) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i155) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i158) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i157) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdShared (toggle T) 0 \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i160) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdShared (toggle T) 1 \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i159) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1"
      apply (insert i162) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0"
      apply (insert i161) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> HSTATE SharedM (toggle T) \<longrightarrow> reqs2 (toggle T) = [] \<or> nextReqIs CleanEvict (toggle T) 1 \<or> nextReqIs CleanEvictNoData (toggle T) 1 \<or> nextReqIs RdOwn (toggle T) 1"
      apply (insert i164) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> HSTATE SharedM (toggle T) \<longrightarrow> reqs1 (toggle T) = [] \<or> nextReqIs CleanEvict (toggle T) 0 \<or> nextReqIs CleanEvictNoData (toggle T) 0 \<or> nextReqIs RdOwn (toggle T) 0"
      apply (insert i163) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> HSTATE IB (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE MB (toggle T)"
      apply (insert i166) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> HSTATE IB (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE MB (toggle T)"
      apply (insert i165) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 0 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE InvalidM (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE ID (toggle T)"
      apply (insert i168) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 1 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE InvalidM (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE ID (toggle T)"
      apply (insert i167) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i170) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i169) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> HSTATE SharedM (toggle T) \<longrightarrow> CSTATE Shared (toggle T) 1 \<or> CSTATE SIA (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE ISA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> CSTATE ISD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE SIAC (toggle T) 1"
      apply (insert i172) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> HSTATE SharedM (toggle T) \<longrightarrow> CSTATE Shared (toggle T) 0 \<or> CSTATE SIA (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE ISA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> CSTATE ISD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE SIAC (toggle T) 0"
      apply (insert i171) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> dthdatas1 (toggle T) = [] \<and> dthdatas2 (toggle T) = []"
      apply (insert i173) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<longrightarrow> \<not>CSTATE MIA (toggle T) 0"
      apply (insert i175) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<longrightarrow> \<not>CSTATE MIA (toggle T) 1"
      apply (insert i174) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> dthdatas2 (toggle T) = [] \<and> dthdatas1 (toggle T) = []"
      apply (insert i176) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<longrightarrow> dthdatas2 (toggle T) = [] \<and> dthdatas1 (toggle T) = []"
      apply (insert i177) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i179) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i178) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i181) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i180) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SA (toggle T) \<longrightarrow> dthdatas2 (toggle T) = [] \<and> dthdatas1 (toggle T) = []"
      apply (insert i182) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<longrightarrow> \<not> CSTATE IIA (toggle T) 0 \<or> \<not> CSTATE IIA (toggle T) 1"
      apply (insert i183) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<longrightarrow> (\<not> CSTATE IIA (toggle T) 0 \<or> nextSnpRespIs RspIFwdM (toggle T) 0) \<and> (\<not> CSTATE IIA (toggle T) 1 \<or> nextSnpRespIs RspIFwdM (toggle T) 1)"
      apply (insert i184) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i186) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i185) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<longrightarrow> \<not> CSTATE IIA (toggle T) 1"
      apply (insert i188) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<longrightarrow> \<not> CSTATE IIA (toggle T) 0"
      apply (insert i187) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i190) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i189) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps1 (toggle T) \<noteq> [] \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i192) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps2 (toggle T) \<noteq> [] \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i191) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdShared (toggle T) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i194) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs RdShared (toggle T) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i193) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i196) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i195) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 0 \<or> nextSnpRespIs RspSFwdM (toggle T) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i198) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> (nextSnpRespIs RspIFwdM (toggle T) 1 \<or> nextSnpRespIs RspSFwdM (toggle T) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i197) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i199) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict (toggle T)"
      apply (insert i200) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i201) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i203) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i202) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i204) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> HSTATE IB (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE MB (toggle T)"
      apply (insert i206) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> HSTATE IB (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE MB (toggle T)"
      apply (insert i205) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) (toggle T)"
      apply (insert i207) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i209) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i208) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict (toggle T)"
      apply (insert i210) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) (toggle T)"
      apply (insert i211) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i212) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 0 \<longrightarrow> HSTATE InvalidM (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE IB (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE ID (toggle T)"
      apply (insert i214) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 1 \<longrightarrow> HSTATE InvalidM (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE SB (toggle T) \<or> HSTATE IB (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE ID (toggle T)"
      apply (insert i213) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) (toggle T)"
      apply (insert i215) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i229) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE SA (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i218) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE SA (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i217) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1)"
      apply (insert i220) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0)"
      apply (insert i219) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_not_C_msg Modified IMAD nextGOPending (toggle T)"
      apply (insert i221) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE MD (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i230) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<longrightarrow> nextStore (toggle T) 0"
      apply (insert i224) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<longrightarrow> nextStore (toggle T) 1"
      apply (insert i223) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i226) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i225) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps1 (toggle T) \<noteq> [] \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i192) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps2 (toggle T) \<noteq> [] \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i191) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i216) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE MD (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i222) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE MD (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i232) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE MD (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i231) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<longrightarrow> nextStore (toggle T) 0"
      apply (insert i234) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<longrightarrow> nextStore (toggle T) 1"
      apply (insert i233) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same IMA (nextGOPending) nextStore (toggle T)"
      apply (insert i235) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0 \<or> CSTATE ISA (toggle T) 0 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i237) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1 \<or> CSTATE ISA (toggle T) 1 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i236) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i238) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i239) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) (toggle T)"
      apply (insert i240) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i242) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i241) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0 \<or> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextGOPending (toggle T) 0) \<longrightarrow> ((\<not> CSTATE ISD (toggle T) 1) \<and> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1 \<and> \<not>( (CSTATE ISAD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextGOPending (toggle T) 1) \<and> \<not>CSTATE ISA (toggle T) 1 \<and> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> \<not> ( nextHTDDataPending (toggle T) 1) \<and> \<not> CSTATE Shared (toggle T) 1 \<and> \<not> CSTATE Modified (toggle T) 1) \<or> nextSnoopIs SnpInv (toggle T) 1"
      apply (insert i244) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1 \<or> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextGOPending (toggle T) 1) \<longrightarrow> ((\<not> CSTATE ISD (toggle T) 0) \<and> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0 \<and> \<not>( (CSTATE ISAD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextGOPending (toggle T) 0) \<and> \<not>CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> \<not> ( nextHTDDataPending (toggle T) 0) \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 0) \<or> nextSnoopIs SnpInv (toggle T) 0"
      apply (insert i243) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0 \<or> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0) \<longrightarrow> dthdatas1 (toggle T) = [] \<and> (dthdatas2 (toggle T) = [] \<or> HSTATE MB (toggle T) \<or> HSTATE ModifiedM (toggle T))"
      apply (insert i246) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1 \<or> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1) \<longrightarrow> dthdatas2 (toggle T) = [] \<and> (dthdatas1 (toggle T) = [] \<or> HSTATE MB (toggle T) \<or> HSTATE ModifiedM (toggle T))"
      apply (insert i245) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0 \<or> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextGOPending (toggle T) 0) \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i248) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1 \<or> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextGOPending (toggle T) 1) \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i247) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_same SMA (nextGOPending) nextStore (toggle T)"
      apply (insert i249) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0) \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i251) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1) \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T)"
      apply (insert i250) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<or> CSTATE ISA (toggle T) 0 \<or> CSTATE ISDI (toggle T) 0 \<longrightarrow> nextLoad (toggle T) 0"
      apply (insert i253) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<or> CSTATE ISA (toggle T) 1 \<or> CSTATE ISDI (toggle T) 1 \<longrightarrow> nextLoad (toggle T) 1"
      apply (insert i252) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SMA (toggle T) 0 \<longrightarrow> nextStore (toggle T) 0"
      apply (insert i255) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SMA (toggle T) 1 \<longrightarrow> nextStore (toggle T) 1"
      apply (insert i254) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0) \<or> CSTATE ISA (toggle T) 0 \<or> ( nextHTDDataPending (toggle T) 0) \<or> CSTATE Shared (toggle T) 0 \<longrightarrow> \<not> CSTATE Modified (toggle T) 1 \<and> (dthdatas1 (toggle T) = [] \<or> nextSnpRespIs RspSFwdM (toggle T) 0 \<or> HSTATE SD (toggle T))"
      apply (insert i257) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1) \<or> CSTATE ISA (toggle T) 1 \<or> ( nextHTDDataPending (toggle T) 1) \<or> CSTATE Shared (toggle T) 1 \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> (dthdatas2 (toggle T) = [] \<or> nextSnpRespIs RspSFwdM (toggle T) 1 \<or> HSTATE SD (toggle T))"
      apply (insert i256) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i259) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE SharedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i258) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MD (toggle T)\<or> HSTATE ID (toggle T) \<or> HSTATE InvalidM (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i261) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> HSTATE ModifiedM (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE MA (toggle T) \<or> HSTATE MD (toggle T)\<or> HSTATE ID (toggle T) \<or> HSTATE InvalidM (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE SB (toggle T)"
      apply (insert i260) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i263) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = [] \<and> snps2 (toggle T) = []"
      apply (insert i262) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 0 \<longrightarrow> \<not>nextReqIs RdOwn (toggle T) 1 \<or> \<not>HSTATE ModifiedM (toggle T)"
      apply (insert i265) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISDI (toggle T) 1 \<longrightarrow> \<not>nextReqIs RdOwn (toggle T) 0 \<or> \<not>HSTATE ModifiedM (toggle T)"
      apply (insert i264) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 0 \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i267) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 1 \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i266) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i269) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i268) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i271) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i270) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i273) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i272) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> reqresps1 (toggle T) = [] \<and> htddatas1 (toggle T) = [] \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i275) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> reqresps2 (toggle T) = [] \<and> htddatas2 (toggle T) = [] \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i274) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE SMAD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0"
      apply (insert i277) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE SMAD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1"
      apply (insert i276) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<and> CXL_SPG_used (toggle T) 0 \<longrightarrow> nextReqIs RdOwn (toggle T) 0"
      apply (insert i279) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<and> CXL_SPG_used (toggle T) 1 \<longrightarrow> nextReqIs RdOwn (toggle T) 1"
      apply (insert i278) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i281) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i280) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i283) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i282) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> snpresps1 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i284) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> CSTATE IMD (toggle T) 1"
      apply (insert i286) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> CSTATE IMD (toggle T) 0"
      apply (insert i285) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextReqIs CleanEvict (toggle T) 0 \<and> \<not> nextReqIs CleanEvictNoData (toggle T) 0"
      apply (insert i288) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextReqIs CleanEvict (toggle T) 1 \<and> \<not> nextReqIs CleanEvictNoData (toggle T) 1"
      apply (insert i287) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i289) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i291) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i290) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i293) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i292) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextReqIs CleanEvict (toggle T) 0 \<and> \<not> nextReqIs CleanEvictNoData (toggle T) 0"
      apply (insert i295) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextReqIs CleanEvict (toggle T) 1 \<and> \<not> nextReqIs CleanEvictNoData (toggle T) 1"
      apply (insert i294) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> reqs2 (toggle T) = []"
      apply (insert i297) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 1 \<and> reqs1 (toggle T) = []"
      apply (insert i296) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i299) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i298) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(HSTATE SAD (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SA (toggle T) \<or> HSTATE MA (toggle T)) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> htddatas1 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 0"
      apply (insert i301) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(HSTATE SAD (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SA (toggle T) \<or> HSTATE MA (toggle T)) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> htddatas2 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 1"
      apply (insert i300) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspSFwdM (toggle T) 0 \<longrightarrow> CSTATE Shared (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SIA (toggle T) 0 \<or> CSTATE SIAC (toggle T) 0"
      apply (insert i303) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspSFwdM (toggle T) 1 \<longrightarrow> CSTATE Shared (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SIA (toggle T) 1 \<or> CSTATE SIAC (toggle T) 1"
      apply (insert i302) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 0 \<or> CSTATE ISDI (toggle T) 0 \<or> nextReqIs RdOwn (toggle T) 0) \<and> HSTATE MA (toggle T) \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1)"
      apply (insert i305) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Invalid (toggle T) 1 \<or> CSTATE ISDI (toggle T) 1 \<or> nextReqIs RdOwn (toggle T) 1) \<and> HSTATE MA (toggle T) \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0)"
      apply (insert i304) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i307) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i306) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i309) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i308) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i311) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i310) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i313) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i312) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i315) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i314) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i317) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i316) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i319) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i318) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i321) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i320) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i323) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i322) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i325) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i324) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i327) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i326) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i329) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i328) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> reqs1 (toggle T) = []"
      apply (insert i331) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> reqs2 (toggle T) = []"
      apply (insert i330) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i333) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i332) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdShared (toggle T) 0 \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i335) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdShared (toggle T) 1 \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i334) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1 \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i336) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs RdOwn (toggle T) 0 \<longrightarrow> \<not> CSTATE ISAD (toggle T) 0 \<and> \<not> CSTATE Invalid (toggle T) 0"
      apply (insert i338) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs RdOwn (toggle T) 1 \<longrightarrow> \<not> CSTATE ISAD (toggle T) 1 \<and> \<not> CSTATE Invalid (toggle T) 1"
      apply (insert i337) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i340) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i339) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i342) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i341) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i344) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i343) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i346) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i345) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<and> CXL_SPG_used (toggle T) 0 \<longrightarrow> (nextReqIs CleanEvict (toggle T) 0 \<or> nextReqIs CleanEvictNoData (toggle T) 0 )"
      apply (insert i348) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<and> CXL_SPG_used (toggle T) 1 \<longrightarrow> (nextReqIs CleanEvict (toggle T) 1 \<or> nextReqIs CleanEvictNoData (toggle T) 1 )"
      apply (insert i347) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i350) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i349) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i352) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i351) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1 \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i353) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs DirtyEvict (toggle T) 0 \<longrightarrow> (\<not> CSTATE Modified (toggle T) 0 \<or> \<not> CSTATE Modified (toggle T) 1) \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i355) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs DirtyEvict (toggle T) 1 \<longrightarrow> (\<not> CSTATE Modified (toggle T) 0 \<or> \<not> CSTATE Modified (toggle T) 1) \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i354) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i357) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i356) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0\<longrightarrow> nextHTDDataPending (toggle T) 0"
      apply (insert i359) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1\<longrightarrow> nextHTDDataPending (toggle T) 1"
      apply (insert i358) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) (toggle T)"
      apply (insert i360) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> CSTATE SIAC (toggle T) 0"
      apply (insert i362) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> CSTATE SIAC (toggle T) 1"
      apply (insert i361) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextGOPendingIs GO_WritePull (toggle T) 0 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> reqresps2 (toggle T) = [] \<or> nextReqRespStateIs Invalid (reqresps2 (toggle T))"
      apply (insert i364) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextGOPendingIs GO_WritePull (toggle T) 1 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> reqresps1 (toggle T) = [] \<or> nextReqRespStateIs Invalid (reqresps1 (toggle T))"
      apply (insert i363) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> nextEvict (toggle T) 0"
      apply (insert i366) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> nextEvict (toggle T) 1"
      apply (insert i365) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 0 \<longrightarrow> nextEvict (toggle T) 0"
      apply (insert i368) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 1 \<longrightarrow> nextEvict (toggle T) 1"
      apply (insert i367) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 0"
      apply (insert i370) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 1"
      apply (insert i369) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 0 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 0"
      apply (insert i372) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 1 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 1"
      apply (insert i371) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i374) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i373) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 0 \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i376) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> nextReqIs CleanEvict (toggle T) 1 \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i375) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = [])"
      apply (insert i378) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = [])"
      apply (insert i377) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 0 \<longrightarrow> nextEvict (toggle T) 0"
      apply (insert i380) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 1 \<longrightarrow> nextEvict (toggle T) 1"
      apply (insert i379) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 0 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i382) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 1 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i381) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 0 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISDI (toggle T) 1"
      apply (insert i384) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 1 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISDI (toggle T) 0"
      apply (insert i383) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 0 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> (reqresps2 (toggle T) = [] \<or> nextReqRespStateIs Invalid (reqresps2 (toggle T)))"
      apply (insert i386) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs DirtyEvict (toggle T) 1 \<and> HSTATE InvalidM (toggle T) \<longrightarrow> (reqresps1 (toggle T) = [] \<or> nextReqRespStateIs Invalid (reqresps1 (toggle T)))"
      apply (insert i385) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not>(CSTATE ISA (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1)"
      apply (insert i388) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not>(CSTATE ISA (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0)"
      apply (insert i387) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T) \<and> CSTATE IMAD (toggle T) 1"
      apply (insert i390) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T) \<and> CSTATE IMAD (toggle T) 0"
      apply (insert i389) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T) \<and> CSTATE ISAD (toggle T) 1"
      apply (insert i392) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T) \<and> CSTATE ISAD (toggle T) 0"
      apply (insert i391) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = []"
      apply (insert i394) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = []"
      apply (insert i393) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i396) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i395) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 0 \<or> nextReqIs CleanEvict (toggle T) 0) \<longrightarrow> (CSTATE SIA (toggle T) 0 \<or> CSTATE IIA (toggle T) 0 \<or> CSTATE SIAC (toggle T) 0)"
      apply (insert i398) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 1 \<or> nextReqIs CleanEvict (toggle T) 1) \<longrightarrow> (CSTATE SIA (toggle T) 1 \<or> CSTATE IIA (toggle T) 1 \<or> CSTATE SIAC (toggle T) 1)"
      apply (insert i397) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE Shared (toggle T) 0 \<or> CSTATE Shared (toggle T) 1) \<longrightarrow> \<not> HSTATE MD (toggle T)"
      apply (insert i399) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 0 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i401) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Shared (toggle T) 1 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i400) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 0 \<or> nextReqIs CleanEvict (toggle T) 0) \<longrightarrow> nextEvict (toggle T) 0"
      apply (insert i403) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 1 \<or> nextReqIs CleanEvict (toggle T) 1) \<longrightarrow> nextEvict (toggle T) 1"
      apply (insert i402) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 0 \<or> nextReqIs CleanEvict (toggle T) 0) \<longrightarrow> \<not> CSTATE ISDI (toggle T) 0"
      apply (insert i405) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 1 \<or> nextReqIs CleanEvict (toggle T) 1) \<longrightarrow> \<not> CSTATE ISDI (toggle T) 1"
      apply (insert i404) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 0 \<or> nextReqIs CleanEvict (toggle T) 0) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i407) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(nextReqIs CleanEvictNoData (toggle T) 1 \<or> nextReqIs CleanEvict (toggle T) 1) \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i406) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> HSTATE InvalidM (toggle T) \<and> nextReqIs RdShared (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i409) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> HSTATE InvalidM (toggle T) \<and> nextReqIs RdShared (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i408) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0 \<and> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i410) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0)) \<and> \<not> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i411) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextGOPendingIs GO_WritePull (toggle T) 0 \<or> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> HSTATE InvalidM (toggle T)"
      apply (insert i412) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i414) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i413) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i416) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i415) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0) \<longrightarrow> (HSTATE MA (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MB (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T))"
      apply (insert i418) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1) \<longrightarrow> (HSTATE MA (toggle T) \<or> HSTATE ModifiedM (toggle T) \<or> HSTATE MB (toggle T) \<or> HSTATE MAD (toggle T) \<or> HSTATE SAD (toggle T))"
      apply (insert i417) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i420) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i419) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i422) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MAD (toggle T)"
      apply (insert i421) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i424) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i423) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(HSTATE InvalidM (toggle T) \<or> HSTATE SharedM (toggle T) \<or> HSTATE ModifiedM (toggle T)) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull (toggle T) 0) \<and> (\<not> nextGOPendingIs GO_WritePull (toggle T) 1)"
      apply (insert i425) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 0 \<and> CSTATE IIA (toggle T) 1 \<longrightarrow> HSTATE InvalidM (toggle T) \<or> HSTATE IB (toggle T)"
      apply (insert i427) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 1 \<and> CSTATE IIA (toggle T) 0 \<longrightarrow> HSTATE InvalidM (toggle T) \<or> HSTATE IB (toggle T)"
      apply (insert i426) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> dthdatas1 (toggle T) = [] \<and> dthdatas2 (toggle T) = []"
      apply (insert i428) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (toggle T) 0"
      apply (insert i430) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (toggle T) 1"
      apply (insert i429) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i432) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i431) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = []"
      apply (insert i434) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> [] \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = []"
      apply (insert i433) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i436) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i435) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i438) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i437) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE ISD (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 0"
      apply (insert i440) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE ISD (toggle T) 1 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i439) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE SMD (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0"
      apply (insert i442) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE SMD (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1"
      apply (insert i441) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE IMA (toggle T) 0"
      apply (insert i444) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE IMA (toggle T) 1"
      apply (insert i443) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i448) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i449) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i450) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i445) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i446) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<or> HSTATE ID (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i447) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = [])"
      apply (insert i452) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = [])"
      apply (insert i451) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = [])"
      apply (insert i454) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = [])"
      apply (insert i453) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> htddatas2 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> htddatas2 (toggle T) = [])"
      apply (insert i456) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> htddatas1 (toggle T) \<noteq> []) \<or> ((CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> htddatas1 (toggle T) = [])"
      apply (insert i455) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i458) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i457) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i460) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i459) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i462) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i461) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i464) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i463) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i466) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i465) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i468) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i467) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<or> CSTATE ISA (toggle T) 0 \<longrightarrow> \<not> HSTATE MD (toggle T)"
      apply (insert i470) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<or> CSTATE ISA (toggle T) 1 \<longrightarrow> \<not> HSTATE MD (toggle T)"
      apply (insert i469) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> (nextHTDDataPending (toggle T) 0 \<or> nextGOPending (toggle T) 0) \<longrightarrow> \<not> HSTATE MD (toggle T)"
      apply (insert i472) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> (nextHTDDataPending (toggle T) 1 \<or> nextGOPending (toggle T) 1) \<longrightarrow> \<not> HSTATE MD (toggle T)"
      apply (insert i471) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i474) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i473) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 0 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i476) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 1 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i475) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i478) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i477) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> CSTATE ISA (toggle T) 1 \<and> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i480) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i479) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i482) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> CSTATE Shared (toggle T) 0"
      apply (insert i481) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i281) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISD (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i280) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i486) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISA (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i485) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i488) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i487) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i490) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> HSTATE MA (toggle T)"
      apply (insert i489) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0"
      apply (insert i492) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1"
      apply (insert i491) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i494) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i493) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i496) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i495) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i498) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i497) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i499) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i500) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISD (toggle T) 0 \<and> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i502) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISD (toggle T) 1 \<and> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i501) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i504) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i503) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i506) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i505) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i508) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i507) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0"
      apply (insert i510) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 1 \<and> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1"
      apply (insert i509) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i512) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i511) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE Shared (toggle T) 0"
      apply (insert i514) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i513) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0"
      apply (insert i516) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i515) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> snpresps2 (toggle T) = [] \<and> reqresps1 (toggle T) = [] \<and> snps2 (toggle T) = []"
      apply (insert i518) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> snpresps1 (toggle T) = [] \<and> reqresps2 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i517) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> snpresps2 (toggle T) = [] \<and> snps2 (toggle T) = []"
      apply (insert i520) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> snpresps1 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i519) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i522) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i521) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i524) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i523) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> CSTATE ISAD (toggle T) 1"
      apply (insert i526) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> CSTATE ISAD (toggle T) 0"
      apply (insert i525) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i528) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i527) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i530) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i529) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i532) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i531) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1 \<and> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i533) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i535) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i534) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i536) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> length (dthdatas1 (toggle T)) \<le> 1 \<and> length (dthdatas2 (toggle T)) \<le> 1"
      apply (insert i537) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> length (dthdatas1 (toggle T)) \<le> 1 \<and> length (dthdatas2 (toggle T)) \<le> 1"
      apply (insert i538) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE IIA (toggle T) 1"
      apply (insert i540) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE IIA (toggle T) 0"
      apply (insert i539) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> length (dthdatas1 (toggle T)) \<le> 1 \<and> length (dthdatas2 (toggle T)) \<le> 1"
      apply (insert i541) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i543) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i542) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i545) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i544) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i547) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i546) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> snps2 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i548) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> snps2 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i549) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> snps2 (toggle T) = [] \<and> snps1 (toggle T) = []"
      apply (insert i550) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i552) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i551) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i554) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i553) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i556) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i555) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i558) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i557) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i560) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE IMD (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i559) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> lastSharer (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i562) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> lastSharer (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i561) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> lastSharer (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i564) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<and> lastSharer (toggle T) \<and> nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i563) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i566) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i565) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i568) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i567) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i570) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> HSTATE MA (toggle T) \<longrightarrow> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i569) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 0 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 0) \<and> (\<not> CSTATE SIA (toggle T) 1 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 1)"
      apply (insert i571) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA (toggle T) 0 \<and> \<not> CSTATE SIA (toggle T) 1"
      apply (insert i573) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA (toggle T) 0 \<and> \<not> CSTATE SIA (toggle T) 1"
      apply (insert i572) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> \<not> CSTATE SIA (toggle T) 0 \<and> \<not> CSTATE SIA (toggle T) 1"
      apply (insert i574) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i576) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i575) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i578) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<longrightarrow> \<not> (CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i577) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i580) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i579) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i581) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i582) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i584) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i583) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE SMA (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i586) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE SMA (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i585) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE IMD (toggle T) 1"
      apply (insert i588) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE IMD (toggle T) 0"
      apply (insert i587) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 1 \<and> (nextGOPending (toggle T) 1 \<or> nextHTDDataPending (toggle T) 1))"
      apply (insert i590) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> (CSTATE IMAD (toggle T) 0 \<and> (nextGOPending (toggle T) 0 \<or> nextHTDDataPending (toggle T) 0))"
      apply (insert i589) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i592) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i591) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i594) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i593) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i596) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i595) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISD (toggle T) 0"
      apply (insert i598) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 1 \<and> \<not> CSTATE ISD (toggle T) 1"
      apply (insert i597) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE SMA (toggle T) 0 \<and> \<not> CSTATE SMD (toggle T) 0"
      apply (insert i600) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE SMA (toggle T) 1 \<and> \<not> CSTATE SMD (toggle T) 1"
      apply (insert i599) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE IMD (toggle T) 0"
      apply (insert i602) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE IMD (toggle T) 1"
      apply (insert i601) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i603) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0 \<and> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i604) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i606) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0"
      apply (insert i605) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i608) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i607) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i610) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i609) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdShared (toggle T) 0 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 1"
      apply (insert i612) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<and> nextReqIs RdShared (toggle T) 1 \<longrightarrow> \<not> CSTATE ISDI (toggle T) 0"
      apply (insert i611) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i613) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i615) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i614) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i616) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps1 (toggle T) \<noteq> [] \<and> HSTATE MAD (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i618) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "snpresps2 (toggle T) \<noteq> [] \<and> HSTATE MAD (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i617) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> HSTATE MD (toggle T) \<longrightarrow> snpresps1 (toggle T) = [] \<and> snps1 (toggle T) = [] \<and> reqresps2 (toggle T) = []"
      apply (insert i620) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> HSTATE MD (toggle T) \<longrightarrow> snpresps2 (toggle T) = [] \<and> snps2 (toggle T) = [] \<and> reqresps1 (toggle T) = []"
      apply (insert i619) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 0 (toggle T) \<and> HSTATE MD (toggle T) \<and> nextReqIs RdOwn (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 0"
      apply (insert i622) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextDTHDataFrom 1 (toggle T) \<and> HSTATE MD (toggle T) \<and> nextReqIs RdOwn (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 1"
      apply (insert i621) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextSnpRespIs RspSFwdM (toggle T) 0 \<longrightarrow> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i624) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextSnpRespIs RspSFwdM (toggle T) 1 \<longrightarrow> \<not> CSTATE Modified (toggle T) 0"
      apply (insert i623) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE Modified (toggle T) 1 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i626) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE Modified (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 0"
      apply (insert i625) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i547) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i546) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SA (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i629) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SharedM (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i630) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 0 \<and> HSTATE SA (toggle T) \<longrightarrow> CSTATE ISAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE ISA (toggle T) 1"
      apply (insert i632) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IIA (toggle T) 1 \<and> HSTATE SA (toggle T) \<longrightarrow> CSTATE ISAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE ISA (toggle T) 0"
      apply (insert i631) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> htddatas1 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 0"
      apply (insert i634) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> htddatas2 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 1"
      apply (insert i633) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> \<not> CSTATE ISD (toggle T) 0 \<and> \<not> CSTATE ISD (toggle T) 1"
      apply (insert i635) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> CSTATE Invalid (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<or> CSTATE IMAD (toggle T) 0"
      apply (insert i637) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> CSTATE Invalid (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<or> CSTATE IMAD (toggle T) 1"
      apply (insert i636) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i638) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> snpresps1 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i639) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i641) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i640) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> \<not> CSTATE SIA (toggle T) 0 \<and> \<not> CSTATE SIA (toggle T) 1"
      apply (insert i642) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextReqIs RdOwn (toggle T) 1"
      apply (insert i644) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextReqIs RdOwn (toggle T) 0"
      apply (insert i643) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MB (toggle T) \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE ISA (toggle T) 1"
      apply (insert i645) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE IIA (toggle T) 1"
      apply (insert i647) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<and> HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE IIA (toggle T) 0"
      apply (insert i646) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i649) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i648) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i651) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i650) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i653) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i652) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i655) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i654) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> \<not> nextReqIs RdOwn (toggle T) 0"
      apply (insert i657) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> \<not> nextReqIs RdOwn (toggle T) 1"
      apply (insert i656) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE ISD (toggle T) 1"
      apply (insert i659) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE ISD (toggle T) 0"
      apply (insert i658) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i661) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i660) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i663) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i662) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE ISA (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i665) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE ISA (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i664) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0) \<or> CSTATE ISA (toggle T) 0 \<or> ( nextHTDDataPending (toggle T) 0) \<or> CSTATE Shared (toggle T) 0 \<longrightarrow> \<not> (CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i667) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1) \<or> CSTATE ISA (toggle T) 1 \<or> ( nextHTDDataPending (toggle T) 1) \<or> CSTATE Shared (toggle T) 1 \<longrightarrow> \<not> (CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i666) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> snps2 (toggle T) = []"
      apply (insert i669) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> snps1 (toggle T) = []"
      apply (insert i668) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i671) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i670) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE SIA (toggle T) 0 \<and> \<not> CSTATE SIA (toggle T) 1"
      apply (insert i673) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE SIA (toggle T) 1 \<and> \<not> CSTATE SIA (toggle T) 0"
      apply (insert i672) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> (htddatas2 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 1)"
      apply (insert i675) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> (htddatas1 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 0)"
      apply (insert i674) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i677) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i676) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> snpresps1 (toggle T) = []"
      apply (insert i679) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> snpresps2 (toggle T) = []"
      apply (insert i678) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1)"
      apply (insert i681) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> (CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0)"
      apply (insert i680) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE ISA (toggle T) 1 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i683) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE ISA (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 0"
      apply (insert i682) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i685) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i684) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1"
      apply (insert i687) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0"
      apply (insert i686) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 0 \<longrightarrow> snps1 (toggle T) = []"
      apply (insert i689) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Invalid (toggle T) 1 \<longrightarrow> snps2 (toggle T) = []"
      apply (insert i688) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> CSTATE ISD (toggle T) 1 \<or> CSTATE ISAD (toggle T) 1 \<and> nextGOPending (toggle T) 1"
      apply (insert i691) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> CSTATE ISD (toggle T) 0 \<or> CSTATE ISAD (toggle T) 0 \<and> nextGOPending (toggle T) 0"
      apply (insert i690) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> \<not> nextGOPendingIs GO_WritePull (toggle T) 1"
      apply (insert i692) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i796) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T) \<and> CSTATE ISAD (toggle T) 1"
      apply (insert i695) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T) \<and> CSTATE ISAD (toggle T) 0"
      apply (insert i694) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i697) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i696) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = []"
      apply (insert i699) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = []"
      apply (insert i698) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> HSTATE IB (toggle T) \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i701) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<and> HSTATE IB (toggle T) \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i700) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i703) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<and> HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0"
      apply (insert i702) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs DirtyEvict (toggle T) 0 \<longrightarrow> CSTATE IIA (toggle T) 0"
      apply (insert i705) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<and> nextReqIs DirtyEvict (toggle T) 1 \<longrightarrow> CSTATE IIA (toggle T) 1"
      apply (insert i704) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 0 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 0) \<and> (\<not> CSTATE SIA (toggle T) 1 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 1)"
      apply (insert i706) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 0 \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1)"
      apply (insert i708) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 1 \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0)"
      apply (insert i707) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (dthdatas1 (toggle T)) \<le> 1"
      apply (insert i104) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "length (dthdatas2 (toggle T)) \<le> 1"
      apply (insert i103) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> CSTATE IIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i712) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<and> CSTATE IIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i711) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i714) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i713) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps1 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i716) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> snpresps2 (toggle T) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared (toggle T) 0 \<and> \<not> CSTATE Shared (toggle T) 1"
      apply (insert i715) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> HSTATE MD (toggle T) \<longrightarrow> snpresps1 (toggle T) = [] \<and> snps1 (toggle T) = [] \<and> reqresps2 (toggle T) = []"
      apply (insert i718) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> HSTATE MD (toggle T) \<longrightarrow> snpresps2 (toggle T) = [] \<and> snps2 (toggle T) = [] \<and> reqresps1 (toggle T) = []"
      apply (insert i717) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> (htddatas2 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 1)"
      apply (insert i720) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> (htddatas1 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 0)"
      apply (insert i719) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1 \<and> (htddatas2 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 1)"
      apply (insert i722) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0 \<and> (htddatas1 (toggle T) = [] \<or> CSTATE ISDI (toggle T) 0)"
      apply (insert i721) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> dthdatas1 (toggle T) = []"
      apply (insert i724) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> dthdatas2 (toggle T) = []"
      apply (insert i723) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIHitSE (toggle T) 0 \<longrightarrow> \<not> CSTATE IMA (toggle T) 0 \<and> \<not> CSTATE SMA (toggle T) 0"
      apply (insert i726) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIHitSE (toggle T) 1 \<longrightarrow> \<not> CSTATE IMA (toggle T) 1 \<and> \<not> CSTATE SMA (toggle T) 1"
      apply (insert i725) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i728) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i727) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i730) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i729) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i732) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i731) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i734) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i733) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i736) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE IMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i735) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i738) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i737) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1"
      apply (insert i740) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i739) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE InvalidM (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1 \<and> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i741) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE IB (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1 \<and> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i742) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<longrightarrow> \<not> CSTATE SMAD (toggle T) 1 \<and> \<not> CSTATE SMAD (toggle T) 0"
      apply (insert i743) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIHitSE (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i745) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIHitSE (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i744) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 0 \<longrightarrow> htddatas2 (toggle T) = []"
      apply (insert i747) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE Modified (toggle T) 1 \<longrightarrow> htddatas1 (toggle T) = []"
      apply (insert i746) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ModifiedM (toggle T) \<longrightarrow> snps1 (toggle T) = [] \<and> snps2 (toggle T) = []"
      apply (insert i748) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> nextHTDDataPending (toggle T) 0 \<and> nextSnoopIs SnpInv (toggle T) 0 \<longrightarrow> CSTATE IMAD (toggle T) 1 \<and> htddatas2 (toggle T) = []"
      apply (insert i750) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> nextHTDDataPending (toggle T) 1 \<and> nextSnoopIs SnpInv (toggle T) 1 \<longrightarrow> CSTATE IMAD (toggle T) 0 \<and> htddatas1 (toggle T) = []"
      apply (insert i749) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 1 \<and> HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 0"
      apply (insert i752) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMAD (toggle T) 0 \<and> HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (toggle T) 1"
      apply (insert i751) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIAC (toggle T) 0 \<and> HSTATE SA (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 1"
      apply (insert i754) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIAC (toggle T) 1 \<and> HSTATE SA (toggle T) \<longrightarrow> \<not> CSTATE Modified (toggle T) 0"
      apply (insert i753) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIAC (toggle T) 0 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i756) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SIAC (toggle T) 1 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i755) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) --> snps2 (toggle T) = [] \<and> snpresps2 (toggle T) = [] \<and> htddatas1 (toggle T) = []"
      apply (insert i758) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) --> snps1 (toggle T) = [] \<and> snpresps1 (toggle T) = [] \<and> htddatas2 (toggle T) = []"
      apply (insert i757) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1"
      apply (insert i760) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0"
      apply (insert i759) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas1 (toggle T) \<noteq> []"
      apply (insert i762) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas2 (toggle T) \<noteq> []"
      apply (insert i761) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) \<and> HSTATE MA (toggle T) \<longrightarrow>(CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1"
      apply (insert i764) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) \<and> HSTATE MA (toggle T) \<longrightarrow>(CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0"
      apply (insert i763) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) --> snps1 (toggle T) = []"
      apply (insert i766) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) --> snps2 (toggle T) = []"
      apply (insert i765) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0) --> reqs1 (toggle T) = []"
      apply (insert i768) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1) --> reqs2 (toggle T) = []"
      apply (insert i767) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 0 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 0"
      apply (insert i770) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE MA (toggle T) \<and> nextSnpRespIs RspIFwdM (toggle T) 1 \<longrightarrow> \<not> nextHTDDataPending (toggle T) 1"
      apply (insert i769) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SB (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i771) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs CleanEvictNoData (toggle T) 0 \<longrightarrow> CSTATE SIAC (toggle T) 0"
      apply (insert i773) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextReqIs CleanEvictNoData (toggle T) 1 \<longrightarrow> CSTATE SIAC (toggle T) 1"
      apply (insert i772) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIHitSE (toggle T) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 (toggle T)"
      apply (insert i775) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIHitSE (toggle T) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 (toggle T)"
      apply (insert i774) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIFwdM (toggle T) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData (toggle T) 0"
      apply (insert i777) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "nextSnpRespIs RspIFwdM (toggle T) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData (toggle T) 1"
      apply (insert i776) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 0 \<and> nextSnoopIs SnpData (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i779) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE SMA (toggle T) 1 \<and> nextSnoopIs SnpData (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<longrightarrow> HSTATE SAD (toggle T)"
      apply (insert i778) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 0) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or>(CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1"
      apply (insert i781) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePullDrop (toggle T) 1) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or>(CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0"
      apply (insert i780) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPendingIs GO (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0 \<and> \<not> CSTATE IIA (toggle T) 1 \<and> GTS (toggle T) 1) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 1 \<or> CSTATE MIA (toggle T) 1 \<or> (CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<and> nextGOPending (toggle T) 1 \<or>(CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1) \<and> nextGOPending (toggle T) 1 \<or> (CSTATE IMD (toggle T) 1 \<or> CSTATE SMD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1"
      apply (insert i783) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPendingIs GO (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1 \<and> \<not> CSTATE IIA (toggle T) 0 \<and> GTS (toggle T) 0) \<and> HSTATE ModifiedM (toggle T) \<longrightarrow> CSTATE Modified (toggle T) 0 \<or> CSTATE MIA (toggle T) 0 \<or> (CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<and> nextGOPending (toggle T) 0 \<or>(CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0) \<and> nextGOPending (toggle T) 0 \<or> (CSTATE IMD (toggle T) 0 \<or> CSTATE SMD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0"
      apply (insert i782) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPendingIs GO (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0 \<and> \<not> CSTATE IIA (toggle T) 1 \<and> GTS (toggle T) 1) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas1 (toggle T) \<noteq> []"
      apply (insert i785) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPendingIs GO (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1 \<and> \<not> CSTATE IIA (toggle T) 0 \<and> GTS (toggle T) 0) \<and> HSTATE MD (toggle T) \<longrightarrow> dthdatas2 (toggle T) \<noteq> []"
      apply (insert i784) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 0 \<and> nextGOPendingIs GO (toggle T) 0 \<and> nextGOPendingState Invalid (toggle T) 0 \<and> \<not> CSTATE IIA (toggle T) 1 \<and> GTS (toggle T) 1) \<and> HSTATE MA (toggle T) \<longrightarrow> ((CSTATE IMAD (toggle T) 1 \<or> CSTATE SMAD (toggle T) 1) \<and> nextHTDDataPending (toggle T) 1 \<or> CSTATE IMA (toggle T) 1 \<or> CSTATE SMA (toggle T) 1)"
      apply (insert i787) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "(CSTATE SIAC (toggle T) 1 \<and> nextGOPendingIs GO (toggle T) 1 \<and> nextGOPendingState Invalid (toggle T) 1 \<and> \<not> CSTATE IIA (toggle T) 0 \<and> GTS (toggle T) 0) \<and> HSTATE MA (toggle T) \<longrightarrow> ((CSTATE IMAD (toggle T) 0 \<or> CSTATE SMAD (toggle T) 0) \<and> nextHTDDataPending (toggle T) 0 \<or> CSTATE IMA (toggle T) 0 \<or> CSTATE SMA (toggle T) 0)"
      apply (insert i786) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> snps2 (toggle T) = []"
      apply (insert i789) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> snps1 (toggle T) = []"
      apply (insert i788) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> reqresps1 (toggle T) = []"
      apply (insert i791) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> reqresps2 (toggle T) = []"
      apply (insert i790) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 0 (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 1 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 1)"
      apply (insert i793) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE ID (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 0 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 0)"
      apply (insert i792) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 0 \<and> nextGOPendingIs GO_WritePull (toggle T) 0 \<and> HSTATE ID (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 1 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 1)"
      apply (insert i795) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "CSTATE MIA (toggle T) 1 \<and> nextGOPendingIs GO_WritePull (toggle T) 1 \<and> HSTATE ID (toggle T) \<longrightarrow> (\<not> CSTATE SIA (toggle T) 0 \<or> nextGOPendingIs GO_WritePullDrop (toggle T) 0)"
      apply (insert i794) apply (unfold invariant_wrappers toggle_eqs) apply blast done
    show "HSTATE SAD (toggle T) \<and> nextDTHDataFrom 1 (toggle T) \<longrightarrow> \<not> CSTATE MIA (toggle T) 0 \<and> \<not> CSTATE MIA (toggle T) 1"
      apply (insert i693) apply (unfold invariant_wrappers toggle_eqs) apply blast done
  qed
qed

lemma symmetry_iff: "SWMR_state_machine (toggle T) = SWMR_state_machine T"
  using symmetry toggle_toggle by metis

end
