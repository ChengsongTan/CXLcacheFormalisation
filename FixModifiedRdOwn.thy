theory FixModifiedRdOwn  imports BasicInvariants  Super2023 begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]




\<comment>\<open>
lemma HostModifiedRdOwn'_devcache_invariant1: shows "(CLEntry.block_state (devcache1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))) = CLEntry.block_state (devcache1 T)" 
  apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM])) = CLEntry.block_state (devcache1 (  T ))")
  apply(subgoal_tac "CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM] [ 0 +=reqresp GO Shared txid])) = CLEntry.block_state (devcache1 (  T [ 0 +=hostdata  txid] [ 5 sHost= SharedM]))")
  by simp+  
  

lemma HostModifiedRdOwn'_devcache_invariant2: shows "(CLEntry.block_state (devcache2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))) = CLEntry.block_state (devcache2 T)" 
  by simp+

lemma HostModifiedRdOwn'_CSTATE_invariant1: shows "CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = CSTATE X T 0" 
  by simp

lemma HostModifiedRdOwn'_CSTATE_invariant2: shows "CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = CSTATE X T 1" 
  by simp

  

lemma nextGOPending_HostModifiedRdOwn: "nextGOPending (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

lemma nextLoad_HostModifiedRdOwn: "nextLoad (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

lemma nextGOPending_HostModifiedRdOwn: "nextGOPending (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextGOPending T i"
apply(case_tac i)
apply simp+
done

lemma nextLoad_HostModifiedRdOwn: "nextLoad (   T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ] ) i = nextLoad T i"
apply(case_tac i)
apply simp+
done

\<close>


lemma snps1_HostsModifiedRdOwn: shows "snps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snps1 T"
  apply(case_tac "program1 T")
  by simp+

lemma reqs2_HostsModifiedRdOwn: shows "reqs2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = reqs2 T"
  apply(case_tac "program1 T")
  by simp+



lemma snpresps2_HostsModifiedRdOwn: shows "snpresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snpresps2 T"
  apply(case_tac "program1 T")
  by simp+

lemma snpresps1_HostsModifiedRdOwn: shows "snpresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = snpresps1 T"
  apply(case_tac "program1 T")
  by simp+

lemma reqresps2_HostsModifiedRdOwn: shows "reqresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = reqresps2 T"
  apply(case_tac "program1 T")
  by simp+



lemma reqresps1_HostsModifiedRdOwn: shows "reqresps1 T = [] \<Longrightarrow> length (reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
  by simp

lemma reqresps1_HostsModifiedRdOwn2: shows "reqresps1 T =  (reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]))"
  by simp

lemma dthdatas1_HostsModifiedRdOwn: shows "dthdatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = dthdatas1 T"
  apply(case_tac "program1 T")
  by simp+

lemma dthdatas2_HostsModifiedRdOwn: shows "dthdatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = dthdatas2 T"
  apply(case_tac "program1 T")
  by simp+


lemma htddatas1_HostsModifiedRdOwn: shows "htddatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = htddatas1 T"
  apply(case_tac "program1 T")
  by simp+

lemma htddatas2_HostsModifiedRdOwn: shows "htddatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = htddatas2 T"
  apply(case_tac "program1 T")
  by simp+

lemma reqresps1_HostsModifiedRdOwn_aux: shows "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 (T [0 -=reqresp ]) = []"
  apply(case_tac "reqresps1 T")
  by simp+

lemma reqresps1_HostsModifiedRdOwn_aux1: shows "reqresps1 T = reqresps1 (T [ Dev1 +=d2hd dthd] [ -=i 0])"
 apply(case_tac "program1 T")
  by simp+







lemma nextEvict_HostsModifiedRdOwn_invariant: shows"nextEvict T 0 = nextEvict (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0"
  by simp




lemma CSTATE_HostsModifiedRdOwn_otherside_invariant2: shows
" CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = CSTATE X T 1"
  by simp

lemma CSTATE_HostsModifiedRdOwn_otherside_invariant3: shows
" CSTATE X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = CSTATE X T 0"
  by simp



lemma HostsModifiedRdOwn_nextGOPendingIs_otherside: shows 
"nextGOPendingIs X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
  by simp

lemma HostsModifiedRdOwn_nextEvict_otherside: shows 
"nextEvict  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextEvict T 1"
 by simp

lemma HostsModifiedRdOwn_nextHTDDataPending_otherside: shows 
"nextDTHDataPending  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextDTHDataPending T 1" 
  by simp


lemma HostsModifiedRdOwn_nextSnpRespIs_otherside: shows 
"nextSnpRespIs X  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 = nextSnpRespIs X T 1"
  by simp



lemma HostsModifiedRdOwn_nextSnpRespIs_sameside: shows 
"nextSnpRespIs X  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 = nextSnpRespIs X T 0"
  by simp
 

lemma HostModifiedRdOwn_HSTATE: shows "HSTATE MAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) " 
 apply(case_tac "program1 T")
  by simp+

lemma nextStore_nextEvict_exclusive: shows "nextEvict T i \<Longrightarrow> \<not>nextStore T i"
  apply(induct "program1 T")
   apply simp
  apply (metis One_nat_def startsEvict.elims(2) startsStore.simps(4) zero_neq_one)
  apply(case_tac a)
  apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
  apply (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))
  by (metis nextEvict_def nextStore_def startsEvict.elims(2) startsStore.simps(4))


lemma reqlength1_minus: shows "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 (T [ 0 -=req]) = []"
  apply(cases "reqs1 T")
   apply simp+
  done


  
lemma empty_reqs_nextReqIs: shows "reqs1 T  = [] \<Longrightarrow> \<not> nextReqIs X T 0"
  by simp

lemma HostModifiedRdOwn_empty_reqs1_aux: shows " reqs1 T = reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD])"
  by simp

lemma snps2_HostModifiedRdOwn: shows "snps2 (T [ 5 sHost= MAD] [ 0 -=req ]) = snps2 T"
  by simp





lemma HostModifiedRdOwn'_coherent_aux_simpler: assumes "SWMR_state_machine T \<and> HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 "
  shows "SWMR_state_machine  (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])"
proof -
have i0: "SWMR T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i1x: "HSTATE ModifiedM T " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextReqIs RdOwn T 0"  by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i4: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i5: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i6: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i10: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i11: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i12: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i13: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i14: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i15: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i16: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i17: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i18: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i19: "C_H_state Invalid nextStore Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i20: "C_H_state Invalid nextStore Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i21: "C_H_state Invalid nextStore Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i22: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i23: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i24: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i25: "C_msg_not RdShared IMAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i26: "C_msg_not RdShared Invalid T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i27: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i28: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i29: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i30: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i31: "C_state_not MIA RdShared T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i35: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i36: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i37: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i39: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i40: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i41: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i46: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i47: "C_msg_state RdShared ISAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i49: "C_not_C_msg Modified ISAD nextGOPending T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i50: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i51: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i52: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i56: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i57: "length (reqs1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i58: "length (reqs2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i59: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i60: "length (snps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i61: "length (snps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611old: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612old: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613old: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614old: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615old: "(CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616old: "(CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617old: "(CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618old: "(CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i68: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i69: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i70: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i71: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i72: "CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i73: "CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i74: "CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i75: "CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i76: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i77: "length (htddatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i78: "length (htddatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i79: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i80: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i81: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i82: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i83: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i84: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i85: "(length (reqresps1 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i86: "(length (reqresps2 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i87: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0)  \<longrightarrow> snps1 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i88: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1)  \<longrightarrow> snps2 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)

have i89: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i90: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i91: "(CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i92: "(CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i93: "(C_msg_P_same MIA  (nextReqIs DirtyEvict) (nextEvict) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i94: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i95: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i98: "(reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i99: "(reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i100: "(reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i101: "(reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have i751old: " (CSTATE ISD T 0 \<longrightarrow> nextLoad T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i752old: " (CSTATE ISD T 1 \<longrightarrow> nextLoad T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+

 
 have i104: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i105: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i106: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i107: "(HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i108: "(HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i109: "(HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i110: "(length (dthdatas1 T ) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i111: "(length (dthdatas2 T ) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i112: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i113: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i114: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i115: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 
 
 have i118: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i120: "(length (snpresps1 T) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i121: "(length (snpresps2 T) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i126: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i127: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i128: "(HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i129: "(HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i130: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i131: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i132: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i133: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i136: "(dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i137: "(dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i138: "(CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i139: "(CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i142: "(C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i143: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i144: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i145: "(CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i146: "(CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i147: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i148: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i149: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i150: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i153: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i154: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i159: "(HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i160: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i161: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i164: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i165: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i166: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i167: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i168: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i169: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i170: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i171: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i172: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i173: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i178: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i179: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i180: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i181: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i182: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i183: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i186: "(HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i187: "(CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i188: "(CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i189: "(HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i190: "(nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i191: "(nextDTHDataFrom  1 T \<longrightarrow> \<not> nextHTDDataPending T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i192: "(nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i193: "(nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i194: "(HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i195: "(HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i196: "(HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i197: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i198: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i199: "(CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i200: "(CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i301: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i302: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i305: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i306: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i307: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i308: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i309: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i310: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i313: "(HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i314: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i315: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i317: "(CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i318: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i319: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i320: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i321: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i322: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i323: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i324: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i325: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i326: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i327: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i328: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i329: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i332: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i333: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i334: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i335: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i336: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i337: "(C_not_C_msg Modified IMAD nextGOPending T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i338: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i339: "(CSTATE IMAD T 0 \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i340: "(CSTATE IMAD T 1 \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i341: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i342: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i343: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i344: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i345: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i346: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i347: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i348: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i349: "(CSTATE SMAD T 0 \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i350: "(CSTATE SMAD T 1 \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i351: "(C_msg_P_same IMA (nextGOPending) nextStore T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i353: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i354: "(C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i355: "(C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i356: "(C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i357: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i358: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 
 
 have i365: "(C_msg_P_same SMA (nextGOPending) nextStore T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i366: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i367: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i368: "(CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i369: "(CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i370: "(CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i371: "(CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i374: "(CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i375: "(CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i376: "(CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i377: "(CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i378: "(CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i379: "(CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i380: "(CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i381: "(CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i382: "(CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = [])"   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i383: "(CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i384: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i385: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i388: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i389: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i390: "(CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i391: "(CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i392: "(nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i393: "(nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i396: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i397: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i400: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i406: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0)  \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i407: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1)  \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i408: "(HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i415: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i416: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i417: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i418: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i419: "(CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i420: "(CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i421: "(HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i422: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i423: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i424: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i425: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i426: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i427: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i430: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i431: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i432: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i433: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i437: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i438: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i439: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i440: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i443: "(nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i444: "(nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i445: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i446: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i447: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i448: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i451: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i452: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i453: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i454: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i455: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i456: "(nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or>  CSTATE SIA T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i457: "(HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i458: "((nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i459: "((nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i462: "((CSTATE Invalid T 0  \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i463: "((CSTATE Invalid T 1  \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i464: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i465: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i467: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i468: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> (  nextHTDDataPending T 0) \<and>  \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i469: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i470: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i471: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i472: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i473: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i474: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i475: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i476: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i477: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i478: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i479: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i480: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i481: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i482: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i483: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i484: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i485: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i486: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i487: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i488: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i489: "(CSTATE Modified T 0 \<longrightarrow> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i490: "(CSTATE Modified T 1 \<longrightarrow> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i491: "(CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i492: "(CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i493: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i494: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i495: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i496: "(nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i497: "(nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i498: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i499: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i500: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i501: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i502: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i503: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i504: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i505: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i506: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i507: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i508: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i509: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i510: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i511: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i512: "(HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i513: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i514: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i515: "(HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i516: "(HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i517: "(CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i518: "(CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i519: "(C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i520: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i521: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i524: "(nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i525: "(nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i526: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i527: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i528: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i529: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i530: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i531: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i532: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i533: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i534: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i535: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i536: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i537: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i538: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i539: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i540: "(nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i541: "(nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i542: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i543: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i544: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i545: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i546: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i547: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i548: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i549: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i550: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i551: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i552: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i553: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i554: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i555: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i556: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i557: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i558: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i559: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i560: "((CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i561: "(CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i562: "(CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i563: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i564: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i565: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i566: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i567: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i568: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i569: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i570: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i571: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i572: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i573: "(CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i574: "(CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i575: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and>  \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i576: "(HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i577: "(nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i578: "(CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i579: "(CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i580: "(nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i581: "(nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i582: "((CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i583: "((CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i584: "(CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i585: "(CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i586: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i587: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i588: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i589: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i590: "((HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i591: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i592: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i593: "(HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i594: "(CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i595: "(CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i596: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i597: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i598: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i599: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i600: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i601: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i602: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i603: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i604: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i605: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i606: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i607: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i608: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i609: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i610: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i619: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i620: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i621: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i622: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i623: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i624: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i625: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i626: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i627: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i628: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i629: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i630: "(CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i631: "(CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i632: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i633: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i634: "(CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i635: "(CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i636: "(CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i637: "(CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i638: "(CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i639: "(CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i640: "(CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i641: "(CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i642: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i643: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i644: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i645: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i646: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i647: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i648: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i649: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i650: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i651: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i652: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i653: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i654: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i655: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i656: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i657: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i658: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i659: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i660: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i661: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i662: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i663: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i664: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i665: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i666: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i667: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i668: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i669: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i670: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i671: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i672: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i673: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i674: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i675: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i676: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i677: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i678: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i679: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i680: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i681: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i682: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i683: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i684: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i685: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i686: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i687: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i688: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i689: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i690: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i691: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i692: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i693: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i694: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i695: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i696: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i697: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i698: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i699: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i700: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i701: "(HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i702: "(HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i703: "(HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i704: "(HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i705: "(HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i706: "(HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i707: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i708: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i709: "(HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i710: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i711: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i712: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i713: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i714: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i715: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i716: "(HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i717: "(HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i718: "(HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i719: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i720: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i721: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i722: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i723: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i724: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i725: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i726: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i727: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i728: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i729: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i730: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i731: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i732: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i733: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i734: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i735: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i736: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i737: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i738: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i739: "(HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i740: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i741: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i742: "(HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i743: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i744: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i745: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i746: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i747: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i748: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i749: "(HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i750: "(HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i752: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i753: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i754: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i755: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i756: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i757: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i758: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i759: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i760: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i761: "(CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i762: "(CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i763: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i764: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i765: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i766: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i767: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i768: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i769: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i770: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i771: "(HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i772: "(HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i773: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i774: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i775: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i776: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i777: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i778: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i779: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i780: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i781: "(HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i782: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i783: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i784: "(HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i785: "(snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i786: "(snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i787: "(CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i788: "(CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i789: "(nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i790: "(nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i791: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i792: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i793: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i794: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i795: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i796: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i797: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i798: "(HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i799: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i800: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i801: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i802: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i803: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i804: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i805: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i806: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i807: "(HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i808: "(HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i809: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i810: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i811: "(HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i812: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i813: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i814: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i815: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i816: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i817: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i818: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i819: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i820: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i821: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i822: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i823: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i824: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i825: "(CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i826: "(CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i827: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i828: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i829: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i830: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i831: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i832: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i833: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i834: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i835: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i836: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i837: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i838: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i839: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i840: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i841: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i842: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i843: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i844: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i845: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i846: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i847: "(CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i848: "(CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i849: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i850: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i851: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i852: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i853: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i854: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i855: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i856: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i857: "(CSTATE Invalid T 0 \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i858: "(CSTATE Invalid T 1 \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i859: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i860: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i861: "(HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i862: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i863: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i864: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i865: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i866: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i867: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i868: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i869: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i870: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i871: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i872: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i873: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i874: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i875: "(HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i876: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i877: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i878: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i879: "(HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i880: "(HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i883: "length (dthdatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i884: "length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i885: "(HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i886: "(HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i887: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i888: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i889: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i890: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i891: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i892: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i893: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i894: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i895: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i896: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i897: "(CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i898: "(CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i899: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i900: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i901: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i902: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i903: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i904: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i905: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i906: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i907: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i908: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i909: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i910: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i911: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i912: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i913: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i914: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i915: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i916: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i917: "(HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i918: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i919: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i920: "(CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i921: "(CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i922: "(HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i923: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i924: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i925: "(CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i926: "(CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i927: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i928: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i929: "(CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i930: "(CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i931: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i932: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i933: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i934: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i935: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i936: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i937: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i938: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i939: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i940: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i941: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i942: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i945: "(HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i946: "(nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i947: "(nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i948: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i949: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i950: "(nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i951: "(nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i952: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i953: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i954: "((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i955: "((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i956: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i957: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i958: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i959: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> [])  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i960: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i961: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i962: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i963: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i964: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i965: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i966: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i967: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i968: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i969: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i970: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)






(*BigHeaderEnd*)

 have i201: " HSTATE MAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])"

subgoal  apply auto done  done
(* ./proofs/NewModifiedRdOwn/26286.txt *)

have i205: "\<not> nextReqIs RdShared T 0"

subgoal  using i2x nextReqIs_invariant apply blast done  done
(* ./proofs/NewModifiedRdOwn/26298.txt *)

  have i207: "\<not> CSTATE ISAD T 0"

subgoal  using CSTATE_disj1 i2x i392 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26310.txt *)

  have i2080: "length (reqs1 T) \<le> 1"

subgoal  using i57 apply auto done  done
(* ./proofs/NewModifiedRdOwn/26322.txt *)

  have i208: "reqs1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []"

subgoal  using HostModifiedRdOwn_empty_reqs1_aux reqlength1_minus i57 apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26334.txt *)

  have i209: "\<forall>X. \<not> nextReqIs X (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0"

subgoal  using i208 nextReqIs_not_various_forms1 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26346.txt *)

  have i210: " (reqresps1 T ) = []"

subgoal  using assms i94 nextReqIs_not_various_forms1 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26358.txt *)

  have i211: "(snps2 T ) = []"

subgoal  using assms i55 nextReqIs_not_various_forms1 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26370.txt *)

  have i212: "snpresps2 T = []"

subgoal  using i1x i159 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26382.txt *)

  have i2130: "length (snps2 (T [ 1 +=snp SnpInv txid]  )) \<le> 1"

subgoal  apply auto using i211 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26394.txt *)

  have i213: "  length( snps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) )\<le>1"

subgoal  using i2130 snps2_HostModifiedRdOwn apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26406.txt *)

  have i214: " snpresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = [] "

subgoal  using i212 snpresps2_HostsModifiedRdOwn apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26418.txt *)

  have i2150: "htddatas1 T = []"

subgoal  using assms i100 nextReqIs_not_various_forms1 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26430.txt *)

  have i215: "   htddatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []"

subgoal  using htddatas1_HostsModifiedRdOwn i2150 apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26442.txt *)

  have i217: "\<not>CSTATE ISAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0"

subgoal  using CSTATE_HostsModifiedRdOwn_otherside_invariant3 i207 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26454.txt *)

  have i2180: "\<not>CSTATE Shared T  1"

subgoal  using i1x i107 apply blast done  done
(* ./proofs/NewModifiedRdOwn/26466.txt *)

  have i218: "\<not>CSTATE Shared (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1"

subgoal  using CSTATE_HostsModifiedRdOwn_otherside_invariant2 i2180 apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26478.txt *)

  have i219: "dthdatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []"

subgoal  using dthdatas2_HostsModifiedRdOwn i1x i189 apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26490.txt *)

  have i2200: "reqresps1 T = []"

subgoal  apply ( simp add : i210 ) done  done
(* ./proofs/NewModifiedRdOwn/26502.txt *)

  have i220: "reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []"

subgoal  using i2200 reqresps1_HostsModifiedRdOwn2 apply presburger done  done
(* ./proofs/NewModifiedRdOwn/26514.txt *)
  have aux319_1: "nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply (insert i211)  by simp
  have aux_notSnpD: "\<not> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1"
 
 by (metis SnoopType.distinct(1) aux319_1 nextSnoopIs_invariant_variant1)

  show ?thesis
 unfolding SWMR_state_machine_def

(*BigLemmaEnd*)

proof (intro conjI)
  show goal1: "SWMR ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostSide_rule_13_0 CSTATE_various_forms2 CSTATE_various_forms6 assms i107 i218) done
  show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i825) done
  show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i217 i825) done
  show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201 i208 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i209 i825) done
  show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(15) HOST_State.distinct(269) HSTATE_invariant3 i201 i208 nextReqIs_not_various_forms1) done
  show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) assms dthdatas1_general_rule_11_0 i189 i209 i457 nextDTHDataPending_def) done
  show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(15) HOST_State.distinct(225) HSTATE_invariant3 i201 i208 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_otherside i209 i212 nextSnpRespIs_invariant2) done
  show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i209 i825) done
  show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i209 i825) done
  show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i209 i825) done
  show goal15: "C_H_state Invalid nextStore Modified SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496 i825) done
  show goal16: "C_H_state Invalid nextStore Modified SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496 i825) done
  show goal17: "C_H_state Invalid nextStore Modified SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496 i825) done
  show goal18: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal19: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal20: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal21: "C_msg_not RdShared IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 C_msg_not_def i209 i25 nextReqIs_otherside_rule_4_0) done
  show goal22: "C_msg_not RdShared Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 C_msg_not_def i209 i26 nextReqIs_otherside_rule_4_0) done
  show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(15) HOST_State.distinct(269) HSTATE_invariant3 i201 i208 nextReqIs_not_various_forms1) done
  show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 i187 i1x i590 nextGOPendingIs_general_rule_17_0 nextGOPendingIs_general_rule_17_1) done
  show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis i1x i590 nextGOPendingIs_general_rule_17_0 nextGOPendingIs_general_rule_17_1) done
  show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis i1x i590 nextGOPendingIs_general_rule_17_0 nextGOPendingIs_general_rule_17_1) done
  show goal27: "C_state_not MIA RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 C_state_not_def i209 i31 nextReqIs_otherside_rule_4_0) done
  show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_X_rd_invariant1 DIRTYEVICT_COL_def HTDDataPending_htddatas_invariant1 MEM_SD_ROW_def OFFSET_def assms i188 i215 i220 i415 i420 i578 i597 i753 i755 i825 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0 reqresps_empty_noGOPending1 reqresps_empty_noGOPendingIs1) done
  show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant DIRTYEVICT_COL_def MESI_State.distinct(339) i1x i209 i2200 i2x i420 i747 i825 i83 reqresps_empty_noGOPending1 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) i219 i220 nextDTHDataPending_def reqresps_empty_noGOPendingIs1) done
  show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(15) HOST_State.distinct(269) HSTATE_invariant3 i201 i208 nextReqIs_not_various_forms1) done
  show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i209 i313) done
  show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HOST_State.distinct(15) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal37: "C_msg_state RdShared ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 C_msg_state_def i209 i47 nextReqIs_otherside_rule_4_0) done
  show goal38: "C_not_C_msg Modified ISAD nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i217 i825) done
  show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 assms i1x i418 i467 i496 i578 i595 i747 i825 nextHTDDataPending_general_rule_13_0) done
  show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def Invalid_not_eq_MIA assms i187 i1x i337 i415 i418 i467 i496 i578 i595 i597 i744 i747 i825) done
  show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_X_rd_invariant1 DIRTYEVICT_COL_def HOST_State.distinct(11) HOST_State.distinct(141) HOST_State.distinct(15) HOST_State.distinct(179) HOST_State.distinct(35) HOST_State.distinct(9) HSTATE_invariant3 HSTATE_invariant4 OFFSET_def assms i101 i144 i1x i209 i217 i22 i415 i655 i662 nextGOPending_General_rule_19_1 nextHTDDataPending_def nextReqIs_not_various_forms2 nextReqIs_otherside_rule_4_0) done
  show goal42: "snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208 i214 i219 i220) done
  show goal43: "snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i208 i922 snps1_HostsModifiedRdOwn) done
  show goal44: "length (reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i208 i211 i60) done
  show goal45: "length (reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i58 reqs2_HostsModifiedRdOwn) done
  show goal46: "length (snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i213) done
  show goal47: "length (snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) assms i61 i922 snps1_HostsModifiedRdOwn) done
  show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_general_rule_8_0 C_not_C_msg_def assms i187 i1x i337 i353 i415 i418 i467 i496 i578 i595 i597 i744 i747 i754 i756 i825) done
  show goal51: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496) done
  show goal52: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 htddatas2_X_rd_invariant1 i159 i1x i382 i614old reqresps2_X_rd_invariant1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal53: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal54: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal55: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostSide_rule_13_0 CSTATE_different1 MESI_State.distinct(343) i1x i2x i747) done
  show goal56: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i159 i208 i618old snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal57: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal58: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i69 reqs2_HostsModifiedRdOwn) done
  show goal59: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal60: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal61: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal62: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal63: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal64: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal65: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal66: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i75) done
  show goal68: "length (htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i211 i215 i60) done
  show goal69: "length (htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) htddatas2_HostsModifiedRdOwn i78) done
  show goal70: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal71: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal72: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal73: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal74: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal75: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i84 nextHTDDataPending_general_rule_13_0 reqs2_HostsModifiedRdOwn) done
  show goal76: "length (reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i211 i220 i60) done
  show goal77: "length (reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i86 reqresps2_HostsModifiedRdOwn) done
  show goal78: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis i2200 reqresps1_HostsModifiedRdOwn2 reqresps_empty_noGOPendingIs1) done
  show goal79: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal80: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis i2200 reqresps1_HostsModifiedRdOwn2 reqresps_empty_noGOPendingIs1) done
  show goal81: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal82: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal83: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i92 nextReqIs_otherside_rule_4_0) done
  show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextEvict_otherside i209 i541 nextReqIs_otherside_rule_4_0) done
  show goal85: "reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal86: "reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208 i95 reqresps2_HostsModifiedRdOwn reqs2_HostsModifiedRdOwn) done
  show goal87: "reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal88: "reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal89: "reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal90: "reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) htddatas2_HostsModifiedRdOwn i101 i208 reqs2_HostsModifiedRdOwn) done
  show goal91: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal92: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def MESI_State.distinct(329) assms i187 i1x i337 i352 i415 i416 i548 i549 i578 i579 i597 i644 i645 i743 i744 i747 i748 i825 i826 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0 nextReqIs_otherside_rule_4_0) done
  show goal93: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 assms i1x i415 i518 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal94: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal95: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i199 i1x i415 i518 i747 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal96: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i420 i747 i825 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0) done
  show goal97: "reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal98: "reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208 i95 reqresps2_HostsModifiedRdOwn reqs2_HostsModifiedRdOwn) done
  show goal99: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal100: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal101: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal102: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal103: "length (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i211 i2150 i60) done
  show goal104: "length (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i211 i219 i60) done
  show goal105: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal106: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal107: "HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(201) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal108: "HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(201) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal109: "nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal110: "nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 assms i1x i380 i459 nextSnpRespIs_general_rule_14_0) done
  show goal111: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal112: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i456 nextReqIs_otherside_rule_4_0) done
  show goal113: "snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal114: "snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal115: "length (snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i211 i2150 i60 snpresps1_HostsModifiedRdOwn) done
  show goal116: "length (snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i211 i214 i60) done
  show goal117: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal118: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal119: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_sameside assms i159 nextSnpRespIs_invariant1) done
  show goal120: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_otherside i212 nextSnpRespIs_invariant2) done
  show goal121: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal122: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal123: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal124: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal125: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal126: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HSTATE_invariant4 i201) done
  show goal127: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal128: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal129: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal130: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal131: "dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal132: "dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal133: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal134: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_X_rd_invariant1 DIRTYEVICT_COL_def HTDDataPending_htddatas_invariant1 OFFSET_def assms i187 i2150 i220 i2200 i415 i420 i578 i597 i755 i825 reqresps_empty_noGOPending1 reqresps_empty_noGOPendingIs1) done
  show goal136: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal137: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal138: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal139: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i146 nextLoad_general_rule_12_0) done
  show goal140: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal141: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 HOST_State.distinct(11) HOST_State.distinct(141) HOST_State.distinct(15) HOST_State.distinct(35) HOST_State.distinct(9) HSTATE_invariant3 HSTATE_invariant4 MESI_State.distinct(11) MESI_State.distinct(273) OFFSET_def assms empty_no_snoop i144 i1x i334 i336 i353 i415 i468 i655 i657 i659 i661 i738 i747 i922)done
  show goal142: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal143: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i150 i159 i208 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal144: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i380 i415 i496 i518 i747 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal145: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant Invalid_not_eq_MIA assms i1x i380 i415 i418 i467 i595 i747 i754 i825) done
  show goal146: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal147: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i187 i1x i2150 i2200 i380 i415 i418 i578 i597 i747 i759 i825 nextHTDDataPending_various_forms1 reqresps_empty_noGOPending1) done
  show goal148: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i212 i214 snpresps1_HostsModifiedRdOwn) done
  show goal149: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal150: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal151: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HSTATE_invariant4 i201) done
  show goal152: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal153: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HSTATE_invariant4 i201) done
  show goal154: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal155: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HSTATE_invariant4 i201) done
  show goal156: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal157: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal158: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal159: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal160: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal161: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i199 i1x i415 i518 i747 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal162: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i420 i747 i825 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0) done
  show goal163: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal164: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal165: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal166: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal167: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i220 reqresps_empty_noGOPendingIs1) done
  show goal168: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HTDDataPending_htddatas_invariant1 OFFSET_def assms i188 i2150 i2200 i415 i420 i578 i597 i753 i755 i825 reqresps_empty_noGOPending1) done
  show goal169: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal170: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal171: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal172: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal173: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal174: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i187) done
  show goal175: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i187) done
  show goal176: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal177: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219 i457) done
  show goal178: "nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i190 nextDTHDataFrom_general_rule_11_0 nextHTDDataPending_general_rule_13_0) done
  show goal179: "nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i191 nextDTHDataFrom_general_rule_11_0 nextHTDDataPending_general_rule_13_0) done
  show goal180: "nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i192 nextDTHDataFrom_general_rule_11_0) done
  show goal181: "nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i192 nextDTHDataFrom_general_rule_11_0) done
  show goal182: "HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal183: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i199) done
  show goal184: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> (\<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal185: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal186: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal187: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i199) done
  show goal188: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i199) done
  show goal189: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis i1x i590 nextGOPendingIs_general_rule_17_0) done
  show goal190: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal191: "snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal192: "snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal193: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal194: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal195: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal196: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal197: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal198: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal199: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i209 i313) done
  show goal202: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostSide_rule_13_0 CSTATE_different1 MESI_State.distinct(355) i1x i2x i747) done
  show goal203: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i159 i208 i317 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal205: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal206: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal208: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal209: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 MESI_State.distinct(355) MESI_State.distinct(385) MESI_State.distinct(413) MESI_State.distinct(43) MESI_State.distinct(505) MESI_State.distinct(565) MESI_State.distinct(575) MESI_State.distinct(583) OFFSET_def assms i220 i415 reqresps_empty_noGOPendingIs1) done
  show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_X_rd_invariant1 C_msg_P_same_def C_state_not_def i101 i1x i220 i2x i31 i324 i371 i415 i490 i739 nextHTDDataPending_various_forms2 nextReqIs_not_various_forms2 nextReqIs_otherside_rule_4_0 nextStore_nextEvict_exclusive reqresps_empty_noGOPendingIs1) done
  show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 MESI_State.distinct(355) MESI_State.distinct(385) MESI_State.distinct(413) MESI_State.distinct(43) MESI_State.distinct(505) MESI_State.distinct(565) MESI_State.distinct(575) MESI_State.distinct(583) OFFSET_def assms i220 i415 reqresps_empty_noGOPendingIs1) done
  show goal213: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i220 reqresps_empty_noGOPendingIs1) done
  show goal214: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 MESI_State.distinct(355) MESI_State.distinct(385) MESI_State.distinct(413) MESI_State.distinct(43) MESI_State.distinct(505) MESI_State.distinct(565) MESI_State.distinct(575) MESI_State.distinct(583) OFFSET_def assms i415) done
  show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) i219 i220 nextDTHDataPending_def reqresps_empty_noGOPendingIs1) done
  show goal216: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal217: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal218: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 DIRTYEVICT_COL_def HOST_State.distinct(11) HOST_State.distinct(15) HOST_State.distinct(17) HOST_State.distinct(3) HOST_State.distinct(35) HSTATE_invariant3 i1x i334 i772 nextHTDDataPending_general_rule_13_0) done
  show goal219: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal220: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i336 i747 nextHTDDataPending_general_rule_13_0) done
  show goal221: "C_not_C_msg Modified IMAD nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 C_not_C_msg_def assms i337 i747 i825 nextGOPending_General_rule_19_0) done
  show goal222: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal223: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i339 i747 nextStore_general_rule_12_0) done
  show goal224: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i340 nextStore_general_rule_12_0) done
  show goal225: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal226: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i342 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal227: "snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal228: "snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal229: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal230: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal231: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal232: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal233: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal234: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i350 nextStore_general_rule_12_0) done
  show goal235: "C_msg_P_same IMA nextGOPending nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i339 i371 i747 nextStore_general_rule_12_0) done
  show goal236: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i352 i749 nextHTDDataPending_general_rule_13_0) done
  show goal237: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i353 i749 nextHTDDataPending_general_rule_13_0) done
  show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) i1x i220 i922 nextSnoopPending_empty_not_other_rule_3_0 reqresps_empty_noGOPending1) done
  show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) i1x i220 i922 nextSnoopPending_empty_not_other_rule_3_0 reqresps_empty_noGOPending1) done
  show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal241: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal242: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal243: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> ((CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) aux319_1) done
  show goal244: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> ((CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_HostSide_rule_13_0 CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_otherside_rule_33 assms i107 i2x i392 i468 i517 i74 i749 nextGOPending_General_rule_19_0 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0 nextSnoopIs_otherside_rule_3_0) done
  show goal245: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal246: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal247: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal248: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal249: "C_msg_P_same SMA nextGOPending nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i339 i371 i747 nextStore_general_rule_12_0) done
  show goal250: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal251: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal252: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i217 i368 i74 i749 nextLoad_general_rule_12_0) done
  show goal253: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextLoad ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i146 i380 i749 i75 nextLoad_general_rule_12_0) done
  show goal254: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i339 i747 nextStore_general_rule_12_0) done
  show goal255: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextStore ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i340 i350 i371 nextStore_general_rule_12_0) done
  show goal256: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms dthdatas1_HostsModifiedRdOwn i107 i189 i217 i464 i749 nextHTDDataPending_general_rule_13_0) done
  show goal257: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i219 i825) done
  show goal258: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal259: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal260: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal261: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal262: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostSide_rule_13_0 CSTATE_different1 MESI_State.distinct(295) i1x i2x i747) done
  show goal263: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i380) done
  show goal264: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> \<not> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i379 nextReqIs_otherside_rule_4_0) done
  show goal265: "CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> \<not> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal266: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal267: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 i382 reqresps2_HostsModifiedRdOwn) done
  show goal268: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal269: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal270: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal271: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal272: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i1x i415 i622 i747 i760 i846 i910 nextHTDDataPending_various_forms2 nextSnoopIs_otherside_rule_3_0) done
  show goal273: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i159 i1x i415 i492 i555 i585 i601 i680 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal274: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HSTATE_equals_sHost HSTATE_invariant3 assms hstate_invariants(13) i1x i2150 i2200 i390 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal275: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_X_rd_invariant1 CSTATE_different2 MESI_State.distinct(35) MESI_State.distinct(497) htddatas2_X_rd_invariant1 i1x i2x i415 i518 nextHTDDataPending_various_forms2) done
  show goal276: "nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal277: "nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal278: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> CXL_SPG_used ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal279: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> CXL_SPG_used ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 CXL_SPG_used_def CXL_SPG_used_general_rule_10_0 MESI_State.distinct(35) MESI_State.distinct(405) MESI_State.distinct(497) MESI_State.distinct(561) OFFSET_def SPG_simple_def assms i415 i518 i747 i83 nextReqIs_not_various_forms1 reqresps_empty_noGOPending2) done
  show goal280: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal281: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal282: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal283: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal284: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i212 i214 snpresps1_HostsModifiedRdOwn) done
  show goal285: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal286: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal287: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal288: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(225) HOST_State.distinct(251) HSTATE_invariant3 i201) done
  show goal289: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal290: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i189 i1x nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal291: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal292: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal293: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal294: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal295: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i192 i219 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal296: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i189 i457 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal297: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i189 i457 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal298: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i189 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal299: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal300: "(HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal301: "(HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal302: "nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i107 i1x i443 i747 nextSnpRespIs_general_rule_14_0) done
  show goal303: "nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 HostsModifiedRdOwn_nextSnpRespIs_otherside i2180 i444) done
  show goal304: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(249) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal305: "(CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i187 i1x i380 i415 i416 i418 i578 i597 i747 i825 nextHTDDataPending_general_rule_13_0 nextReqIs_otherside_rule_4_0) done
  show goal306: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal307: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal308: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal309: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal310: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal311: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal312: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_X_rd_invariant1 i1x i2x i622 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal313: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal314: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal315: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal316: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_X_rd_invariant1 i1x i2x i622 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal317: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal318: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal319: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal320: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(329) assms i747) done
  show goal321: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal322: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597) done
  show goal323: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal324: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_H_state_def MESI_State.distinct(261) assms i17 i1x i415 i578 i687 i693 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal325: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal326: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal327: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal328: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal329: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal330: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal331: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i490 reqs2_HostsModifiedRdOwn) done
  show goal332: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal333: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i159 i208 i492 reqresps2_HostsModifiedRdOwn snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal334: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal335: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal336: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal337: "nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal338: "nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i497 nextReqIs_otherside_rule_4_0) done
  show goal339: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal340: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal341: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal342: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal343: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i415 i462 i504 i579 i622 i747 i844 i856 i894 i896 nextHTDDataPending_various_forms2 nextSnoopIs_otherside_rule_3_0) done
  show goal344: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i317 i585 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal345: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 HSTATE_invariant4 assms i201 i504 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal346: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 MESI_State.distinct(385) MESI_State.distinct(43) MESI_State.distinct(505) MESI_State.distinct(575) OFFSET_def assms i317 i415 nextHTDDataPending_various_forms2) done
  show goal347: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> CXL_SPG_used ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 CXL_SPG_used_general_rule_10_0 assms i370 i506 i563 i565 i747 nextSnoopIs_otherside_rule_3_0 nextStore_nextEvict_exclusive) done
  show goal348: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> CXL_SPG_used ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 CXL_SPG_used_def CXL_SPG_used_general_rule_10_0 MESI_State.distinct(43) MESI_State.distinct(505) OFFSET_def SPG_simple_def assms i1x i317 i415 nextHTDDataPending_various_forms2 numerals(1) reqresps_empty_noGOPending2 zero_neq_numeral) done
  show goal349: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i508 i510 nextSnoopIs_otherside_rule_3_0) done
  show goal350: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal351: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal352: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal353: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal354: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (\<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal355: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (\<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218 i825) done
  show goal356: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal357: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal358: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal359: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i518 i914 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
  apply  (cases "dthdatas1 T") apply  (auto)
apply (smt (verit) i2200 nextReqRespIs.simps(1)) 
apply (smt (verit) i1x i922) 
apply (smt (verit) i189 i194 i1x i2200 list.discI) 
apply (smt (verit) i1x i922) 
 done

  show goal361: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal362: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i947 nextReqIs_otherside_rule_4_0) done
  show goal363: "nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal364: "nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal365: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal366: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextEvict_otherside i564 nextReqIs_otherside_rule_4_0) done
  show goal367: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal368: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextEvict_otherside i564 nextReqIs_otherside_rule_4_0) done
  show goal369: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal370: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i380) done
  show goal371: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal372: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i380) done
  show goal373: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal374: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i564 i568 nextReqIs_otherside_rule_4_0) done
  show goal375: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal376: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i564 i568 nextReqIs_otherside_rule_4_0) done
  show goal377: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal378: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal379: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal380: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextEvict_otherside i541 nextReqIs_otherside_rule_4_0) done
  show goal381: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal382: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) assms i189 i457 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal383: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal384: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal385: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal386: "nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]))"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal387: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i548 i749 nextHTDDataPending_general_rule_13_0) done
  show goal388: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i549 i749 nextHTDDataPending_general_rule_13_0) done
  show goal389: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i201 i550 nextHTDDataPending_general_rule_13_0 nextSnoopIs_otherside_rule_3_0) done
  show goal390: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i201 i747) done
  show goal391: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i215 nextHTDDataPending_def) done
  show goal392: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal393: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i336 i747 i83 nextHTDDataPending_general_rule_13_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal394: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i555 i922 nextHTDDataPending_general_rule_13_0 reqresps2_HostsModifiedRdOwn snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal395: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 i556 nextHTDDataPending_general_rule_13_0 nextReqIs_otherside_rule_4_0) done
  show goal396: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal397: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal398: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i559 i947 nextReqIs_otherside_rule_4_0) done
  show goal399: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal400: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal401: "CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal402: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal403: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> nextEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextEvict_otherside i564 nextReqIs_otherside_rule_4_0) done
  show goal404: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal405: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i380) done
  show goal406: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal407: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextReqIs CleanEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i568 nextReqIs_otherside_rule_4_0) done
  show goal408: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal409: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 C_msg_state_def i47 nextReqIs_otherside_rule_4_0) done
  show goal410: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal411: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> ((CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)) \<and> \<not> ((CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal412: "nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal413: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597) done
  show goal414: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i579 nextHTDDataPending_general_rule_13_0) done
  show goal415: "nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal416: "nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal417: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal418: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal419: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597) done
  show goal420: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i159 i208 i585 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal421: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal422: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i201) done
  show goal423: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i187 i1x i588 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal424: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal425: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal426: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i1x i415 i575 i591 i663 i675 i678 i701 i739 i768 i770 i771 i772) done
  show goal427: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i199 i1x i415 i575 i592 i663 i675 i678 i701 i739 i747 i768 i770 i771 i772 i915 i916) done
  show goal428: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i219) done
  show goal429: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496) done
  show goal430: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def Invalid_not_eq_MIA assms i187 i1x i337 i415 i418 i467 i578 i595 i597 i744 i747 i825 i835) done
  show goal431: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal432: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i597) done
  show goal433: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HSTATE_equals_sHost assms hstate_invariants(13) htddatas2_HostsModifiedRdOwn i1x i598 i622 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal434: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(249) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal435: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal436: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i601 i914 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal437: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HSTATE_equals_sHost assms hstate_invariants(13) i1x i462 i696 i747 nextHTDDataPending_general_rule_13_0 nextSnoopIs_otherside_rule_3_0) done
  show goal438: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(249) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal439: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i749) done
  show goal440: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749 i75) done
  show goal441: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal442: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal443: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal444: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal445: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal446: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) i215 i220 nextHTDDataPending_def reqresps_empty_noGOPending1) done
  show goal447: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal448: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal449: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal450: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<or> HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal451: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal452: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal453: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal454: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749) done
  show goal455: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal456: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_different2 CSTATE_general_rule_8_0 HOST_State.distinct(11) HOST_State.distinct(15) HOST_State.distinct(167) HOST_State.distinct(35) HOST_State.distinct(9) HSTATE_invariant3 HSTATE_invariant4 MESI_State.distinct(11) MESI_State.distinct(261) MESI_State.distinct(273) MESI_State.distinct(285) OFFSET_def assms i144 i334 i336 i353 i415 i468 i655 i657 i661 i696 i738 i747) done
  show goal457: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i208 i622 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal458: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal459: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i208 i622 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal460: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal461: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms htddatas2_HostsModifiedRdOwn i1x i622 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal462: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal463: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal464: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal465: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms htddatas2_HostsModifiedRdOwn i208 i622 i696 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal466: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal467: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms htddatas2_HostsModifiedRdOwn i1x i622 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal468: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal469: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i749) done
  show goal470: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749 i75) done
  show goal471: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<longrightarrow> \<not> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal472: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<longrightarrow> \<not> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal473: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal474: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal475: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal476: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749) done
  show goal477: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i642 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal478: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal479: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i644 i749 nextHTDDataPending_general_rule_13_0) done
  show goal480: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i645 i749 nextHTDDataPending_general_rule_13_0) done
  show goal481: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal482: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal483: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal484: "CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal485: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal486: "CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749) done
  show goal487: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal488: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HOST_State.distinct(15) HOST_State.distinct(35) HOST_State.distinct(9) HSTATE_invariant3 OFFSET_def assms i144 i22 i415 i637 i655 i657 i659 i661 i662 nextGOPending_General_rule_19_1) done
  show goal489: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal490: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 HOST_State.distinct(11) HOST_State.distinct(141) HOST_State.distinct(35) HOST_State.distinct(375) HSTATE_invariant3 OFFSET_def assms i1x i22 i334 i336 i353 i415 i462 i468 i598 i622 i657 i659 i661 i662 i738 i747 i754 i756 i844 nextHTDDataPending_general_rule_13_0)done
  show goal491: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(329) MESI_State.distinct(349) assms i747) done
  show goal492: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal493: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal494: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal495: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal496: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal497: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal498: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal499: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HOST_State.distinct(85) HSTATE_invariant3 i201) done
  show goal500: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal501: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal502: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal503: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal504: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal505: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i220 reqresps_empty_noGOPending1) done
  show goal506: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal507: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant HSTATE_equals_sHost MESI_State.distinct(347) assms hstate_invariants(13) i1x i747) done
  show goal508: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal509: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal510: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal511: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i336 i747 i83 nextHTDDataPending_general_rule_13_0 nextReqIs_not_various_forms1) done
  show goal512: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(251) HSTATE_invariant3 i201) done
  show goal513: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107) done
  show goal514: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i218) done
  show goal515: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal516: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal517: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i336 i747 i83 nextHTDDataPending_general_rule_13_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal518: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i761 i922 reqresps2_HostsModifiedRdOwn snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal519: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i336 i747 i83 nextHTDDataPending_general_rule_13_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal520: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i342 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal521: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i683 nextSnoopIs_otherside_rule_3_0) done
  show goal522: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal523: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i685 nextSnoopIs_otherside_rule_3_0) done
  show goal524: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal525: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i687 i747 nextSnoopIs_otherside_rule_3_0) done
  show goal526: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal527: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_H_state_def HSTATE_X_rd_invariant1 HSTATE_equals_sHost HSTATE_invariant3 MESI_State.distinct(329) MESI_State.distinct(347) MESI_State.distinct(377) assms hstate_invariants(13) i148 i17 i1x i336 i353 i415 i462 i467 i468 i551 i603 i642 i687 i693 i696 i697 i699 i747 i756 nextSnoopIs_otherside_rule_3_0)done
  show goal528: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal529: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 CSTATE_inequality_invariant MESI_State.distinct(329) assms i747) done
  show goal530: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal531: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) empty_no_snoop i1x i922 nextSnoopIs_otherside_rule_3_0) done
  show goal532: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal533: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal534: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal535: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal536: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal537: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HSTATE_invariant4 i201) done
  show goal538: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HSTATE_invariant4 i201) done
  show goal539: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) assms i190 i1x i420 i747 i825 nextDTHDataFrom_general_rule_11_0) done
  show goal540: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal541: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> length (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1 \<and> length (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HSTATE_invariant4 i201) done
  show goal542: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal543: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal544: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal545: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal546: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal547: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal548: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HSTATE_invariant4 i201) done
  show goal549: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HSTATE_invariant4 i201) done
  show goal550: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HSTATE_invariant4 i201) done
  show goal551: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal552: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HSTATE_invariant4 i201) done
  show goal553: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal554: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HSTATE_invariant4 i201) done
  show goal555: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal556: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(269) HSTATE_invariant4 i201) done
  show goal557: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal558: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal559: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal560: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal561: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> lastSharer ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal562: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> lastSharer ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal563: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> lastSharer ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal564: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> lastSharer ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal565: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal566: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal567: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal568: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal569: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal570: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(249) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal571: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> (\<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i739 i747 nextGOPendingIs_general_rule_17_0 nextGOPendingIs_general_rule_17_1) done
  show goal572: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal573: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal574: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal575: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 i743 nextGOPending_General_rule_19_1) done
  show goal576: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i744 i747 nextGOPending_General_rule_19_0) done
  show goal577: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i759) done
  show goal578: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i760) done
  show goal579: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal580: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal581: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal582: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal583: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal584: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal585: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597 i753) done
  show goal586: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i579 i754) done
  show goal587: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597 i755) done
  show goal588: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i579 i756) done
  show goal589: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1))"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i187 i1x i747) done
  show goal590: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i579 i744 i747 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0) done
  show goal591: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i759) done
  show goal592: "CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i760) done
  show goal593: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i208 i761 reqresps2_HostsModifiedRdOwn) done
  show goal594: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal595: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal596: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal597: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i749) done
  show goal598: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749 i75) done
  show goal599: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal600: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal601: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal602: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal603: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal604: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal605: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal606: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal607: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i220) done
  show goal608: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(225) HSTATE_invariant4 i201) done
  show goal609: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(225) HOST_State.distinct(251) HSTATE_invariant3 i201) done
  show goal610: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HTDDataPending_htddatas_invariant1 i2150 nextHTDDataPending_general_rule_13_0) done
  show goal611: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal612: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdShared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i780 nextReqIs_otherside_rule_4_0) done
  show goal613: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal614: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal615: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal616: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal617: "snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal618: "snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<and> HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal619: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms empty_no_snoop_variant2 i159 i1x i211 i415 i467 i492 i756 i761 i922 reqresps2_X_rd_invariant1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal620: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal621: "nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal622: "nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i748 nextReqIs_otherside_rule_4_0) done
  show goal623: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal624: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspSFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal625: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i218 i793 i831 nextGOPending_General_rule_19_0) done
  show goal626: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i825) done
  show goal627: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal628: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal629: "HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal630: "HSTATE SharedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal631: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(201) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal632: "CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(201) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal633: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal634: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal635: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74 i75) done
  show goal636: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i747) done
  show goal637: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal638: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal639: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i212 i214 snpresps1_HostsModifiedRdOwn) done
  show goal640: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal641: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal642: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(265) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal643: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i187 i190 i415 i416 i430 i437 i438 i467 i468 i578 i599 i696 i697 i737 i743 i744 i747 i748 i825 i826 i909 i910 nextDTHDataFrom_general_rule_11_0 nextReqIs_not_various_forms2 nextReqIs_otherside_rule_4_0) done
  show goal644: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal645: "HSTATE MB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal646: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis i1x i590 nextGOPendingIs_general_rule_17_0) done
  show goal647: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal648: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i189 i457 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal649: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal650: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal651: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal652: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal653: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal654: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal655: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal656: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal657: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i826 nextReqIs_otherside_rule_4_0) done
  show goal658: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i75) done
  show goal659: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i74) done
  show goal660: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i415 i417 i579 i747 i793 i829 i831 i836 nextGOPending_General_rule_19_0) done
  show goal661: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal662: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i353 i415 i417 i579 i747 i793 i831 nextGOPending_General_rule_19_0) done
  show goal663: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i353 i415 i417 i579 i747 i793 i831 nextGOPending_General_rule_19_0) done
  show goal664: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i749) done
  show goal665: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i749) done
  show goal666: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i217 i749 i831 i835 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal667: "CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(329) assms i1x i747) done
  show goal668: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i189 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal669: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i208 i922 snps1_HostsModifiedRdOwn) done
  show goal670: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i187 i1x i415 i578 i597) done
  show goal671: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_X_rd_invariant1 i187 i219 nextDTHDataFrom_def) done
  show goal672: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i189 i1x nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal673: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i192 i219 nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0) done
  show goal674: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal675: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i215 i844) done
  show goal676: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal677: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i846) done
  show goal678: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal679: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal680: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i849 nextGOPending_General_rule_19_0 nextGOPending_General_rule_19_1) done
  show goal681: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) i217) done
  show goal682: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i218 i749) done
  show goal683: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i749) done
  show goal684: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal685: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal686: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i855 nextGOPending_General_rule_19_0) done
  show goal687: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i856 nextGOPending_General_rule_19_1) done
  show goal688: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i496) done
  show goal689: "CSTATE Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i188 i1x i2150 i2200 i415 i418 i578 i597 i747 i825 nextHTDDataPending_various_forms1 reqresps_empty_noGOPending1) done
  show goal690: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal691: "HSTATE SD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE ISD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(175) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal692: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal693: "HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(147) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal694: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 C_not_C_msg_def assms i1x i336 i337 i415 i549 i645 i687 i744 i747 i835 i908 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0 nextSnoopIs_otherside_rule_3_0) done
  show goal695: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE ISAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) aux_notSnpD) done
  show goal696: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis C_not_C_msg_def assms i1x i337 i371 i415 i541 i549 i645 i744 i747 i909 nextGOPending_General_rule_19_0 nextHTDDataPending_general_rule_13_0 nextReqIs_otherside_rule_4_0 nextStore_nextEvict_exclusive) done
  show goal697: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal698: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis htddatas1_general_rule_13_0 i2150 nextHTDDataPending_various_forms1) done
  show goal699: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i159 i208 i601 i914 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal700: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal701: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal702: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal703: "CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextGOPendingIs_otherside assms i313) done
  show goal704: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal705: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal706: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> (\<not> CSTATE SIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant HSTATE_equals_sHost assms hstate_invariants(13) i1x i739 i747 nextGOPendingIs_general_rule_17_0 nextGOPendingIs_general_rule_17_1) done
  show goal707: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(249) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal708: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i214 nextSnpRespIs_property2) done
  show goal709: "length (dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i211 i2150 i60) done
  show goal710: "length (dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) i211 i219 i60) done
  show goal711: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i313 nextGOPendingIs_general_rule_17_0) done
  show goal712: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> CSTATE IIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal713: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal714: "HSTATE MAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i107 i218) done
  show goal715: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i159 i208 snpresps1_HostsModifiedRdOwn) done
  show goal716: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE Shared ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i214) done
  show goal717: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal718: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> reqresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal719: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (metis i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal720: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i353 i415 i417 i579 i747 i831 i844 i894) done
  show goal721: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> (htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1)"
 apply  (insert assms)(**)apply (metis i2200 nextGOPending_General_rule_19_0 reqresps_empty_noGOPending1) done
  show goal722: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> (htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<or> CSTATE ISDI ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i353 i415 i417 i579 i747 i844 i856 i894 i896) done
  show goal723: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms dthdatas1_HostsModifiedRdOwn i189 i208) done
  show goal724: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i219) done
  show goal725: "nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 HostsModifiedRdOwn_nextSnpRespIs_sameside i899) done
  show goal726: "nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 HostsModifiedRdOwn_nextSnpRespIs_otherside i900) done
  show goal727: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i901 nextHTDDataPending_general_rule_13_0) done
  show goal728: "CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal729: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 i903 nextHTDDataPending_general_rule_13_0) done
  show goal730: "CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal731: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i747 i909 nextGOPending_General_rule_19_0) done
  show goal732: "CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i353 i415 i417 i747 i758 i760 i831 i846 i906) done
  show goal733: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i747 i909 nextGOPending_General_rule_19_0) done
  show goal734: "CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i353 i415 i417 i747 i760 i846 i908) done
  show goal735: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 assms i747 i909 nextGOPending_General_rule_19_0) done
  show goal736: "CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal737: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal738: "HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(251) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal739: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 assms i1x i747 i909 nextGOPending_General_rule_19_0) done
  show goal740: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal741: "HSTATE InvalidM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(117) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal742: "HSTATE IB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal743: "HSTATE ID ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(225) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal744: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal745: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_disj1 C_not_C_msg_def HSTATE_X_rd_invariant1 HSTATE_invariant3 assms i187 i1x i337 i352 i371 i380 i415 i418 i420 i456 i459 i467 i478 i541 i579 i597 i744 i747 i825 i919 i92 nextReqIs_otherside_rule_4_0 nextSnpRespIs_general_rule_14_0 nextStore_nextEvict_exclusive)done
  show goal746: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal747: "CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i215) done
  show goal748: "HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(15) HSTATE_invariant4 i201) done
  show goal749: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis htddatas1_general_rule_13_0 i2150 nextHTDDataPending_various_forms1) done
  show goal750: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpInv ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i215 i747) done
  show goal751: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal752: "CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant MESI_State.distinct(347) assms i1x i747) done
  show goal753: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(201) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal754: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE SA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i825) done
  show goal755: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 i929 nextHTDDataPending_general_rule_13_0) done
  show goal756: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i930 nextHTDDataPending_general_rule_13_0) done
  show goal757: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i931 i941 nextGOPendingStateGeneral_rule_19_0 nextGOPending_General_rule_19_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal758: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> snpresps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = [] \<and> htddatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 htddatas2_X_rd_invariant1 i159 i1x i922 i932 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_1 snpresps1_HostsModifiedRdOwn snps1_HostsModifiedRdOwn) done
  show goal759: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def assms i1x i337 i415 i744 i747 i909 i930 nextGOPending_General_rule_19_0 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal760: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def IMAD_HTDData_overall_def MESI_State.distinct(169) MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) MESI_State.distinct(5) assms i1x i337 i415 i579 i744 i747 i825 i835 i856 i930 i934 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_0 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal761: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant3 assms i941 nextGOPendingStateGeneral_rule_19_0 nextGOPending_General_rule_19_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal762: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i2150 i2200 i415 i578 i597 i743 i747 i759 i825 i930 i934 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_1 nextHTDDataPending_various_forms1 reqresps_empty_noGOPending1) done
  show goal763: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_X_rd_invariant1 CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def HSTATE_equals_sHost MESI_State.distinct(329) MESI_State.distinct(349) assms hstate_invariants(13) i1x i337 i353 i415 i467 i551 i603 i695 i744 i747 i909 i929 i930 i933 nextGOPendingStateGeneral_rule_19_0 nextGOPending_General_rule_19_0) done
  show goal764: "(CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (CSTATE IMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant C_not_C_msg_def IMAD_HTDData_overall_def MESI_State.distinct(169) MESI_State.distinct(329) MESI_State.distinct(339) MESI_State.distinct(349) MESI_State.distinct(5) assms i1x i337 i415 i579 i744 i747 i825 i835 i930 i934 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_1 nextHTDDataPending_general_rule_13_0) done
  show goal765: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> snps1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i208 i922 snps1_HostsModifiedRdOwn) done
  show goal766: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> snps2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_general_rule_8_0 CSTATE_inequality_invariant assms i1x i2150 i2200 i415 i578 i597 i743 i747 i825 i930 i934 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_1 nextHTDDataPending_various_forms1 reqresps_empty_noGOPending1) done
  show goal767: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> reqs1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) i208) done
  show goal768: "CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> reqs2 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i942 nextGOPendingStateGeneral_rule_19_1 nextGOPending_General_rule_19_1 reqs2_HostsModifiedRdOwn) done
  show goal769: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i336 i747 i83 nextHTDDataPending_general_rule_13_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal770: "HSTATE MA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_otherside i212 nextSnpRespIs_invariant2) done
  show goal771: "HSTATE SB ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HOST_State.distinct(267) HOST_State.distinct(269) HSTATE_invariant3 i201) done
  show goal772: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal773: "nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_HostsModifiedRdOwn_otherside_invariant2 i947 nextReqIs_otherside_rule_4_0) done
  show goal774: "nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_sameside i948 nextDTHDataFrom_general_rule_11_0) done
  show goal775: "nextSnpRespIs RspIHitSE ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ])"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_otherside i949 nextDTHDataFrom_general_rule_11_0) done
  show goal776: "nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i209) done
  show goal777: "nextSnpRespIs RspIFwdM ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 1 +=snp SnpInv txid] [ 5 sHost= MAD] [ 0 -=req ]) 1"
 apply  (insert assms)(**)apply (smt (verit) HostsModifiedRdOwn_nextSnpRespIs_otherside i951 nextReqIs_otherside_rule_4_0) done
  show goal778: "(CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextSnoopIs SnpData (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<longrightarrow> HSTATE SAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])) "

 by (smt (verit) empty_no_snoop i1x i922 nextSnoopIs_otherside_rule_3_0)
  show goal779: "(CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextSnoopIs SnpData (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<longrightarrow> HSTATE SAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])) "

 by (smt (verit) aux_notSnpD)
  show goal780: "((CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or>(CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) "

 by (smt (verit) HOST_State.distinct(15) HSTATE_invariant3 i201)
  show goal781: "((CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or>(CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0)   "

 by (smt (verit) HOST_State.distinct(15) HSTATE_invariant3 i201)
  show goal782: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE ModifiedM (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or>(CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> (CSTATE IMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) "

 by (smt (verit) HOST_State.distinct(15) HSTATE_invariant3 i201)
  show goal783: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE ModifiedM (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> CSTATE Modified (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or>(CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextGOPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> (CSTATE IMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0)   "

 by (smt (verit) HOST_State.distinct(15) HSTATE_invariant3 i201)
  show goal784: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> []) "
apply simp done  
  show goal785: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> dthdatas2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<noteq> [])  "
 apply simp done
  show goal786: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> HSTATE MA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> ((CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1)) "

 by (smt (verit) HOST_State.simps(250) HSTATE_invariant4 i201)
  show goal787: "((CSTATE SIAC (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingState Invalid (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> \<not> CSTATE IIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> GTS (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> HSTATE MA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> ((CSTATE IMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) \<and> nextHTDDataPending (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE IMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> CSTATE SMA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0)) "

 by (metis aux319_1 goal438)
  show goal788: "(HSTATE SD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []) "

 by (smt (verit) goal668 i201)
  show goal789: "(HSTATE SD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> snps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []) "

 by (smt (verit) goal669 i201)
  show goal790: "(HSTATE SD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []) "

 by (smt (verit) i220)
  show goal791: "(HSTATE SD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> reqresps2 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) = []) "

 by (smt (verit) i189 i1x nextDTHDataFrom_def nextDTHDataFrom_general_rule_11_0)


  show goal792: "(HSTATE ID (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 0 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) ) "

 by (metis goal672 i201)
  show goal793: "(HSTATE ID (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0) ) "

 by (metis goal673 i201)
  show goal794: "(CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> nextGOPendingIs GO_WritePull (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> HSTATE ID (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<or> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1)) "

 by (metis CSTATE_HostsModifiedRdOwn_otherside_invariant2 HostsModifiedRdOwn_nextGOPendingIs_otherside i1x i739)
  show goal795: "(CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> nextGOPendingIs GO_WritePull (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1 \<and> HSTATE ID (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> (\<not> CSTATE SIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<or> nextGOPendingIs GO_WritePullDrop (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0))  "

 by (metis HostsModifiedRdOwn_nextGOPendingIs_otherside i1x i590)

  show goal796: "(HSTATE SAD (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<and> nextDTHDataFrom 1 (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) \<longrightarrow> \<not> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 0 \<and> \<not> CSTATE MIA (  T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ]) 1) "

    by (smt (verit) goal150 i217)
qed
qed

lemma helper: "f T \<Longrightarrow>
 (\<And>T txid.
  f T \<and> HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<Longrightarrow>
  f ( T [ 1 +=snp SnpInv txid]  [ 5 sHost= MAD] [ 0 -=req ])) \<Longrightarrow>
 Lall
  (if HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0
   then [clearBuffer
 (let owner = (0 + 1) mod 2; requestor = 0
  in  T [ owner +=snp SnpInv nextReqID T requestor]  [ 5 sHost= MAD] [ requestor -=req ])]
   else [])
  f"
  by simp

lemma HostModifiedRdOwn'_coherent: shows "
SWMR_state_machine T \<Longrightarrow> Lall (HostModifiedRdOwn' T 0) SWMR_state_machine"
  unfolding HostModifiedRdOwn'_def sendSnoop_def
  apply(insert HostModifiedRdOwn'_coherent_aux_simpler)
  
  by (smt (verit) helper)




value "1::nat"


end
