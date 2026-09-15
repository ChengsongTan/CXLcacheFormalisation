theory HitSE_SharedRdOwn
  imports "AllFixes.FixSharedRdOwn" HitSE_Defs
begin

lemma HostSharedRdOwn'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Shared T 1 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ])"
proof -
assume hi: "HitSE_inv T"
have h1: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
by (insert hi, unfold HitSE_inv_def, elim conjE, assumption)
have h2: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
by (insert hi, unfold HitSE_inv_def, elim conjE, assumption)
have h3: "CSTATE ISD T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0"
by (insert hi, unfold HitSE_inv_def, elim conjE, assumption)
have h4: "CSTATE ISD T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1"
by (insert hi, unfold HitSE_inv_def, elim conjE, assumption)
have i1x: "HSTATE SharedM T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i000x: "CSTATE Shared T 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextReqIs RdOwn T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616old: "(CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i98: "(reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i212: "snpresps2 T = []"
using assms empty_reqs_nextReqIs i98
by blast
have i214: " snpresps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) = [] "
using i212
using snpresps2_HostSharedRdOwn
by presburger
have goal1: "HSTATE MA ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0"
by (insert h1, (insert assms), (smt (verit) i000x i616old nextSnpRespIs_general_rule_15_0 nextSnpRespIs_property1))
have goal2: "HSTATE MA ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1"
by (insert h2, (insert assms), (smt (verit) i214 nextSnpRespIs_invariant2))
have goal3: "CSTATE ISD ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 0"
by (insert h3 i1x i000x i2x, simp)
have goal4: "CSTATE ISD ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ]) 1"
by (insert h4 i1x i000x i2x, simp)
show "HitSE_inv ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostSharedRdOwn'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Shared T 1 "
  shows "SWMR_HitSE ( T [ 0 +=hostdata  txid] [ 5 sHost= MA] [ 1 +=snp SnpInv txid]  [ 0 -=req ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Shared T 1" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Shared T 1 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostSharedRdOwn'_coherent_aux_simpler[OF a] HostSharedRdOwn'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostSharedRdOwn'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostSharedRdOwn' T 0) SWMR_HitSE
"
unfolding HostSharedRdOwn'_def
unfolding invalidateSharers_def clearBuffer_def
using HostSharedRdOwn'_SWHitSE_aux
by (smt (verit, del_insts) Lall.simps(1) Lall.simps(2) add_cancel_left_left one_mod_two_eq_one sendHostData_def)

lemma HostSharedRdOwn'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostSharedRdOwn' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostSharedRdOwn'_SWHitSE[OF SWMR_HitSE_I]])

end
