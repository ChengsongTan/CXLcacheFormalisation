theory HitSE_SharedRdOwnSelf
  imports "AllFixes.FixSharedRdOwnSelf" HitSE_Defs
begin

lemma HostSharedRdOwnSelf'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Invalid T 1 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ])"
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
(* the goal proofs cite no have block of HostSharedRdOwnSelf'_coherent_aux_simpler *)
have goal1: "HSTATE MA (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0"
by (insert h1, simp)
have goal2: "HSTATE MA (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1"
by (insert h2, simp)
have goal3: "CSTATE ISD (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 0"
by (insert h3, simp)
have goal4: "CSTATE ISD (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ]) 1"
by (insert h4, simp)
show "HitSE_inv (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostSharedRdOwnSelf'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Invalid T 1 "
  shows "SWMR_HitSE (T [ 0 +=hostdata  txid] [ 5 sHost= ModifiedM] [ 0 +=reqresp GO mesi txid] [ 0 -=req ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Invalid T 1" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<and> CSTATE Invalid T 1 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostSharedRdOwnSelf'_coherent_aux_simpler[OF a] HostSharedRdOwnSelf'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostSharedRdOwnSelf'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostSharedRdOwnSelf' T 0) SWMR_HitSE
"
unfolding HostSharedRdOwnSelf'_def
unfolding noInvalidateSharers_def clearBuffer_def sendHostDataGO_def
using HostSharedRdOwnSelf'_SWHitSE_aux
by (smt (verit) Lall.simps(1) Lall.simps(2) add_diff_inverse_nat add_implies_diff diff_is_0_eq' le_numeral_extra(4) not_one_less_zero one_mod_two_eq_one ordered_cancel_comm_monoid_diff_class.diff_diff_right)

lemma HostSharedRdOwnSelf'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostSharedRdOwnSelf' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostSharedRdOwnSelf'_SWHitSE[OF SWMR_HitSE_I]])

end
