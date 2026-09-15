theory HitSE_SharedLoad
  imports "AllFixes.FixSharedLoad" HitSE_Defs
begin

lemma SharedLoad'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE Shared T 0 \<and> nextLoad T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv (T [ -=i 0])"
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
have i1x: "CSTATE Shared T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i201: "\<forall>X j. CSTATE X T j = CSTATE X (T [ -=i 0])  j"
using CSTATE_remove_op
by blast
have i202: "\<forall>X. HSTATE X T  = HSTATE X (T [ -=i 0])"
using remove_instr_HSTATE
by presburger
have i205: "CSTATE Shared (T [ -=i 0]) 0"
by (metis i1x i201)
have goal1: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIHitSE (T [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i202 i943 nextHTDDataPending_general_rule_12_0 nextSnpRespIs_general_rule_13_0))
have goal2: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIHitSE (T [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
by (insert h2, (insert assms), (metis i944 nextHTDDataPending_remove_op nextSnpRespIs_remove_op remove_instr_HSTATE))
have goal3: "CSTATE ISD (T [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_disj1 MESI_State.distinct(97) i205))
have goal4: "CSTATE ISD (T [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) i201 i202 i401 nextSnoopIs_general_rule_14_0))
show "HitSE_inv (T [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SharedLoad'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE Shared T 0 \<and> nextLoad T 0 "
  shows "SWMR_HitSE (T [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE Shared T 0 \<and> nextLoad T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE Shared T 0 \<and> nextLoad T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SharedLoad'_coherent_aux_simpler[OF a] SharedLoad'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SharedLoad'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SharedLoad' T 0) SWMR_HitSE
"
unfolding SharedLoad'_def clearBuffer_def
by (metis Lall.simps(1) Lall.simps(2) SharedLoad'_SWHitSE_aux)

lemma SharedLoad'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SharedLoad' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SharedLoad'_SWHitSE[OF SWMR_HitSE_I]])

end
