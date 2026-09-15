theory HitSE_ISDIData
  imports "AllFixes.FixISDIData" HitSE_Defs
begin

lemma ISDIData'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
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
have i77: "length (htddatas1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i221: " CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
using ISDIData_Shared
by blast
have g39aux: "htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
apply(insert i77)
by (metis htddatas1_empty_if_minus_rule_2_0 i77)
have g39aux1: "\<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
by (metis g39aux nextHTDDataPending_various_forms1)
have goal1: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
by (insert h1, (insert assms), (smt (verit) g39aux1))
have goal2: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
by (insert h2, (insert assms), (smt (verit) device_perform_op_nextHTDDataPending ISDIData_HSTATE i944 nextSnpRespIs_general_rule_7_0))
have goal3: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_different1 MESI_State.distinct(139) i221))
have goal4: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
by (insert h4, (insert assms), (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i401))
show "HitSE_inv ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma ISDIData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 "
  shows "SWMR_HitSE ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE ISDI T 0 \<and> nextHTDDataPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF ISDIData'_coherent_aux_simpler[OF a] ISDIData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma ISDIData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (ISDIData' T 0) SWMR_HitSE
"
unfolding ISDIData'_def copyInDataPerformInstr_def
using ISDIData'_SWHitSE_aux
by (metis Lall.simps(1) clearBuffer_def general_helper)

lemma ISDIData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (ISDIData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF ISDIData'_SWHitSE[OF SWMR_HitSE_I]])

end
