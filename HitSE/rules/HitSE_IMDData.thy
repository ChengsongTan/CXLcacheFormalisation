theory HitSE_IMDData
  imports "AllFixes.FixIMDData" HitSE_Defs
begin

lemma IMDData'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
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
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i467: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i644: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i901: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i221: " CSTATE Modified ( T [ 0 s= Modified] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
by (smt (verit) IMDData_Modified)
have goal1: "HSTATE MA ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
by (insert h1, (insert assms), (smt (verit) IMDData_HSTATE assms i943 nextSnpRespIs_general_rule_7_0))
have goal2: "HSTATE MA ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
by (insert h2, (insert assms), (smt (verit) device_perform_op_nextHTDDataPending assms i644 i901))
have goal3: "CSTATE ISD ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_different1 MESI_State.distinct(7) i221))
have goal4: "CSTATE ISD ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
by (insert h4, (insert assms), (smt (verit) CSTATE_IMDData_otherside IMDData_HSTATE assms i401 i467))
show "HitSE_inv ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma IMDData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 "
  shows "SWMR_HitSE ( T [ 0 s= Modified] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF IMDData'_coherent_aux_simpler[OF a] IMDData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma IMDData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (IMDData' T 0) SWMR_HitSE
"
unfolding IMDData'_def
apply(insert  IMDData'_SWHitSE_aux )
by (smt (verit) IMDData_helper)

lemma IMDData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (IMDData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF IMDData'_SWHitSE[OF SWMR_HitSE_I]])

end
