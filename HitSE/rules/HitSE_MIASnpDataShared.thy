theory HitSE_MIASnpDataShared
  imports "AllFixes.FixMIASnpDataShared" HitSE_Defs
begin

lemma MIASnpDataShared'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])"
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
have i1x: "CSTATE MIA T 0 "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "CXL_SPG_used T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "nextSnoopIs SnpData T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i481: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have aux153: "HSTATE SAD T"
by (smt (verit) i1x i3x i481)
have goal1: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0"
by (insert h1, (insert assms), (metis HOST_State.distinct(149) HOST_State.distinct(249) HSTATE_invariant4 HSTATE_rule_16 aux153 hstate_invariants(2)))
have goal2: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1"
by (insert h2 i1x i2x i3x, simp)
have goal3: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 0"
by (insert h3 i1x i2x i3x, simp)
have goal4: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd]) 1"
by (insert h4 i1x i2x i3x, simp)
show "HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma MIASnpDataShared'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspSFwdM txid] [0 -=snp ] [ 0 s= SIA] [ Dev1 +=d2hd dthd])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF MIASnpDataShared'_coherent_aux_simpler[OF a] MIASnpDataShared'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma MIASnpDataShared'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (MIASnpDataShared' T 0) SWMR_HitSE
"
unfolding MIASnpDataShared'_def
unfolding sendSnpRespAndData_def clearBuffer_def
apply(insert MIASnpDataShared'_SWHitSE_aux)
by (metis CXL_SPG_used_general_rule_8_0 Lall.simps(1) MIASnpDataShared'_SWHitSE_aux helper nat_to_id.simps(1))

lemma MIASnpDataShared'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (MIASnpDataShared' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF MIASnpDataShared'_SWHitSE[OF SWMR_HitSE_I]])

end
