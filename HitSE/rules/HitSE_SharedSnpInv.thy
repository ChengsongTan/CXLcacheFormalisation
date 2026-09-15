theory HitSE_SharedSnpInv
  imports "AllFixes.FixSharedSnpInv" HitSE_Defs
begin

lemma SharedSnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
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
have i2x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i50: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i59: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i383: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have aux153: "HSTATE MA (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
by (metis HSTATE_invariant_ModifiedSnpInv i1x i2x i383)
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 0"
by (insert h1, (insert assms), (metis CXL_SPG_used_general_rule_6_0 C_msg_P_same_def SharedSnpInv'_MA aux153 i1x i2x i50 i59 nextHTDDataPending_general_rule_8_0))
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SharedSnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SharedSnpInv'_coherent_aux_simpler[OF a] SharedSnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SharedSnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SharedSnpInv' T 0) SWMR_HitSE
"
unfolding SharedSnpInv'_def
unfolding sendSnpResp_def
apply(insert SharedSnpInv'_SWHitSE_aux)
using helper
by (metis SharedSnpInv'_SWHitSE_aux getSnoops_def)

lemma SharedSnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SharedSnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SharedSnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
