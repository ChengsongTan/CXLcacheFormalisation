theory HitSE_MIASnpInv
  imports "AllFixes.FixMIASnpInv" HitSE_Defs
begin

lemma MIASnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])"
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
have i3x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i147: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i384: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i578: "(CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i584: "(CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i602: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i648: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have auxIIA_not_other_states: "\<not> CSTATE ISAD T 0 \<and> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0 \<and> \<not> nextHTDDataPending T 0"
by (smt (verit) i147 i1x i384 i3x i578 i584 i602 i648 nextHTDDataPending_def)
have goal1: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by (insert h1, (insert assms), (metis CSTATE_MIASnpInv_otherside_invariant3 CXL_SPG_used_general_rule_8_0 auxIIA_not_other_states nextHTDDataPending_general_rule_11_0))
have goal2: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1"
by (insert h2 i1x i2x i3x, simp)
have goal3: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 0"
by (insert h3 i1x i2x i3x, simp)
have goal4: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd]) 1"
by (insert h4 i1x i2x i3x, simp)
show "HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma MIASnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= IIA] [ Dev1 +=d2hd dthd])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF MIASnpInv'_coherent_aux_simpler[OF a] MIASnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma MIASnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (MIASnpInv' T 0) SWMR_HitSE
"
unfolding MIASnpInv'_def
unfolding sendSnpRespAndData_def clearBuffer_def
using MIASnpInv'_SWHitSE_aux
apply(simp only: nat_to_id.simps)
apply(simp only: HOL.simp_thms)
apply(rule SWMR_shape)
apply metis
by (metis MIASnpInv'_SWHitSE_aux)

lemma MIASnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (MIASnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF MIASnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
