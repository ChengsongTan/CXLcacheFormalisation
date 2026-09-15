theory HitSE_ModifiedSnpInv
  imports "AllFixes.FixModifiedSnpInv" HitSE_Defs
begin

lemma ModifiedSnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])"
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
have i1x: "CSTATE Modified T 0 "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "CXL_SPG_used T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i61: "length (snps1 T) \<le> 1"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i473: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i598: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i843: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i920: "(CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i201: "\<not>nextSnoopPending (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [0 s= Invalid]) 0"
by (metis SharedSnpInv'_MAD_aux2_snoopNotInflight SharedSnpInv'_MAD_aux2_snoopNotInflight_invariant1 SharedSnpInv'_MAD_snps1_length i61 nextSnoopPending_def snoopNotInflight_empty)
have aux153: "HSTATE MAD (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid])"
by (metis hstate_invariants(12) hstate_invariants(2) hstate_invariants(24) hstate_invariants(7) i1x i201 i3x i473)
have goal1: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by (insert h1, (insert assms), (metis CSTATE_ModifiedSnpInv_otherside_invariant3 CXL_SPG_used_general_rule_8_0 HSTATE_invariant3 aux153 hstate_invariants(12) hstate_invariants(24) hstate_invariants(9) i1x i3x i473 i598 i843 i920))
have goal2: "HSTATE MA (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) \<and> nextSnpRespIs RspIHitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextHTDDataPending (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1"
by (insert h2 i1x i2x i3x, simp)
have goal3: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 0"
by (insert h3 i1x i2x i3x, simp)
have goal4: "CSTATE ISD (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd]) 1"
by (insert h4 i1x i2x i3x, simp)
show "HitSE_inv (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma ModifiedSnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE (T \<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIFwdM txid] [0 -=snp ] [ 0 s= Invalid] [ Dev1 +=d2hd dthd])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF ModifiedSnpInv'_coherent_aux_simpler[OF a] ModifiedSnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma ModifiedSnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (ModifiedSnpInv' T 0) SWMR_HitSE
"
unfolding ModifiedSnpInv'_def
unfolding sendSnpRespAndData_def clearBuffer_def
apply(insert ModifiedSnpInv'_SWHitSE_aux)
by (metis ModifiedSnpInv'_SWHitSE_aux SharedSnpInv'_CSTATE_invariant5 helper nat_to_id.simps(1))

lemma ModifiedSnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (ModifiedSnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF ModifiedSnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
