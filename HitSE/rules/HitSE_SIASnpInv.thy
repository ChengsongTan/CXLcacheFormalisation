theory HitSE_SIASnpInv
  imports "AllFixes.FixSIASnpInv" HitSE_Defs
begin

lemma SIASnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<and> \<not> nextReqIs DirtyEvict T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA])"
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
have i1x: "CSTATE SIA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "\<not> nextReqIs DirtyEvict T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i00x: "CXL_SPG_used T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i503: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have aux1531: "HSTATE MA T"
by (metis i1x i2x i503)
have aux153: "HSTATE MA (T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [0 s= IIA])"
apply simp
using aux1531
by auto
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 0"
by (insert h1, (insert assms), (metis HTDDataPending_htddatas_invariant1 aux153 i1x i316 nextHTDDataPending_general_rule_8_0))
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 1"
by (insert h2 i1x i2x i3x i00x, simp)
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 0"
by (insert h3 i1x i2x i3x i00x, simp)
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA]) 1"
by (insert h4 i1x i2x i3x i00x, simp)
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SIASnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<and> \<not> nextReqIs DirtyEvict T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IIA])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<and> \<not> nextReqIs DirtyEvict T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<and> \<not> nextReqIs DirtyEvict T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SIASnpInv'_coherent_aux_simpler[OF a] SIASnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SIASnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SIASnpInv' T 0) SWMR_HitSE
"
unfolding SIASnpInv'_def
unfolding sendSnpResp_def
apply(insert SIASnpInv'_SWHitSE_aux)
by (metis Lall.simps(1) Lall.simps(2) SIASnpInv_helper SIASnpInv_nextReqIs sendSnpResp_def)

lemma SIASnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SIASnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SIASnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
