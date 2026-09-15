theory HitSE_ISDSnpInv
  imports "AllFixes.FixISDSnpInv" HitSE_Defs
begin

lemma ISDSnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI])"
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
have i1x: "CSTATE ISD T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i00x: "CXL_SPG_used T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 0"
by (insert h1 h2 h3 h4 i1x i2x i00x, simp)
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 1"
by (insert h2 i1x i2x i00x, simp)
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 0"
by (insert h3 i1x i2x i00x, simp)
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI]) 1"
by (insert h4 i1x i2x i00x, simp)
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma ISDSnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= ISDI])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF ISDSnpInv'_coherent_aux_simpler[OF a] ISDSnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma ISDSnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (ISDSnpInv' T 0) SWMR_HitSE
"
unfolding ISDSnpInv'_def
unfolding sendSnpResp_def
apply(insert ISDSnpInv'_SWHitSE_aux)
using helper
by (metis CXL_SPG_used_general_rule_6_0 Lall.simps(1) Lall.simps(2) sendSnpResp_def)

lemma ISDSnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (ISDSnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF ISDSnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
