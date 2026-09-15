theory HitSE_SMADSnpInv
  imports "AllFixes.FixSMADSnpInv" HitSE_Defs
begin

lemma SMADSnpInv'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD])"
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
have i1x: "CSTATE SMAD T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextSnoopIs SnpInv T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i00x: "CXL_SPG_used T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i94: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i100: "(reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i390: "(CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i395: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i597: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i923: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have aux1531: "HSTATE MA T"
by (smt (verit) i00x i100 i1x i2x i390 i395 i94 reqs1_empty_not_nextReqIs_general_invariant)
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 0"
by (insert h1, (insert assms), (metis CSTATE_disj1 MESI_State.distinct(329) MESI_State.distinct(349) aux1531 i1x i2x i597 i923 nextHTDDataPending_general_rule_8_0))
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 1"
by (insert h2 i1x i2x i00x, simp)
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 0"
by (insert h3 i1x i2x i00x, simp)
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD]) 1"
by (insert h4 i1x i2x i00x, simp)
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SMADSnpInv'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= IMAD])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SMADSnpInv'_coherent_aux_simpler[OF a] SMADSnpInv'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SMADSnpInv'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SMADSnpInv' T 0) SWMR_HitSE
"
unfolding SMADSnpInv'_def
unfolding sendSnpResp_def
apply(insert SMADSnpInv'_SWHitSE_aux)
by (metis SMADSnpInv'_SWHitSE_aux SharedSnpInv'_CSTATE_invariant5 helper)

lemma SMADSnpInv'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SMADSnpInv' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SMADSnpInv'_SWHitSE[OF SWMR_HitSE_I]])

end
