theory HitSE_IIAGO_WritePull
  imports "AllFixes.FixIIAGO_WritePull" HitSE_Defs
begin

lemma IIAGO_WritePull'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
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
have i1x: "CSTATE IIA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPendingIs GO_WritePull T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617old: "(CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i178: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i714: "(HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i715: "(HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i716: "(HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i207: "\<not> nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (metis HTDDataPending_htddatas_invariant1 htddatas1_IIAGO_WritePull htddatas1_remove_op i1x i617old)
have i208: "snps1 T = [] \<and> snps2 T = []"
by (smt (verit) i178 i1x i2x i617old i714 i715 i716)
have i209: "\<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using empty_no_snoop i208 snps1_IIAGO_WritePull
by presburger
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i208 snps2_IIAGO_WritePull
by presburger
have i2160: "CSTATE Invalid (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i207))
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis HSTATE_IIAGO_WritePull_invariant IIAGO_WritePull_nextSnpRespIs_otherside assms i2160 i617old nextGOPendingIs_general_rule_3_0 nextSnpRespIs_invariant2))
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) i209))
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) empty_no_snoop2 i214))
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma IIAGO_WritePull'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF IIAGO_WritePull'_coherent_aux_simpler[OF a] IIAGO_WritePull'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma IIAGO_WritePull'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (IIAGO_WritePull' T 0) SWMR_HitSE
"
unfolding IIAGO_WritePull'_def consumeGOSendData_def
apply(simp only: nat_to_id.simps)
apply(simp only: HOL.simp_thms(6) nat_to_id.simps if_True)
apply(insert IIAGO_WritePull'_SWHitSE_aux)
by (metis IIAGO_WritePull'_SWHitSE_aux helper)

lemma IIAGO_WritePull'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (IIAGO_WritePull' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF IIAGO_WritePull'_SWHitSE[OF SWMR_HitSE_I]])

end
