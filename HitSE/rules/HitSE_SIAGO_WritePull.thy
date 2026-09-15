theory HitSE_SIAGO_WritePull
  imports "AllFixes.FixSIAGO_WritePull" HitSE_Defs
begin

lemma SIAGO_WritePull'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
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
have i1x: "CSTATE SIA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i318: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i207: "\<not> nextHTDDataPending  ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using htddatas1_SIAGO_WritePull
using i1x i316 nextHTDDataPending_def
by presburger
have i208: "snps1 T = [] \<and> snps2 T = []"
by (metis C_msg_P_same_def assms i318 i316 nextSnoopPending_def)
have i209: "\<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
using empty_no_snoop i208 snps1_SIAGO_WritePull
by presburger
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
using i208 snps2_SIAGO_WritePull
by presburger
have i2160: "CSTATE Invalid (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have goal1: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i207))
have goal2: "HSTATE MA ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis HSTATE_SIAGO_WritePull_invariant SIAGO_WritePull_nextHTDDataPending_real SIAGO_WritePull_nextSnpRespIs_otherside hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) hstate_invariants(9) i2160 i944 nextGOPendingIs_general_rule_3_0 remove_instr_HSTATE))
have goal3: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) i209))
have goal4: "CSTATE ISD ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) empty_no_snoop2 i214))
show "HitSE_inv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SIAGO_WritePull'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
  shows "SWMR_HitSE ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SIAGO_WritePull'_coherent_aux_simpler[OF a] SIAGO_WritePull'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SIAGO_WritePull'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SIAGO_WritePull' T 0) SWMR_HitSE
"
unfolding SIAGO_WritePull'_def consumeGOSendData_def
apply(insert SIAGO_WritePull'_SWHitSE_aux)
using general_helper
by (metis SIAGO_WritePull'_SWHitSE_aux SIAGO_WritePull_helper)

lemma SIAGO_WritePull'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SIAGO_WritePull' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SIAGO_WritePull'_SWHitSE[OF SWMR_HitSE_I]])

end
