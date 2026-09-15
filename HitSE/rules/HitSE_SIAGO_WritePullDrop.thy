theory HitSE_SIAGO_WritePullDrop
  imports "AllFixes.FixSIAGO_WritePullDrop" HitSE_Defs
begin

lemma SIAGO_WritePullDrop'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
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
have i2x: "nextGOPendingIs GO_WritePullDrop T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i326: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i207: "\<not> nextHTDDataPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
using htddatas1_SIAGO_WritePullDrop i1x i316 nextHTDDataPending_def
by presburger
have i208: "snps1 T = [] \<and> snps2 T = []"
using i1x i2x i316 i326
by force
have i209: "\<not> nextSnoopIs SnpInv ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]  [ -=i 0]) 0"
using empty_no_snoop i208 snps1_SIAGO_WritePullDrop
by presburger
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) = []"
using i208 snps2_SIAGO_WritePullDrop
by presburger
have i2160: "CSTATE Invalid (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have goal1: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i207))
have goal2: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis HSTATE_SIAGO_WritePullDrop_invariant SIAGO_WritePullDrop_nextHTDDataPending SIAGO_WritePullDrop_nextSnpRespIs_otherside hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i2160 i944 nextGOPendingIs_XYAGO_other1 remove_instr_HSTATE))
have goal3: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) i209))
have goal4: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) empty_no_snoop2 i214))
show "HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SIAGO_WritePullDrop'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 "
  shows "SWMR_HitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SIAGO_WritePullDrop'_coherent_aux_simpler[OF a] SIAGO_WritePullDrop'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SIAGO_WritePullDrop'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SIAGO_WritePullDrop' T 0) SWMR_HitSE
"
unfolding SIAGO_WritePullDrop'_def
apply(insert SIAGO_WritePullDrop'_SWHitSE_aux)
unfolding consumeGODiscard_def
by (metis Nat.add_0_right SIAGO_WritePullDrop'_SWHitSE_aux SharedSnpInv'_CSTATE_invariant5 add.commute add_0 helper one_mod_two_eq_one)

lemma SIAGO_WritePullDrop'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SIAGO_WritePullDrop' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SIAGO_WritePullDrop'_SWHitSE[OF SWMR_HitSE_I]])

end
