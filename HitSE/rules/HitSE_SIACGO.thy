theory HitSE_SIACGO
  imports "AllFixes.FixSIACGO" HitSE_Defs
begin

lemma SIACGO'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> GTS T 1 \<and> saneSIACGO T 0"
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
have i1x: "CSTATE SIAC T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPendingIs GO T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i929: "(CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i204: "CSTATE Invalid ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
by (metis CSTATE_SIACGO_IMAD_invariant)
have i2160: "CSTATE Invalid (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have i216: "CSTATE Invalid ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ]  [ -=i 0]) 0"
using i204
by force
have goal1: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h1, (insert assms), (metis HTDDataPending_htddatas_invariant1 SIACGO_nextHTDDataPending htddatas1_SIACGO htddatas1_general_rule_12_0 i1x i2160 i929 nextGOPending_overlooked_reqresp_rule_4_0))
have goal2: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis SIACGO_nextHTDDataPending i119 i2160 i2x nextGOPending_overlooked_reqresp_rule_4_0 nextSnpRespIs_invariant2 reqresps_empty_noGOPendingIs1 snpresps2_SIACGO snpresps2_remove_op))
have goal3: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_different1 MESI_State.distinct(139) i216))
have goal4: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h4, (insert assms), (metis CSTATE_otherside_rule_4_0 CSTATE_remove_op hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i2160 i401 nextGOPending_overlooked_reqresp_rule_4_0 nextSnoopIs_SIACGO nextSnoopIs_general_rule_14_0 nextSnoopIs_general_rule_6_0 remove_instr_HSTATE))
show "HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SIACGO'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> GTS T 1 \<and> saneSIACGO T 0"
  shows "SWMR_HitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Invalid] [ 0 -=reqresp ] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> GTS T 1 \<and> saneSIACGO T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> GTS T 1 \<and> saneSIACGO T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SIACGO'_coherent_aux_simpler[OF a] SIACGO'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SIACGO'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SIACGO' T 0) SWMR_HitSE
"
unfolding SIACGO'_def
apply(insert SIACGO'_SWHitSE_aux)
using  general_helper helper
by (metis HOST_DEVNUM_def Lall.simps(1) Lall.simps(2) SIACGO'_SWHitSE_aux add_0 bits_one_mod_two_eq_one consumeGODiscard_def consumeGO_def one_add_one)

lemma SIACGO'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SIACGO' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SIACGO'_SWHitSE[OF SWMR_HitSE_I]])

end
