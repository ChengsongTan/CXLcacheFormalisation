theory HitSE_SMAGO
  imports "AllFixes.FixSMAGO" HitSE_Defs
begin

lemma SMAGO'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE SMA T 0 \<and> nextGOPending T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
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
have i1x: "CSTATE SMA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPending T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i370: "(CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i202: "nextStore T 0"
using i1x i370
by blast
have i204: "CSTATE Modified ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0"
using CSTATE_SMAGO_IMAD_invariant i202
by blast
have aux207: " \<not> nextHTDDataPending T 0"
using i1x i352
by blast
have i207: "\<not> nextHTDDataPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0"
apply simp
using aux207 i202 startsStore.elims(2)
by force
have i208: " snps2 T = []"
apply (smt (verit) i2x i55 reqresps_empty_noGOPending1)
done
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) = []"
using i208 snps2_SMAGO
by presburger
have i2160: "CSTATE Modified (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have i216: "CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]  [ -=i 0]) 0"
using i204
by force
\<comment>\<open>
  have i217: "\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 " 
 using CSTATE_def MESI_State.simps(6) i216 by presburger
  have i218: "HSTATE ModifiedM T \<longrightarrow> \<not> nextReqIs RdShared T 1"
 using i1x i41 by simp
  have i219: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]  [ -=i 0]) \<longrightarrow>\<not>nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ]  [ -=i 0]) 1"
 
 
 using HSTATE_SMAGO_invariant i218 reqs2_SMAGO by auto

\<close>
have goal1: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i207))
have goal2: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis assms i119 i2160 nextGOPending_yes_reqresp_rule_4_1 nextReqIs_SMAGO nextSnpRespIs_property2 reqresps_empty_noGOPending1 snpresps2_SMAGO snpresps2_remove_op))
have goal3: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_different1 MESI_State.distinct(7) i216))
have goal4: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) empty_no_snoop_variant2 i214))
show "HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SMAGO'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE SMA T 0 \<and> nextGOPending T 0 "
  shows "SWMR_HitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Modified] [ 0 -=reqresp ] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SMA T 0 \<and> nextGOPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE SMA T 0 \<and> nextGOPending T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SMAGO'_coherent_aux_simpler[OF a] SMAGO'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SMAGO'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SMAGO' T 0) SWMR_HitSE
"
apply(insert SMAGO'_SWHitSE_aux)
unfolding SMAGO'_def consumeGOPerform_def
by (metis SMAGO'_SWHitSE_aux SMAGO_SWMR_shape)

lemma SMAGO'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SMAGO' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SMAGO'_SWHitSE[OF SWMR_HitSE_I]])

end
