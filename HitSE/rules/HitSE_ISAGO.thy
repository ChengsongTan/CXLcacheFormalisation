theory HitSE_ISAGO
  imports "AllFixes.FixISAGO" HitSE_Defs
begin

lemma ISAGO'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE ISA T 0 \<and> nextGOPending T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
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
have i1x: "CSTATE ISA T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPending T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i368: "(CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i750: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i202: "nextLoad T 0"
using i1x i368
by blast
have i204: "CSTATE Shared ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0"
using CSTATE_ISAGO_IMAD_invariant i202
by blast
have aux207: " \<not> nextHTDDataPending T 0"
using i1x i352
by blast
have i207: "\<not> nextHTDDataPending  ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0"
using ISAGO_nextHTDDataPending_sameside aux207
by blast
have i208: " snps2 T = []"
by (metis i2x i55 reqresps_empty_noGOPending1)
have i214: " snps2 ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) = []"
using i208 snps2_ISAGO
by presburger
have i2160: "CSTATE Shared (T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared]) 0"
using SharedSnpInv'_CSTATE_invariant5
by presburger
have i216: "CSTATE Shared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]  [ -=i 0]) 0"
using i204
by force
\<comment>\<open>
  have i217: "\<not> CSTATE Modified ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 " 
 using CSTATE_def MESI_State.simps(6) i216 by presburger
  have i218: "HSTATE ModifiedM T \<longrightarrow> \<not> nextReqIs RdShared T 1"
 using i1x i41 by simp
  have i219: "HSTATE ModifiedM ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]  [ -=i 0]) \<longrightarrow>\<not>nextReqIs RdShared ( T\<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ]  [ -=i 0]) 1"
 
 
 using HSTATE_ISAGO_invariant i218 reqs2_ISAGO by auto

\<close>
have goal1: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h1, (insert assms), (smt (verit) i207))
have goal2: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h2, (insert assms), (metis ISAGO_nextSnpRespIs_otherside assms hstate_invariants(14) hstate_invariants(2) hstate_invariants(24) i2160 i750 nextGOPending_yes_reqresp_rule_4_1 nextReqIs_ISAGO nextSnpRespIs_property2 remove_instr_HSTATE))
have goal3: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 0"
by (insert h3, (insert assms), (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(97) i216))
have goal4: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0]) 1"
by (insert h4, (insert assms), (smt (verit) empty_no_snoop_variant2 i214))
show "HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma ISAGO'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE ISA T 0 \<and> nextGOPending T 0 "
  shows "SWMR_HitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE ISA T 0 \<and> nextGOPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE ISA T 0 \<and> nextGOPending T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF ISAGO'_coherent_aux_simpler[OF a] ISAGO'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma ISAGO'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (ISAGO' T 0) SWMR_HitSE
"
unfolding ISAGO'_def consumeGOPerform_def
apply(case_tac "CSTATE ISA T 0 \<and> nextGOPending T 0")
apply(subgoal_tac "SWMR_HitSE (T\<lparr>buffer1 := Some (nextGO T 0)\<rparr> [ 0 s= Shared] [ 0 -=reqresp ] [ -=i 0])")
apply(simp only: HOL.if_True HOL.simp_thms(6) HOL.simp_thms(21))
subgoal
apply (induct arbitrary: T)
apply ( metis Lall.simps ( 2 ) )
done
subgoal
apply (induct T)
using ISAGO'_SWHitSE_aux
apply blast
done
apply(simp only: if_False)
subgoal
using Lall.simps(1)
apply blast
done
done

lemma ISAGO'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (ISAGO' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF ISAGO'_SWHitSE[OF SWMR_HitSE_I]])

end
