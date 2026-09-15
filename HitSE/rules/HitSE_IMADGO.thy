theory HitSE_IMADGO
  imports "AllFixes.FixIMADGO" HitSE_Defs
begin

lemma IMADGO'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE IMAD T 0 \<and> nextGOPending T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
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
have i1x: "CSTATE IMAD T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextGOPending T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
by (insert h1 i1x i2x, simp)
have goal2: "HSTATE MA ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) \<and> nextSnpRespIs RspIHitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma IMADGO'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE IMAD T 0 \<and> nextGOPending T 0"
  shows "SWMR_HitSE ( T \<lparr>buffer1 := Some m\<rparr> [ 0 s= IMD] [ 0 -=reqresp ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE IMAD T 0 \<and> nextGOPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE IMAD T 0 \<and> nextGOPending T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF IMADGO'_coherent_aux_simpler[OF a] IMADGO'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma IMADGO'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (IMADGO' T 0) SWMR_HitSE
"
unfolding IMADGO'_def consumeGO_def
apply(insert IMADGO'_SWHitSE_aux)
by (metis IMADGO'_CSTATE_sameside IMADGO_SWMR_shape Lall.simps(1) Lall.simps(2) consumeGO_def hstate_invariants(2))

lemma IMADGO'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (IMADGO' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF IMADGO'_SWHitSE[OF SWMR_HitSE_I]])

end
