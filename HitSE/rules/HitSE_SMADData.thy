theory HitSE_SMADData
  imports "AllFixes.FixSMADData" HitSE_Defs
begin

lemma SMADData'_HitSE_aux: assumes "SWMR_state_machine T \<and> CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
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
have i2x: "nextHTDDataPending T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 0"
by (insert h1 i1x i2x, auto)
have goal2: "HSTATE MA ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma SMADData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 "
  shows "SWMR_HitSE ( T [ 0 s= SMA] [ 0 :=dd msg ]  [ 0 -=devd ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF SMADData'_coherent_aux_simpler[OF a] SMADData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma SMADData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (SMADData' T 0) SWMR_HitSE
"
unfolding SMADData'_def
unfolding copyInData_def
apply (insert SMADData'_SWHitSE_aux Lall.simps(1) Lall.simps(2))
using helper
by (smt (verit))

lemma SMADData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (SMADData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF SMADData'_SWHitSE[OF SWMR_HitSE_I]])

end
