theory HitSE_InvalidLoad
  imports "AllFixes.FixInvalidLoad" HitSE_Defs
begin

lemma InvalidLoad'_HitSE_aux: assumes "SWMR_state_machine T \<and>  CSTATE Invalid T 0 \<and> nextLoad T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])"
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
have i1x: "CSTATE Invalid T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextLoad T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 0"
by (insert h1 i1x i2x, simp)
have goal2: "HSTATE MA ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma InvalidLoad'_SWHitSE_aux: assumes "SWMR_HitSE T \<and>  CSTATE Invalid T 0 \<and> nextLoad T 0"
  shows "SWMR_HitSE ( T [ 0 +=rdreq RdShared] [ 0 s= ISAD])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "CSTATE Invalid T 0 \<and> nextLoad T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and>  CSTATE Invalid T 0 \<and> nextLoad T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF InvalidLoad'_coherent_aux_simpler[OF a] InvalidLoad'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma InvalidLoad'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (InvalidLoad' T 0) SWMR_HitSE
"
unfolding InvalidLoad'_def sendReq_def
apply(insert InvalidLoad'_SWHitSE_aux)
by (smt (verit) helper)

lemma InvalidLoad'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (InvalidLoad' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF InvalidLoad'_SWHitSE[OF SWMR_HitSE_I]])

end
