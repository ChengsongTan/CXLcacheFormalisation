theory HitSE_IDData
  imports "AllFixes.FixIDData" HitSE_Defs
begin

lemma HostIDData'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE ID T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> (CSTATE IIA T 1 \<or> CSTATE Invalid T 1 \<or> CSTATE SIA T 1) "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
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
have i1x: "HSTATE ID T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextDTHDataFrom 0 T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i6x: " CSTATE Invalid T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i7x: "(CSTATE IIA T 1 \<or> CSTATE Invalid T 1 \<or> CSTATE SIA T 1)"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0"
by (insert h1 i1x i2x i6x i7x, simp)
have goal2: "HSTATE MA ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1"
by (insert h2 i1x i2x i6x i7x, simp)
have goal3: "CSTATE ISD ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 0"
by (insert h3 i1x i2x i6x i7x, simp)
have goal4: "CSTATE ISD ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ]) 1"
by (insert h4 i1x i2x i6x i7x, simp)
show "HitSE_inv ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostIDData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE ID T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> (CSTATE IIA T 1 \<or> CSTATE Invalid T 1 \<or> CSTATE SIA T 1) "
  shows "SWMR_HitSE ( T [ =hv v] [ 5 sHost= InvalidM] [ Dev1 -=d2hdHead ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> (CSTATE IIA T 1 \<or> CSTATE Invalid T 1 \<or> CSTATE SIA T 1)" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE ID T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0 \<and> (CSTATE IIA T 1 \<or> CSTATE Invalid T 1 \<or> CSTATE SIA T 1) "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostIDData'_coherent_aux_simpler[OF a] HostIDData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostIDData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostIDData' T 0) SWMR_HitSE"
unfolding HostIDData'_def copyInDataHost_def
apply(insert HostIDData'_SWHitSE_aux)
by (metis HostIDData'_SWHitSE_aux helper nat_to_id.simps(1))

lemma HostIDData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostIDData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostIDData'_SWHitSE[OF SWMR_HitSE_I]])

end
