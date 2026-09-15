theory HitSE_MDData
  imports "AllFixes.FixMDData" HitSE_Defs
begin

lemma HostMDData'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE MD T \<and> nextDTHDataFrom 0 T "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
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
have i1x: "HSTATE MD T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextDTHDataFrom 0 T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0"
by (insert h1 i1x i2x, simp)
have goal2: "HSTATE MA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostMDData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE MD T \<and> nextDTHDataFrom 0 T "
  shows "SWMR_HitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= ModifiedM] [ Dev1 -=d2hdHead ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE MD T \<and> nextDTHDataFrom 0 T" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE MD T \<and> nextDTHDataFrom 0 T "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostMDData'_coherent_aux_simpler[OF a] HostMDData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostMDData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostMDData' T 0) SWMR_HitSE
"
unfolding HostMDData'_def
unfolding copyInAndForwardData_def
using HostMDData'_SWHitSE_aux
by (smt (verit) Lall.simps(1) Lall.simps(2) One_nat_def add_0_left clearBuffer_def nat_to_id.simps(1) nat_to_id.simps(2) one_mod_two_eq_one)

lemma HostMDData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostMDData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostMDData'_SWHitSE[OF SWMR_HitSE_I]])

end
