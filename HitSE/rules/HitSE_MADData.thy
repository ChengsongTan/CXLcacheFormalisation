theory HitSE_MADData
  imports "AllFixes.FixMADData" HitSE_Defs
begin

lemma HostMADData'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE MAD T \<and> nextDTHDataFrom 0 T "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])"
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
have i1x: "HSTATE MAD T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextDTHDataFrom 0 T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i190: "(nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i428: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have aux_125: "snpresps2 T = []"
by (metis i1x i2x i428)
have goal1: "HSTATE MA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0"
by (insert h1, (insert assms), (smt (verit) assms i190 nextHTDDataPending_real_MADData))
have goal2: "HSTATE MA ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1"
by (insert h2, (insert assms), (smt (verit) HostMADData_nextSnpRespIs_otherside aux_125 nextSnpRespIs_invariant2))
have goal3: "CSTATE ISD ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostMADData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE MAD T \<and> nextDTHDataFrom 0 T "
  shows "SWMR_HitSE ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= MA] [ Dev1 -=d2hdHead ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE MAD T \<and> nextDTHDataFrom 0 T" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE MAD T \<and> nextDTHDataFrom 0 T "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostMADData'_coherent_aux_simpler[OF a] HostMADData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostMADData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostMADData' T 0) SWMR_HitSE
"
unfolding HostMADData'_def
unfolding copyInAndForwardData_def
apply(simp only: HOL.simp_thms(6) nat_to_id.simps if_True   )
apply(simp only: Groups.add_0)
apply(simp only: bits_one_mod_two_eq_one)
using HostMADData'_SWHitSE_aux
by (smt (verit) Lall.simps(1) Lall.simps(2) One_nat_def clearBuffer_def nat_to_id.simps(2))

lemma HostMADData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostMADData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostMADData'_SWHitSE[OF SWMR_HitSE_I]])

end
