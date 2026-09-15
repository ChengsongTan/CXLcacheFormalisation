theory HitSE_ModifiedDirtyEvict
  imports "AllFixes.FixModifiedDirtyEvict" HitSE_Defs
begin

lemma HostModifiedDirtyEvict'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE MIA T 0 "
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
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
have i1x: "HSTATE ModifiedM T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextReqIs DirtyEvict T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by (insert h1 i1x i2x, simp)
have goal2: "HSTATE MA ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
by (insert h2 i1x i2x, simp)
have goal3: "CSTATE ISD ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 0"
by (insert h3 i1x i2x, simp)
have goal4: "CSTATE ISD ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ]) 1"
by (insert h4 i1x i2x, simp)
show "HitSE_inv ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostModifiedDirtyEvict'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE MIA T 0 "
  shows "SWMR_HitSE ( T [ 5 sHost= ID] [ 0 +=reqresp GO_WritePull Invalid txid] [ 0 -=req ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE MIA T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T 1 \<and> CSTATE MIA T 0 "
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostModified_DirtyEvict'_coherent_aux_simpler[OF a] HostModifiedDirtyEvict'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostModifiedDirtyEvict'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostModifiedDirtyEvict' T 0) SWMR_HitSE
"
unfolding HostModifiedDirtyEvict'_def
apply(insert HostModifiedDirtyEvict'_SWHitSE_aux)
by (metis HostModifiedDirtyEvict'_SWHitSE_aux helper one_mod_two_eq_one plus_nat.add_0 sendEvictResp_def)

lemma HostModifiedDirtyEvict'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostModifiedDirtyEvict' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostModifiedDirtyEvict'_SWHitSE[OF SWMR_HitSE_I]])

end
