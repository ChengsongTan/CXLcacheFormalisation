theory HitSE_MARspIHitSE
  imports "AllFixes.FixMARspIHitSE" HitSE_Defs
begin

lemma HostMARspIHitSE'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> htddatas1 T = []"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
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
have i1x: "HSTATE MA T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextSnpRespIs RspIHitSE T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i00x: "GTS T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "htddatas1 T = []"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) \<and> nextSnpRespIs RspIHitSE ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0"
by (insert h1 i1x i2x i00x i3x, simp)
have goal2: "HSTATE MA ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) \<and> nextSnpRespIs RspIHitSE ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1"
by (insert h2 i1x i2x i00x i3x, simp)
have goal3: "CSTATE ISD ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 0"
by (insert h3 i1x i2x i00x i3x, simp)
have goal4: "CSTATE ISD ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ]) 1"
by (insert h4 i1x i2x i00x i3x, simp)
show "HitSE_inv ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostMARspIHitSE'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> htddatas1 T = []"
  shows "SWMR_HitSE ( T [ 1 +=reqresp GO Modified txid] [ 5 sHost= ModifiedM] [ 0 -=snpresp  ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> htddatas1 T = []" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> htddatas1 T = []"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostMARspIHitSE'_coherent_aux_simpler[OF a] HostMARspIHitSE'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostMARspIHitSE'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostMARspIHitSE' T 0) SWMR_HitSE
"
unfolding HostMARspIHitSE'_def not_nextHTDDataPending_0
unfolding sendGOFromSnpResp_def
apply(insert HostMARspIHitSE'_SWHitSE_aux)
by (metis HostMARspIHitSE'_SWHitSE_aux MARspIHitSE_helper Nat.add_0_right add.commute one_mod_two_eq_one plus_nat.add_0)

lemma HostMARspIHitSE'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostMARspIHitSE' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostMARspIHitSE'_SWHitSE[OF SWMR_HitSE_I]])

end
