theory HitSE_SBData
  imports "AllFixes.FixSBData" HitSE_Defs
begin

lemma HostSBData'_HitSE_aux: assumes "SWMR_state_machine T \<and> HSTATE SB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0"
  shows "HitSE_inv T \<Longrightarrow> HitSE_inv ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
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
have i1x: "HSTATE SB T "
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextDTHDataFrom 0 T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3x: "CSTATE Invalid T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have goal1: "HSTATE MA ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0"
by (insert h1 i1x i2x i3x, simp)
have goal2: "HSTATE MA ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) \<and> nextSnpRespIs RspIHitSE ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1"
by (insert h2 i1x i2x i3x, simp)
have goal3: "CSTATE ISD ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 0"
by (insert h3 i1x i2x i3x, simp)
have goal4: "CSTATE ISD ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ]) 1"
by (insert h4 i1x i2x i3x, simp)
show "HitSE_inv ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
  unfolding HitSE_inv_def by (rule conjI[OF goal1 conjI[OF goal2 conjI[OF goal3 goal4]]])
qed

lemma HostSBData'_SWHitSE_aux: assumes "SWMR_HitSE T \<and> HSTATE SB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0"
  shows "SWMR_HitSE ( T [ 5 sHost= SharedM] [ Dev1 -=d2hdHead ])"
proof -
  have sh: "SWMR_HitSE T" using assms by (rule conjunct1)
  have g: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0" using assms by (rule conjunct2)
  have a: "SWMR_state_machine T \<and> HSTATE SB T \<and> nextDTHDataFrom 0 T \<and> CSTATE Invalid T 0"
    by (rule conjI[OF SWMR_HitSE_D1[OF sh] g])
  show ?thesis
    by (rule SWMR_HitSE_I[OF HostSBData'_coherent_aux_simpler[OF a] HostSBData'_HitSE_aux[OF a SWMR_HitSE_D2[OF sh]]])
qed

lemma HostSBData'_SWHitSE: shows "
SWMR_HitSE T \<Longrightarrow> Lall (HostSBData' T 0) SWMR_HitSE"
unfolding HostSBData'_def copyInDataHost_def discardDataHost_def
using HostSBData'_SWHitSE_aux shape_help_SBData
by presburger

lemma HostSBData'_HitSE: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> Lall (HostSBData' T 0) HitSE_inv"
  by (rule Lall_SWMR_HitSE_D2[OF HostSBData'_SWHitSE[OF SWMR_HitSE_I]])

end
