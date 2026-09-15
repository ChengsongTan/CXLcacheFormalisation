theory HitSE_Reach
  imports "AllFixes.TopLevelTheorem"
    "HitSE_Rules.HitSE_InvalidLoad"
    "HitSE_Rules.HitSE_SharedLoad"
    "HitSE_Rules.HitSE_InvalidStore"
    "HitSE_Rules.HitSE_SharedStore"
    "HitSE_Rules.HitSE_SharedEvict"
    "HitSE_Rules.HitSE_SharedEvictData"
    "HitSE_Rules.HitSE_ModifiedEvict"
    "HitSE_Rules.HitSE_SharedSnpInv"
    "HitSE_Rules.HitSE_ISDSnpInv"
    "HitSE_Rules.HitSE_ISDData"
    "HitSE_Rules.HitSE_ISDIData"
    "HitSE_Rules.HitSE_IMADData"
    "HitSE_Rules.HitSE_SMADData"
    "HitSE_Rules.HitSE_IMADGO"
    "HitSE_Rules.HitSE_ISADGO"
    "HitSE_Rules.HitSE_ISADData"
    "HitSE_Rules.HitSE_SMADGO"
    "HitSE_Rules.HitSE_SMAGO"
    "HitSE_Rules.HitSE_SMADSnpInv"
    "HitSE_Rules.HitSE_SMDData"
    "HitSE_Rules.HitSE_IMAGO"
    "HitSE_Rules.HitSE_ISAGO"
    "HitSE_Rules.HitSE_ModifiedStore"
    "HitSE_Rules.HitSE_ModifiedLoad"
    "HitSE_Rules.HitSE_SIAGO_WritePull"
    "HitSE_Rules.HitSE_SIAGO_WritePullDrop"
    "HitSE_Rules.HitSE_IIAGO_WritePullDrop"
    "HitSE_Rules.HitSE_IIAGO_WritePull"
    "HitSE_Rules.HitSE_IMDData"
    "HitSE_Rules.HitSE_MIASnpDataInvalid"
    "HitSE_Rules.HitSE_MIASnpDataShared"
    "HitSE_Rules.HitSE_MIASnpInv"
    "HitSE_Rules.HitSE_MIAGO_WritePull"
    "HitSE_Rules.HitSE_SIASnpInv"
    "HitSE_Rules.HitSE_ModifiedSnpInv"
    "HitSE_Rules.HitSE_ModifiedSnpDataShared"
    "HitSE_Rules.HitSE_ModifiedSnpDataInvalid"
    "HitSE_Rules.HitSE_InvalidRdShared"
    "HitSE_Rules.HitSE_InvalidRdOwn"
    "HitSE_Rules.HitSE_SharedRdShared"
    "HitSE_Rules.HitSE_Shared_CleanEvict_NotLastDrop"
    "HitSE_Rules.HitSE_Shared_CleanEvict_NotLastData"
    "HitSE_Rules.HitSE_Shared_CleanEvict_Last"
    "HitSE_Rules.HitSE_Shared_CleanEvictNoData_NotLast"
    "HitSE_Rules.HitSE_Shared_CleanEvictNoData_Last"
    "HitSE_Rules.HitSE_SharedDirtyEvict"
    "HitSE_Rules.HitSE_ModifiedDirtyEvict"
    "HitSE_Rules.HitSE_ModifiedRdShared"
    "HitSE_Rules.HitSE_ModifiedRdOwn"
    "HitSE_Rules.HitSE_SharedRdOwn"
    "HitSE_Rules.HitSE_SharedRdOwnSelf"
    "HitSE_Rules.HitSE_SDData"
    "HitSE_Rules.HitSE_SADData"
    "HitSE_Rules.HitSE_MDData"
    "HitSE_Rules.HitSE_IDData"
    "HitSE_Rules.HitSE_MADData"
    "HitSE_Rules.HitSE_SADRspIFwdM"
    "HitSE_Rules.HitSE_SADRspSFwdM"
    "HitSE_Rules.HitSE_MADRspIFwdM"
    "HitSE_Rules.HitSE_MARspIFwdM"
    "HitSE_Rules.HitSE_SARspIFwdM"
    "HitSE_Rules.HitSE_SARspSFwdM"
    "HitSE_Rules.HitSE_IBData"
    "HitSE_Rules.HitSE_SBData"
    "HitSE_Rules.HitSE_MBData"
    "HitSE_Rules.HitSE_InvalidDirtyEvict"
    "HitSE_Rules.HitSE_MARspIHitSE"
    "HitSE_Rules.HitSE_SIACGO"
begin

text \<open>HitSE_inv holds initially and is preserved by every transition of either device from a state that
  also satisfies SWMR_state_machine, so it holds in every reachable state. The induction takes SWMR_state_machine
  of the intermediate state from SWMR_state_machine_CXL_cache.\<close>

lemma HitSE_inv_initial: assumes "initial_state T" shows "HitSE_inv T"
proof -
  have h: "HSTATE InvalidM T" by (insert assms; unfold initial_state_def; elim conjE; assumption)
  have c0: "CSTATE Invalid T 0" by (insert assms; unfold initial_state_def; elim conjE; assumption)
  have c1: "CSTATE Invalid T 1" by (insert assms; unfold initial_state_def; elim conjE; assumption)
  show ?thesis unfolding HitSE_inv_def using h c0 c1 by simp
qed

lemma HitSE_inv_toggle: "HitSE_inv (toggle T) = HitSE_inv T"
  unfolding HitSE_inv_def HSTATE_toggle CSTATE_toggle0 CSTATE_toggle1
    nextSnpRespIs_toggle0 nextSnpRespIs_toggle1 nextHTDDataPending_toggle0 nextHTDDataPending_toggle1
    nextSnoopIs_toggle0 nextSnoopIs_toggle1
  by blast

lemmas HitSE_rule_lemmas =
  InvalidLoad'_HitSE SharedLoad'_HitSE InvalidStore'_HitSE SharedStore'_HitSE
  SharedEvict'_HitSE SharedEvictData'_HitSE ModifiedEvict'_HitSE SharedSnpInv'_HitSE
  ISDSnpInv'_HitSE ISDData'_HitSE ISDIData'_HitSE IMADData'_HitSE
  SMADData'_HitSE IMADGO'_HitSE ISADGO'_HitSE ISADData'_HitSE
  SMADGO'_HitSE SMAGO'_HitSE SMADSnpInv'_HitSE SMDData'_HitSE
  IMAGO'_HitSE ISAGO'_HitSE ModifiedStore'_HitSE ModifiedLoad'_HitSE
  SIAGO_WritePull'_HitSE SIAGO_WritePullDrop'_HitSE IIAGO_WritePullDrop'_HitSE IIAGO_WritePull'_HitSE
  IMDData'_HitSE MIASnpDataInvalid'_HitSE MIASnpDataShared'_HitSE MIASnpInv'_HitSE
  MIAGO_WritePull'_HitSE SIASnpInv'_HitSE ModifiedSnpInv'_HitSE ModifiedSnpDataShared'_HitSE
  ModifiedSnpDataInvalid'_HitSE HostInvalidRdShared'_HitSE HostInvalidRdOwn'_HitSE HostSharedRdShared'_HitSE
  HostShared_CleanEvict_NotLastDrop'_HitSE HostShared_CleanEvict_NotLastData'_HitSE HostShared_CleanEvict_Last'_HitSE HostShared_CleanEvictNoData_NotLast'_HitSE
  HostShared_CleanEvictNoData_Last'_HitSE HostShared_DirtyEvict'_HitSE HostModifiedDirtyEvict'_HitSE HostModifiedRdShared'_HitSE
  HostModifiedRdOwn'_HitSE HostSharedRdOwn'_HitSE HostSharedRdOwnSelf'_HitSE HostSDData'_HitSE
  HostSADData'_HitSE HostMDData'_HitSE HostIDData'_HitSE HostMADData'_HitSE
  HostSADRspIFwdM'_HitSE HostSADRspSFwdM'_HitSE HostMADRspIFwdM'_HitSE HostMARspIFwdM'_HitSE
  HostSARspIFwdM'_HitSE HostSARspSFwdM'_HitSE HostIBDataPrevious'_HitSE HostSBData'_HitSE
  HostMBData'_HitSE HostInvalidDirtyEvict'_HitSE HostMARspIHitSE'_HitSE SIACGO'_HitSE

theorem HitSE_transitions:
  assumes "SWMR_state_machine T" "HitSE_inv T"
  shows "\<forall>T'\<in>set (List.concat (List.map (\<lambda>f. f T 0) allTransitions')). HitSE_inv T'"
  unfolding allTransitions'_def my_map_concat my_set_concat_split_66elems
  apply (simp only: Ball_Lall)
  apply (intro conjI)
  by (rule HitSE_rule_lemmas[OF assms])+

theorem HitSE_transitions_dev2:
  assumes "SWMR_state_machine T" "HitSE_inv T"
  shows "\<forall>T'\<in>set (List.concat (List.map (\<lambda>f. f T 1) allTransitions')). HitSE_inv T'"
proof
  fix T' assume "T' \<in> set (List.concat (List.map (\<lambda>f. f T 1) allTransitions'))"
  then obtain T'' where T'': "T'' \<in> set (List.concat (List.map (\<lambda>f. f (toggle T) 0) allTransitions'))"
    and T'_eq: "T' = toggle T''"
    by (auto simp only: allTransitions'_toggle set_map image_iff)
  have sw: "SWMR_state_machine (toggle T)" using assms(1) by (rule symmetry)
  have p: "HitSE_inv (toggle T)" using assms(2) unfolding HitSE_inv_toggle .
  have "HitSE_inv T''" using HitSE_transitions[OF sw p] T'' by blast
  then show "HitSE_inv T'" unfolding T'_eq HitSE_inv_toggle .
qed

theorem HitSE_transitions_both:
  assumes "SWMR_state_machine T" "HitSE_inv T"
  shows "\<forall>T'\<in>set (concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions')). HitSE_inv T'"
  using HitSE_transitions[OF assms] HitSE_transitions_dev2[OF assms]
  unfolding set_concat_both by blast

theorem HitSE_inv_CXL_cache:
  assumes "allTransStar T T'" and "initial_state T" shows "HitSE_inv T'"
  using assms
proof (induct rule: allTransStar.induct)
  case (refl T)
  then show ?case by (rule HitSE_inv_initial)
next
  case (step T T' T'')
  from step have reach: "allTransStar T T'" and init: "initial_state T" by blast+
  have sw: "SWMR_state_machine T'" by (rule SWMR_state_machine_CXL_cache[OF reach init])
  from step init have p: "HitSE_inv T'" by blast
  from step show ?case using HitSE_transitions_both[OF sw p] by blast
qed

corollary SWMR_HitSE_CXL_cache:
  assumes "allTransStar T T'" "initial_state T" shows "SWMR_HitSE T'"
  by (rule SWMR_HitSE_I[OF SWMR_state_machine_CXL_cache[OF assms] HitSE_inv_CXL_cache[OF assms]])

text \<open>No reachable state has the host in MA with a RspIHitSE from device i pending and H2D data pending to i.\<close>
corollary MA_RspIHitSE_no_HTDData:
  assumes "allTransStar T T'" "initial_state T"
  shows "\<not> (HSTATE MA T' \<and> nextSnpRespIs RspIHitSE T' 0 \<and> nextHTDDataPending T' 0)"
    and "\<not> (HSTATE MA T' \<and> nextSnpRespIs RspIHitSE T' 1 \<and> nextHTDDataPending T' 1)"
  using HitSE_inv_CXL_cache[OF assms] unfolding HitSE_inv_def by blast+

text \<open>Rule ISDSnpInv' never fires in a reachable state.\<close>
corollary ISDSnpInv_disabled:
  assumes "allTransStar T T'" "initial_state T"
  shows "ISDSnpInv' T' 0 = []" and "ISDSnpInv' T' 1 = []"
proof -
  have c0: "CSTATE ISD T' 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T' 0"
   and c1: "CSTATE ISD T' 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T' 1"
    using HitSE_inv_CXL_cache[OF assms] unfolding HitSE_inv_def by blast+
  show "ISDSnpInv' T' 0 = []" unfolding ISDSnpInv'_def by (rule if_not_P) (insert c0, blast)
  show "ISDSnpInv' T' 1 = []" unfolding ISDSnpInv'_def by (rule if_not_P) (insert c1, blast)
qed

end
