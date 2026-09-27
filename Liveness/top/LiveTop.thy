theory LiveTop
  imports "AllFixes.TopLevelTheorem"
    "Liveness_Rules.LiveIDDataLate"
    "Liveness_Rules.LiveSBDataLate"
    "Liveness_Rules.LiveIBDataLate"
    "Liveness_Rules.LiveMBDataLate"
    "Liveness_Rules.LiveSharedRdOwnSMAD"
    "Liveness_Rules.LiveSharedRdOwnIMAD"
begin

text \<open>The model extended with the six rules of LiveDefs satisfies SWMR, with the
  same invariant @{const SWMR_state_machine} as the original model and for transitions of both devices.\<close>

definition liveTransitions' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where
  "liveTransitions' = [HostIDDataLate', HostSBDataLate', HostIBDataLate', HostMBDataLate',
                       HostSharedRdOwnSMAD', HostSharedRdOwnIMAD']"

definition allTransitions_live' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where
  "allTransitions_live' = allTransitions' @ liveTransitions'"

subsection \<open>Device symmetry of the new rules\<close>

lemma HostIDDataLatep_toggle: "HostIDDataLate' T 1 = map toggle (HostIDDataLate' (toggle T) 0)"
  by (cases T) (simp add: HostIDDataLate'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSBDataLatep_toggle: "HostSBDataLate' T 1 = map toggle (HostSBDataLate' (toggle T) 0)"
  by (cases T) (simp add: HostSBDataLate'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostIBDataLatep_toggle: "HostIBDataLate' T 1 = map toggle (HostIBDataLate' (toggle T) 0)"
  by (cases T) (simp add: HostIBDataLate'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMBDataLatep_toggle: "HostMBDataLate' T 1 = map toggle (HostMBDataLate' (toggle T) 0)"
  by (cases T) (simp add: HostMBDataLate'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSharedRdOwnSMADp_toggle: "HostSharedRdOwnSMAD' T 1 = map toggle (HostSharedRdOwnSMAD' (toggle T) 0)"
  by (cases T) (simp add: HostSharedRdOwnSMAD'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSharedRdOwnIMADp_toggle: "HostSharedRdOwnIMAD' T 1 = map toggle (HostSharedRdOwnIMAD' (toggle T) 0)"
  by (cases T) (simp add: HostSharedRdOwnIMAD'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma liveTransitions'_toggle:
  "concat (map (\<lambda>f. f T 1) liveTransitions') = map toggle (concat (map (\<lambda>f. f (toggle T) 0) liveTransitions'))"
  unfolding liveTransitions'_def
  by (simp only: list.map concat.simps map_append HostIDDataLatep_toggle HostSBDataLatep_toggle
      HostIBDataLatep_toggle HostMBDataLatep_toggle HostSharedRdOwnSMADp_toggle HostSharedRdOwnIMADp_toggle)

subsection \<open>The new rules preserve the invariant\<close>

theorem live_transitions_coherent: assumes "SWMR_state_machine T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) liveTransitions')). SWMR_state_machine T'"
proof -
  note c = HostIDDataLate'_coherent[OF assms] HostSBDataLate'_coherent[OF assms]
    HostIBDataLate'_coherent[OF assms] HostMBDataLate'_coherent[OF assms] HostSharedRdOwnSMAD'_coherent[OF assms]
    HostSharedRdOwnIMAD'_coherent[OF assms]
  show ?thesis unfolding liveTransitions'_def
    by (simp only: list.map concat.simps set_append ball_Un Ball_Lall empty_set ball_empty c simp_thms Lall.simps(1))
qed

theorem live_transitions_coherent_dev2: assumes "SWMR_state_machine T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 1) liveTransitions')). SWMR_state_machine T'"
proof
  fix T' assume "T' \<in> set (concat (map (\<lambda>f. f T 1) liveTransitions'))"
  then obtain T'' where T'': "T'' \<in> set (concat (map (\<lambda>f. f (toggle T) 0) liveTransitions'))"
    and T'_eq: "T' = toggle T''"
    by (auto simp only: liveTransitions'_toggle set_map image_iff)
  have sym: "SWMR_state_machine (toggle T)" using assms by (rule symmetry)
  have "SWMR_state_machine T''" using live_transitions_coherent[OF sym] T'' by blast
  then show "SWMR_state_machine T'" unfolding T'_eq by (rule symmetry)
qed

theorem all_live_transitions_coherent_both: assumes "SWMR_state_machine T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_live')). SWMR_state_machine T'"
  using all_transitions_coherent_both[OF assms] live_transitions_coherent[OF assms] live_transitions_coherent_dev2[OF assms]
  unfolding allTransitions_live'_def map_append concat_append set_append set_concat_both by blast

subsection \<open>Reachability\<close>

inductive allTransStar_live :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool" where
  refl: "allTransStar_live T T"
| step: "allTransStar_live T T' \<Longrightarrow> T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_live'))
         \<Longrightarrow> allTransStar_live T T''"

theorem SWMR_state_machine_CXL_cache_live:
  assumes "allTransStar_live T T'" and "initial_state T" shows "SWMR_state_machine T'"
  using assms
proof (induct rule: allTransStar_live.induct)
  case (refl T)
  then show ?case using initial_valid by blast
next
  case (step T T' T'')
  then show ?case using all_live_transitions_coherent_both by blast
qed

corollary SWMR_pplus_cache_live:
  assumes "allTransStar_live T T'" and "initial_state T" shows "SWMR_pp T'"
proof -
  have inv: "SWMR_state_machine T'" by (rule SWMR_state_machine_CXL_cache_live[OF assms])
  have a: "SWMR T'" by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have b: "CSTATE Modified T' 0 \<longrightarrow> \<not>CSTATE Modified T' 1"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c: "CSTATE Modified T' 1 \<longrightarrow> \<not>CSTATE Modified T' 0"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using a b c unfolding SWMR_pp_def SWMR_def by auto
qed

text \<open>The extended model can do everything the original model can.\<close>

theorem allTransStar_imp_live: assumes "allTransStar T T'" shows "allTransStar_live T T'"
  using assms
proof (induct rule: allTransStar.induct)
  case (refl T) show ?case by (rule allTransStar_live.refl)
next
  case (step T T' T'')
  from step(3) have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_live'))"
    unfolding allTransitions_live'_def map_append concat_append set_append by blast
  with step(2) show ?case by (rule allTransStar_live.step)
qed

end
