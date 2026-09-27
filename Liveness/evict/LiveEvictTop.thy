theory LiveEvictTop
  imports LiveInvalidEvict LiveSARules
begin

text \<open>The model of LiveTop.thy extended with @{const InvalidEvict'}. Its rule lemma needs @{const SA_inv}
  besides @{const SWMR_state_machine}, so the two are proved together: every rule preserves @{const SA_inv}
  (LiveSARules.thy), and together they hold in every reachable state.\<close>

lemma SA_inv_toggle: "SA_inv (toggle T) = SA_inv T"
  unfolding SA_inv_def by (simp only: CSTATE_toggle0 CSTATE_toggle1 HSTATE_toggle) blast

lemma InvalidEvictp_toggle: "InvalidEvict' T 1 = map toggle (InvalidEvict' (toggle T) 0)"
  by (cases T) (simp add: InvalidEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma allTransitions_live2'_toggle:
  "concat (map (\<lambda>f. f T 1) allTransitions_live2') = map toggle (concat (map (\<lambda>f. f (toggle T) 0) allTransitions_live2'))"
  unfolding allTransitions_live2'_def allTransitions_live'_def
  by (simp only: map_append concat_append allTransitions'_toggle liveTransitions'_toggle list.map concat.simps
      InvalidEvictp_toggle append_Nil2)

lemma symmetric_step:
  assumes dev0: "\<And>T. SWMR_state_machine T \<Longrightarrow> SA_inv T \<Longrightarrow> \<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). P T'"
      and symP: "\<And>T. P (toggle T) = P T"
      and sw: "SWMR_state_machine T" and sa: "SA_inv T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 1) allTransitions_live2')). P T'"
proof
  fix T' assume "T' \<in> set (concat (map (\<lambda>f. f T 1) allTransitions_live2'))"
  then obtain T'' where T'': "T'' \<in> set (concat (map (\<lambda>f. f (toggle T) 0) allTransitions_live2'))"
    and T'_eq: "T' = toggle T''"
    by (auto simp only: allTransitions_live2'_toggle set_map image_iff)
  have "SWMR_state_machine (toggle T)" using sw by (rule symmetry)
  moreover have "SA_inv (toggle T)" using sa by (simp only: SA_inv_toggle)
  ultimately have "P T''" using dev0 T'' by blast
  then show "P T'" unfolding T'_eq by (simp only: symP)
qed

lemma SWMR_toggle_iff: "SWMR_state_machine (toggle T) = SWMR_state_machine T"
proof
  assume "SWMR_state_machine (toggle T)"
  then have "SWMR_state_machine (toggle (toggle T))" by (rule symmetry)
  then show "SWMR_state_machine T" by (simp only: toggle_toggle)
next
  assume "SWMR_state_machine T" then show "SWMR_state_machine (toggle T)" by (rule symmetry)
qed

theorem live2_SWMR_dev0: assumes sw: "SWMR_state_machine T" and sa: "SA_inv T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). SWMR_state_machine T'"
proof -
  have a: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions')). SWMR_state_machine T'"
    by (rule all_transitions_coherent[OF sw])
  have b: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) liveTransitions')). SWMR_state_machine T'"
    by (rule live_transitions_coherent[OF sw])
  have c: "Lall (InvalidEvict' T 0) SWMR_state_machine" by (rule InvalidEvict'_coherent[OF sw sa])
  show ?thesis using a b c unfolding allTransitions_live2'_def allTransitions_live'_def
    by (simp only: map_append concat_append set_append ball_Un list.map concat.simps append_Nil2 Ball_Lall)
qed

theorem live2_SA_dev0: assumes sw: "SWMR_state_machine T" and sa: "SA_inv T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). SA_inv T'"
  using SA_rules_dev0[OF sw sa] .

theorem live2_step: assumes sw: "SWMR_state_machine T" and sa: "SA_inv T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_live2')). SWMR_state_machine T' \<and> SA_inv T'"
proof -
  have s0: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). SWMR_state_machine T'"
    by (rule live2_SWMR_dev0[OF sw sa])
  have a0: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). SA_inv T'"
    by (rule live2_SA_dev0[OF sw sa])
  have s1: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 1) allTransitions_live2')). SWMR_state_machine T'"
    by (rule symmetric_step[OF live2_SWMR_dev0 SWMR_toggle_iff sw sa])
  have a1: "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 1) allTransitions_live2')). SA_inv T'"
    by (rule symmetric_step[OF live2_SA_dev0 SA_inv_toggle sw sa])
  show ?thesis using s0 a0 s1 a1 unfolding set_concat_both by blast
qed

inductive allTransStar_live2 :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool" where
  refl: "allTransStar_live2 T T"
| step: "allTransStar_live2 T T' \<Longrightarrow> T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_live2'))
         \<Longrightarrow> allTransStar_live2 T T''"

theorem SWMR_SA_CXL_cache_live2:
  assumes "allTransStar_live2 T T'" and "initial_state T" shows "SWMR_state_machine T' \<and> SA_inv T'"
  using assms
proof (induct rule: allTransStar_live2.induct)
  case (refl T)
  then show ?case using initial_valid unfolding SA_inv_def by auto
next
  case (step T T' T'')
  then show ?case using live2_step by blast
qed

corollary SWMR_pplus_cache_live2:
  assumes "allTransStar_live2 T T'" and "initial_state T" shows "SWMR_pp T'"
proof -
  have inv: "SWMR_state_machine T'" using SWMR_SA_CXL_cache_live2[OF assms] by blast
  have a: "SWMR T'" by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have b: "CSTATE Modified T' 0 \<longrightarrow> \<not>CSTATE Modified T' 1"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c: "CSTATE Modified T' 1 \<longrightarrow> \<not>CSTATE Modified T' 0"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using a b c unfolding SWMR_pp_def SWMR_def by auto
qed

theorem allTransStar_live_imp_live2: assumes "allTransStar_live T T'" shows "allTransStar_live2 T T'"
  using assms
proof (induct rule: allTransStar_live.induct)
  case (refl T) show ?case by (rule allTransStar_live2.refl)
next
  case (step T T' T'')
  from step(3) have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_live2'))"
    unfolding allTransitions_live2'_def map_append concat_append set_append by blast
  with step(2) show ?case by (rule allTransStar_live2.step)
qed

text \<open>In particular SA_inv holds in every reachable state of the original model.\<close>

corollary SA_inv_CXL_cache: assumes "allTransStar T T'" and "initial_state T" shows "SA_inv T'"
  using SWMR_SA_CXL_cache_live2[OF allTransStar_live_imp_live2[OF allTransStar_imp_live[OF assms(1)]] assms(2)] by blast

end
