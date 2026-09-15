theory GuardFree imports HitSE_Reach begin

text \<open>The model without the conjunct \<not> nextHTDDataPending T i in the guard of HostMARspIHitSE' reaches
  exactly the states of the model with it, so the coherence results carry over.\<close>

text \<open>HostMARspIHitSE' without the conjunct \<not> nextHTDDataPending T i.\<close>
definition "HostMARspIHitSE_ng' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIHitSE T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"

lemma HostMARspIHitSE_ng_eq:
  assumes "HitSE_inv T"
  shows "HostMARspIHitSE_ng' T 0 = HostMARspIHitSE' T 0"
    and "HostMARspIHitSE_ng' T 1 = HostMARspIHitSE' T 1"
proof -
  have c0: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (rule impI, erule conjE, rule HitSE_inv_MA_guard0[OF assms])
  have c1: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (rule impI, erule conjE, rule HitSE_inv_MA_guard1[OF assms])
  have g0: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0 \<and> \<not> nextHTDDataPending T 0)
          = (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<and> GTS T 0)" using c0 by blast
  have g1: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<and> GTS T 1 \<and> \<not> nextHTDDataPending T 1)
          = (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<and> GTS T 1)" using c1 by blast
  show "HostMARspIHitSE_ng' T 0 = HostMARspIHitSE' T 0"
    by (simp only: HostMARspIHitSE_ng'_def HostMARspIHitSE'_def g0)
  show "HostMARspIHitSE_ng' T 1 = HostMARspIHitSE' T 1"
    by (simp only: HostMARspIHitSE_ng'_def HostMARspIHitSE'_def g1)
qed

text \<open>The rule list of the guard-free model is allTransitions' with HostMARspIHitSE' (index 66) replaced.\<close>
lemma allTransitions'_length: "length allTransitions' = 68"
  unfolding allTransitions'_def by simp

lemma allTransitions'_nth_HostMARspIHitSE: "allTransitions' ! 66 = HostMARspIHitSE'"
  unfolding allTransitions'_def by simp

definition allTransitions_ng' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where
  "allTransitions_ng' = allTransitions'[66 := HostMARspIHitSE_ng']"

lemma allTransitions_ng'_nth_HostMARspIHitSE: "allTransitions_ng' ! 66 = HostMARspIHitSE_ng'"
  unfolding allTransitions_ng'_def by (simp add: allTransitions'_length)

lemma steps_ng_eq:
  assumes "HitSE_inv T"
  shows "concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_ng') = concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions')"
proof -
  have e: "HostMARspIHitSE_ng' T 0 @ HostMARspIHitSE_ng' T 1 = HostMARspIHitSE' T 0 @ HostMARspIHitSE' T 1"
    by (simp only: HostMARspIHitSE_ng_eq[OF assms])
  have l: "66 < length allTransitions'"
    by (simp add: allTransitions'_length)
  have n: "map (\<lambda>f. f T 0 @ f T 1) allTransitions' ! 66 = HostMARspIHitSE' T 0 @ HostMARspIHitSE' T 1"
    by (simp only: nth_map[OF l] allTransitions'_nth_HostMARspIHitSE)
  have m: "map (\<lambda>f. f T 0 @ f T 1) allTransitions_ng' = map (\<lambda>f. f T 0 @ f T 1) allTransitions'"
    by (simp only: allTransitions_ng'_def map_update e n[symmetric] list_update_id)
  show ?thesis by (simp only: m)
qed

inductive allTransStar_ng :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool" where
  refl: "allTransStar_ng T T"
| step: "allTransStar_ng T T' \<Longrightarrow> T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_ng')) \<Longrightarrow> allTransStar_ng T T''"

theorem allTransStar_ng_imp:
  assumes "allTransStar_ng T T'" and "initial_state T" shows "allTransStar T T'"
  using assms
proof (induct rule: allTransStar_ng.induct)
  case (refl T) show ?case by (rule allTransStar.refl)
next
  case (step T T' T'')
  from step have reach: "allTransStar T T'" and init: "initial_state T" by blast+
  have p: "HitSE_inv T'" by (rule HitSE_inv_CXL_cache[OF reach init])
  from step have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions'))"
    unfolding steps_ng_eq[OF p] by blast
  then show ?case by (rule allTransStar.step[OF reach])
qed

theorem allTransStar_imp_ng:
  assumes "allTransStar T T'" and "initial_state T" shows "allTransStar_ng T T'"
  using assms
proof (induct rule: allTransStar.induct)
  case (refl T) show ?case by (rule allTransStar_ng.refl)
next
  case (step T T' T'')
  from step have reach: "allTransStar T T'" and init: "initial_state T"
    and ng: "allTransStar_ng T T'" by blast+
  have p: "HitSE_inv T'" by (rule HitSE_inv_CXL_cache[OF reach init])
  from step have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_ng'))"
    unfolding steps_ng_eq[OF p] by blast
  then show ?case by (rule allTransStar_ng.step[OF ng])
qed

theorem allTransStar_ng_iff:
  assumes "initial_state T" shows "allTransStar_ng T T' \<longleftrightarrow> allTransStar T T'"
  using allTransStar_ng_imp allTransStar_imp_ng assms by blast

text \<open>SWMR_state_machine and HitSE_inv together are preserved by the transitions of the guard-free model.\<close>
theorem all_transitions_ng_coherent_both:
  assumes "SWMR_state_machine T" "HitSE_inv T"
  shows "\<forall>T'\<in>set (concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_ng')). SWMR_state_machine T' \<and> HitSE_inv T'"
  unfolding steps_ng_eq[OF assms(2)]
  using all_transitions_coherent_both[OF assms(1)] HitSE_transitions_both[OF assms] by blast

corollary SWMR_state_machine_CXL_cache_ng:
  assumes "allTransStar_ng T T'" "initial_state T" shows "SWMR_state_machine T'"
  by (rule SWMR_state_machine_CXL_cache[OF allTransStar_ng_imp[OF assms] assms(2)])

corollary SWMR_CXL_cache_ng:
  assumes "allTransStar_ng T T'" "initial_state T" shows "SWMR T'"
  by (rule SWMR_CXL_cache[OF allTransStar_ng_imp[OF assms] assms(2)])

corollary SWMR_pplus_cache_ng:
  assumes "allTransStar_ng T T'" "initial_state T" shows "SWMR_pp T'"
  by (rule SWMR_pplus_cache[OF allTransStar_ng_imp[OF assms] assms(2)])

end
