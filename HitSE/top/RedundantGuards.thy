theory RedundantGuards imports GuardFree begin

text \<open>Three more guard conjuncts that follow from SWMR_state_machine and the rest of their guards:
  \<not> nextReqIs DirtyEvict T i in SIASnpInv', GTS T ((i + 1) mod 2) in HostModifiedDirtyEvict', and
  CSTATE IIA T i in HostInvalidDirtyEvict'. The model without them, and without the conjunct of
  HostMARspIHitSE' dropped in GuardFree.thy, reaches exactly the states of the original model.\<close>

definition "SIASnpInv_ng' T i = (if CXL_SPG_used T i \<and> CSTATE SIA T i \<and> nextSnoopIs SnpInv T i
  then [sendSnpResp (getSnoopOrMakeup (getSnoops i T))  RspIHitSE IIA i T] else [])"

definition "HostModifiedDirtyEvict_ng' T i = (if HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T i \<and> CSTATE MIA T i
  then [clearBuffer (sendEvictResp GO_WritePull i ID (nextReqID T i) T)] else [])"

definition "HostInvalidDirtyEvict_ng' T i = (if HSTATE InvalidM T \<and> nextReqIs DirtyEvict T i \<and> GTS T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO_WritePull i IB (nextReqID T i) T)] else [])"

lemma SIASnpInv_ng_eq:
  assumes "SWMR_state_machine T"
  shows "SIASnpInv_ng' T 0 = SIASnpInv' T 0" and "SIASnpInv_ng' T 1 = SIASnpInv' T 1"
proof -
  have c0: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c1: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have d1: "\<And>k. nextReqIs CleanEvict T k \<Longrightarrow> \<not> nextReqIs DirtyEvict T k"
    by (erule nextReqIs_invariant[rotated], simp)
  have d2: "\<And>k. nextReqIs CleanEvictNoData T k \<Longrightarrow> \<not> nextReqIs DirtyEvict T k"
    by (erule nextReqIs_invariant[rotated], simp)
  have g0: "(CXL_SPG_used T 0 \<and> CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> \<not> nextReqIs DirtyEvict T 0)
          = (CXL_SPG_used T 0 \<and> CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0)" using c0 d1 d2 by blast
  have g1: "(CXL_SPG_used T 1 \<and> CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> \<not> nextReqIs DirtyEvict T 1)
          = (CXL_SPG_used T 1 \<and> CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1)" using c1 d1 d2 by blast
  show "SIASnpInv_ng' T 0 = SIASnpInv' T 0" by (simp only: SIASnpInv_ng'_def SIASnpInv'_def g0)
  show "SIASnpInv_ng' T 1 = SIASnpInv' T 1" by (simp only: SIASnpInv_ng'_def SIASnpInv'_def g1)
qed

lemma HostModifiedDirtyEvict_ng_eq:
  assumes "SWMR_state_machine T"
  shows "HostModifiedDirtyEvict_ng' T 0 = HostModifiedDirtyEvict' T 0"
    and "HostModifiedDirtyEvict_ng' T 1 = HostModifiedDirtyEvict' T 1"
proof -
  have m1: "HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have m2: "HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have m3: "HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have g0: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE MIA T 0)
          = (HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<and> CSTATE MIA T 0)" using m1 m2 m3 by auto
  have g1: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<and> GTS T ((1 + 1) mod 2) \<and> CSTATE MIA T 1)
          = (HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<and> CSTATE MIA T 1)" using m1 m2 m3 by auto
  show "HostModifiedDirtyEvict_ng' T 0 = HostModifiedDirtyEvict' T 0"
    by (simp only: HostModifiedDirtyEvict_ng'_def HostModifiedDirtyEvict'_def g0)
  show "HostModifiedDirtyEvict_ng' T 1 = HostModifiedDirtyEvict' T 1"
    by (simp only: HostModifiedDirtyEvict_ng'_def HostModifiedDirtyEvict'_def g1)
qed

lemma HostInvalidDirtyEvict_ng_eq:
  assumes "SWMR_state_machine T"
  shows "HostInvalidDirtyEvict_ng' T 0 = HostInvalidDirtyEvict' T 0"
    and "HostInvalidDirtyEvict_ng' T 1 = HostInvalidDirtyEvict' T 1"
proof -
  have v0: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have v1: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have g0: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2) \<and> CSTATE IIA T 0)
          = (HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<and> GTS T ((0 + 1) mod 2))" using v0 by blast
  have g1: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<and> GTS T ((1 + 1) mod 2) \<and> CSTATE IIA T 1)
          = (HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<and> GTS T ((1 + 1) mod 2))" using v1 by blast
  show "HostInvalidDirtyEvict_ng' T 0 = HostInvalidDirtyEvict' T 0"
    by (simp only: HostInvalidDirtyEvict_ng'_def HostInvalidDirtyEvict'_def g0)
  show "HostInvalidDirtyEvict_ng' T 1 = HostInvalidDirtyEvict' T 1"
    by (simp only: HostInvalidDirtyEvict_ng'_def HostInvalidDirtyEvict'_def g1)
qed

lemma allTransitions'_nth_redundant:
  "allTransitions' ! 32 = SIASnpInv'" "allTransitions' ! 45 = HostModifiedDirtyEvict'"
  "allTransitions' ! 64 = HostInvalidDirtyEvict'"
  unfolding allTransitions'_def by simp_all

text \<open>The rule list of the model without the four conjuncts.\<close>
definition allTransitions_ng2' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where
  "allTransitions_ng2' = allTransitions_ng'[32 := SIASnpInv_ng', 45 := HostModifiedDirtyEvict_ng', 64 := HostInvalidDirtyEvict_ng']"

lemma steps_ng2_eq:
  assumes "SWMR_state_machine T" "HitSE_inv T"
  shows "concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions_ng2') = concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions')"
proof -
  have l: "32 < length allTransitions'" "45 < length allTransitions'" "64 < length allTransitions'" "65 < length allTransitions'"
    by (simp_all add: allTransitions'_length)
  have e65: "HostMARspIHitSE_ng' T 0 @ HostMARspIHitSE_ng' T 1 = HostMARspIHitSE' T 0 @ HostMARspIHitSE' T 1"
    by (simp only: HostMARspIHitSE_ng_eq[OF assms(2)])
  have e32: "SIASnpInv_ng' T 0 @ SIASnpInv_ng' T 1 = SIASnpInv' T 0 @ SIASnpInv' T 1"
    by (simp only: SIASnpInv_ng_eq[OF assms(1)])
  have e45: "HostModifiedDirtyEvict_ng' T 0 @ HostModifiedDirtyEvict_ng' T 1 = HostModifiedDirtyEvict' T 0 @ HostModifiedDirtyEvict' T 1"
    by (simp only: HostModifiedDirtyEvict_ng_eq[OF assms(1)])
  have e64: "HostInvalidDirtyEvict_ng' T 0 @ HostInvalidDirtyEvict_ng' T 1 = HostInvalidDirtyEvict' T 0 @ HostInvalidDirtyEvict' T 1"
    by (simp only: HostInvalidDirtyEvict_ng_eq[OF assms(1)])
  have n65: "map (\<lambda>f. f T 0 @ f T 1) allTransitions' ! 65 = HostMARspIHitSE' T 0 @ HostMARspIHitSE' T 1"
    by (simp only: nth_map[OF l(4)] allTransitions'_nth_HostMARspIHitSE)
  have n32: "map (\<lambda>f. f T 0 @ f T 1) allTransitions' ! 32 = SIASnpInv' T 0 @ SIASnpInv' T 1"
    by (simp only: nth_map[OF l(1)] allTransitions'_nth_redundant(1))
  have n45: "map (\<lambda>f. f T 0 @ f T 1) allTransitions' ! 45 = HostModifiedDirtyEvict' T 0 @ HostModifiedDirtyEvict' T 1"
    by (simp only: nth_map[OF l(2)] allTransitions'_nth_redundant(2))
  have n64: "map (\<lambda>f. f T 0 @ f T 1) allTransitions' ! 64 = HostInvalidDirtyEvict' T 0 @ HostInvalidDirtyEvict' T 1"
    by (simp only: nth_map[OF l(3)] allTransitions'_nth_redundant(3))
  have m: "map (\<lambda>f. f T 0 @ f T 1) allTransitions_ng2' = map (\<lambda>f. f T 0 @ f T 1) allTransitions'"
    by (simp only: allTransitions_ng2'_def allTransitions_ng'_def map_update e65 e32 e45 e64
                   n65[symmetric] n32[symmetric] n45[symmetric] n64[symmetric] list_update_id)
  show ?thesis by (simp only: m)
qed

inductive allTransStar_ng2 :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool" where
  refl: "allTransStar_ng2 T T"
| step: "allTransStar_ng2 T T' \<Longrightarrow> T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_ng2')) \<Longrightarrow> allTransStar_ng2 T T''"

theorem allTransStar_ng2_imp:
  assumes "allTransStar_ng2 T T'" and "initial_state T" shows "allTransStar T T'"
  using assms
proof (induct rule: allTransStar_ng2.induct)
  case (refl T) show ?case by (rule allTransStar.refl)
next
  case (step T T' T'')
  from step have reach: "allTransStar T T'" and init: "initial_state T" by blast+
  have sw: "SWMR_state_machine T'" by (rule SWMR_state_machine_CXL_cache[OF reach init])
  have p: "HitSE_inv T'" by (rule HitSE_inv_CXL_cache[OF reach init])
  from step have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions'))"
    unfolding steps_ng2_eq[OF sw p] by blast
  then show ?case by (rule allTransStar.step[OF reach])
qed

theorem allTransStar_imp_ng2:
  assumes "allTransStar T T'" and "initial_state T" shows "allTransStar_ng2 T T'"
  using assms
proof (induct rule: allTransStar.induct)
  case (refl T) show ?case by (rule allTransStar_ng2.refl)
next
  case (step T T' T'')
  from step have reach: "allTransStar T T'" and init: "initial_state T"
    and ng: "allTransStar_ng2 T T'" by blast+
  have sw: "SWMR_state_machine T'" by (rule SWMR_state_machine_CXL_cache[OF reach init])
  have p: "HitSE_inv T'" by (rule HitSE_inv_CXL_cache[OF reach init])
  from step have "T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions_ng2'))"
    unfolding steps_ng2_eq[OF sw p] by blast
  then show ?case by (rule allTransStar_ng2.step[OF ng])
qed

theorem allTransStar_ng2_iff:
  assumes "initial_state T" shows "allTransStar_ng2 T T' \<longleftrightarrow> allTransStar T T'"
  using allTransStar_ng2_imp allTransStar_imp_ng2 assms by blast

corollary SWMR_pplus_cache_ng2:
  assumes "allTransStar_ng2 T T'" "initial_state T" shows "SWMR_pp T'"
  by (rule SWMR_pplus_cache[OF allTransStar_ng2_imp[OF assms] assms(2)])

end
