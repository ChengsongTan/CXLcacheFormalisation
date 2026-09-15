theory HitSE_Defs
  imports "AllFixes.BasicInvariants"
begin

text \<open>A second invariant, kept separate from SWMR_state_machine. Its first two clauses say that a host
  in MA with a RspIHitSE from device i pending has no H2D data pending to i; the last two say that a device in
  ISD has no SnpInv pending. With SWMR_state_machine it holds in every reachable state (HitSE_Reach.thy),
  which makes the conjunct \<not> nextHTDDataPending T i in the guard of HostMARspIHitSE' redundant (GuardFree.thy).\<close>

definition HitSE_inv :: "Type1State \<Rightarrow> bool" where
  "HitSE_inv T \<equiv>
     (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) \<and>
     (HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) \<and>
     (CSTATE ISD T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) \<and>
     (CSTATE ISD T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1)"

text \<open>The conjunction of both invariants. It is not [simp], so the wrapper proofs of the Fix theories
  apply to it unchanged.\<close>
definition SWMR_HitSE :: "Type1State \<Rightarrow> bool" where
  "SWMR_HitSE T \<equiv> SWMR_state_machine T \<and> HitSE_inv T"

lemma SWMR_HitSE_I: "SWMR_state_machine T \<Longrightarrow> HitSE_inv T \<Longrightarrow> SWMR_HitSE T"
  unfolding SWMR_HitSE_def by (rule conjI)
lemma SWMR_HitSE_D1: "SWMR_HitSE T \<Longrightarrow> SWMR_state_machine T"
  unfolding SWMR_HitSE_def by (erule conjunct1)
lemma SWMR_HitSE_D2: "SWMR_HitSE T \<Longrightarrow> HitSE_inv T"
  unfolding SWMR_HitSE_def by (erule conjunct2)

text \<open>Under HitSE_inv, the other conjuncts of the guard of HostMARspIHitSE' imply \<not> nextHTDDataPending T i.\<close>
lemma HitSE_inv_MA_guard0:
  assumes "HitSE_inv T" and "HSTATE MA T" and "nextSnpRespIs RspIHitSE T 0"
  shows "\<not> nextHTDDataPending T 0"
proof -
  have c: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms(1), unfold HitSE_inv_def, elim conjE, assumption)
  show ?thesis by (rule mp[OF c conjI[OF assms(2) assms(3)]])
qed

lemma HitSE_inv_MA_guard1:
  assumes "HitSE_inv T" and "HSTATE MA T" and "nextSnpRespIs RspIHitSE T 1"
  shows "\<not> nextHTDDataPending T 1"
proof -
  have c: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms(1), unfold HitSE_inv_def, elim conjE, assumption)
  show ?thesis by (rule mp[OF c conjI[OF assms(2) assms(3)]])
qed

lemma Lall_set: "Lall xs P = (\<forall>x\<in>set xs. P x)"
  by (induct xs P rule: Lall.induct) auto

lemma Lall_mono: "Lall xs A \<Longrightarrow> (\<And>x. A x \<Longrightarrow> B x) \<Longrightarrow> Lall xs B"
  unfolding Lall_set by blast

lemma Lall_SWMR_HitSE_D2: "Lall xs SWMR_HitSE \<Longrightarrow> Lall xs HitSE_inv"
  by (erule Lall_mono) (erule SWMR_HitSE_D2)

end
