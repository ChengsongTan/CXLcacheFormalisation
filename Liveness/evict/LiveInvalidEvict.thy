theory LiveInvalidEvict imports LiveEvictDefs begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]
lemma InvalidEvict'_coherent_aux_simpler: assumes "SWMR_state_machine T \<and> SA_inv T \<and> CSTATE Invalid T 0 \<and> nextEvict T 0"
  shows "SWMR_state_machine (T [ -=i 0])"
proof -
have i1x: "CSTATE Invalid T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextEvict T 0"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have sa: "SA_inv T"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3y: "\<not> nextSnoopPending T 1" using i1x c248 by simp
show ?thesis
  unfolding SWMR_state_machine_def
proof (intro conjI)
show goal1: "SWMR (T [ -=i 0])"
proof -
  have pre: "SWMR T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD (T [ -=i 0])"
proof -
  have pre: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD (T [ -=i 0])"
proof -
  have pre: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA (T [ -=i 0])"
proof -
  have pre: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal15: "C_H_state Invalid nextStore Modified SAD (T [ -=i 0])"
proof -
  have pre: "C_H_state Invalid nextStore Modified SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre c296 i1x unfolding C_H_state_def by (auto split: list.splits)
qed
show goal16: "C_H_state Invalid nextStore Modified SA (T [ -=i 0])"
proof -
  have pre: "C_H_state Invalid nextStore Modified SA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre sa i1x unfolding C_H_state_def SA_inv_def by (auto split: list.splits)
qed
show goal17: "C_H_state Invalid nextStore Modified SD (T [ -=i 0])"
proof -
  have pre: "C_H_state Invalid nextStore Modified SD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre c218 i1x unfolding C_H_state_def by (auto split: list.splits)
qed
show goal18: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal19: "HSTATE SD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal20: "HSTATE MD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal21: "C_msg_not RdShared IMAD (T [ -=i 0])"
proof -
  have pre: "C_msg_not RdShared IMAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal22: "C_msg_not RdShared Invalid (T [ -=i 0])"
proof -
  have pre: "C_msg_not RdShared Invalid T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) (T [ -=i 0])"
proof -
  have pre: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal27: "C_state_not MIA RdShared (T [ -=i 0])"
proof -
  have pre: "C_state_not MIA RdShared T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal37: "C_msg_state RdShared ISAD (T [ -=i 0])"
proof -
  have pre: "C_msg_state RdShared ISAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal38: "C_not_C_msg Modified ISAD nextGOPending (T [ -=i 0])"
proof -
  have pre: "C_not_C_msg Modified ISAD nextGOPending T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre c248 i1x unfolding C_msg_P_same_def by (auto split: list.splits)
qed
show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c626: "(CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre c626 i1x unfolding C_msg_P_same_def by (auto split: list.splits)
qed
show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal42: "snps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqs1 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> dthdatas2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal43: "snps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqs2 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> dthdatas1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal44: "length (reqs1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (reqs1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal45: "length (reqs2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (reqs2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal46: "length (snps2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (snps2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal47: "length (snps1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (snps1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i3y unfolding C_msg_P_oppo_def by (auto split: list.splits)
qed
show goal51: "CSTATE Invalid (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal52: "CSTATE Invalid (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal53: "CSTATE Shared (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal54: "CSTATE Shared (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal55: "CSTATE IIA (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal56: "CSTATE IIA (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal57: "CSTATE Invalid (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal58: "CSTATE Invalid (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal59: "CSTATE Shared (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal60: "CSTATE Shared (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal61: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal62: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE Modified T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal63: "CSTATE ISD (T [ -=i 0]) 0 \<longrightarrow> \<not> HSTATE ModifiedM (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 0 \<longrightarrow> \<not> HSTATE ModifiedM T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal64: "CSTATE ISD (T [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE ModifiedM (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 1 \<longrightarrow> \<not> HSTATE ModifiedM T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal65: "CSTATE ISD (T [ -=i 0]) 0 \<longrightarrow> nextLoad (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISD T 0 \<longrightarrow> nextLoad T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal66: "CSTATE ISD (T [ -=i 0]) 1 \<longrightarrow> nextLoad (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISD T 1 \<longrightarrow> nextLoad T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal68: "length (htddatas1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (htddatas1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal69: "length (htddatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (htddatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal70: "CSTATE ISD (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal71: "CSTATE ISD (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal72: "CSTATE ISD (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal73: "CSTATE ISD (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal74: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal75: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal76: "length (reqresps1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (reqresps1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal77: "length (reqresps2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (reqresps2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal78: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal79: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal80: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal81: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal82: "CSTATE ISAD (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal83: "CSTATE ISAD (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal85: "reqs1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal86: "reqs2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal87: "reqs1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal88: "reqs2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal89: "reqs1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal90: "reqs2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal91: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal92: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal93: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal94: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal95: "HSTATE MB (T [ -=i 0]) \<and> CSTATE IIA (T [ -=i 0]) 0 \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal96: "HSTATE MB (T [ -=i 0]) \<and> CSTATE IIA (T [ -=i 0]) 1 \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal97: "reqs1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal98: "reqs2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal99: "HSTATE SAD (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal100: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal101: "HSTATE SD (T [ -=i 0]) \<and> dthdatas1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal102: "HSTATE SD (T [ -=i 0]) \<and> dthdatas2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal103: "length (dthdatas1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (dthdatas1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal104: "length (dthdatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (dthdatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal105: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE ISD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal106: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE ISD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal107: "HSTATE SA (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 0) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal108: "HSTATE SA (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 1) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal109: "nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<or> nextSnpRespIs RspIHitSE (T [ -=i 0]) 0 \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISDI (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal110: "nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<or> nextSnpRespIs RspIHitSE (T [ -=i 0]) 1 \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISDI (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal111: "nextReqIs DirtyEvict (T [ -=i 0]) 0 \<longrightarrow> CSTATE MIA (T [ -=i 0]) 0 \<or> CSTATE SIA (T [ -=i 0]) 0 \<or> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or> CSTATE SIA T 0 \<or> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal112: "nextReqIs DirtyEvict (T [ -=i 0]) 1 \<longrightarrow> CSTATE MIA (T [ -=i 0]) 1 \<or> CSTATE SIA (T [ -=i 0]) 1 \<or> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or> CSTATE SIA T 1 \<or> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal113: "snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal114: "snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal115: "length (snpresps1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (snpresps1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal116: "length (snpresps2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (snpresps2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal117: "HSTATE SAD (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 0) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal118: "HSTATE SAD (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 1) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal119: "HSTATE MAD (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> dthdatas1 (T [ -=i 0]) \<noteq> [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal120: "HSTATE MAD (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> dthdatas2 (T [ -=i 0]) \<noteq> [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal121: "HSTATE MA (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal122: "HSTATE MA (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal123: "HSTATE SAD (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal124: "HSTATE SAD (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal125: "HSTATE MD (T [ -=i 0]) \<and> reqs1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> dthdatas1 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal126: "HSTATE MD (T [ -=i 0]) \<and> reqs2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> dthdatas2 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal127: "HSTATE ID (T [ -=i 0]) \<and> dthdatas1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal128: "HSTATE ID (T [ -=i 0]) \<and> dthdatas2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal129: "HSTATE ID (T [ -=i 0]) \<and> dthdatas1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal130: "HSTATE ID (T [ -=i 0]) \<and> dthdatas2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal131: "dthdatas1 (T [ -=i 0]) \<noteq> [] \<and> HSTATE SD (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal132: "dthdatas2 (T [ -=i 0]) \<noteq> [] \<and> HSTATE SD (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal133: "CSTATE ISD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> nextLoad (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal134: "CSTATE ISD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> nextLoad (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal136: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE SD (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal137: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE SD (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal138: "CSTATE ISAD (T [ -=i 0]) 0 \<longrightarrow> nextLoad (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal139: "CSTATE ISAD (T [ -=i 0]) 1 \<longrightarrow> nextLoad (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal140: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal141: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal142: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal143: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal144: "(CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISDI (T [ -=i 0]) 0) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal145: "(CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISDI (T [ -=i 0]) 1) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal146: "(CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISDI (T [ -=i 0]) 0) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal147: "(CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISDI (T [ -=i 0]) 1) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal148: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal149: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal150: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal151: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal152: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal153: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal154: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal155: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal156: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal157: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal158: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal159: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 0 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal160: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 1 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal161: "CSTATE IIA (T [ -=i 0]) 0 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal162: "CSTATE IIA (T [ -=i 0]) 1 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal163: "CSTATE IIA (T [ -=i 0]) 0 \<and> HSTATE SharedM (T [ -=i 0]) \<longrightarrow> reqs2 (T [ -=i 0]) = [] \<or> nextReqIs CleanEvict (T [ -=i 0]) 1 \<or> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<or> nextReqIs RdOwn (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal164: "CSTATE IIA (T [ -=i 0]) 1 \<and> HSTATE SharedM (T [ -=i 0]) \<longrightarrow> reqs1 (T [ -=i 0]) = [] \<or> nextReqIs CleanEvict (T [ -=i 0]) 0 \<or> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<or> nextReqIs RdOwn (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal165: "CSTATE IIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> HSTATE IB (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal166: "CSTATE IIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> HSTATE IB (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal167: "CSTATE IIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal168: "CSTATE IIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal169: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal170: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal171: "CSTATE IIA (T [ -=i 0]) 0 \<and> HSTATE SharedM (T [ -=i 0]) \<longrightarrow> CSTATE Shared (T [ -=i 0]) 1 \<or> CSTATE SIA (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> CSTATE ISD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE SIAC (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal172: "CSTATE IIA (T [ -=i 0]) 1 \<and> HSTATE SharedM (T [ -=i 0]) \<longrightarrow> CSTATE Shared (T [ -=i 0]) 0 \<or> CSTATE SIA (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> CSTATE ISD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE SIAC (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal173: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = [] \<and> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal174: "CSTATE MIA (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal175: "CSTATE MIA (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal176: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = [] \<and> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal177: "HSTATE MA (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = [] \<and> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal178: "nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal179: "nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal180: "nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal181: "nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal182: "HSTATE SA (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = [] \<and> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal183: "HSTATE SD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 0 \<or> \<not> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal184: "HSTATE SAD (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE IIA (T [ -=i 0]) 0 \<or> nextSnpRespIs RspIFwdM (T [ -=i 0]) 0) \<and> (\<not> CSTATE IIA (T [ -=i 0]) 1 \<or> nextSnpRespIs RspIFwdM (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal185: "CSTATE IIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal186: "CSTATE IIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal187: "CSTATE IIA (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal188: "CSTATE IIA (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal189: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal190: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal191: "snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal192: "snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal193: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal194: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal195: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal196: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal197: "HSTATE SAD (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal198: "HSTATE SAD (T [ -=i 0]) \<and> (nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal199: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal202: "CSTATE SIA (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal203: "CSTATE SIA (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal205: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> HSTATE IB (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal206: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> HSTATE IB (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal208: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal209: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal213: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0 \<longrightarrow> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE IB (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal214: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1 \<longrightarrow> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0]) \<or> HSTATE IB (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal216: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal217: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SA (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal218: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SA (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal219: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal220: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal221: "C_not_C_msg Modified IMAD nextGOPending (T [ -=i 0])"
proof -
  have pre: "C_not_C_msg Modified IMAD nextGOPending T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal222: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE MD (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal223: "CSTATE IMAD (T [ -=i 0]) 0 \<longrightarrow> nextStore (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMAD T 0 \<longrightarrow> nextStore T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal224: "CSTATE IMAD (T [ -=i 0]) 1 \<longrightarrow> nextStore (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMAD T 1 \<longrightarrow> nextStore T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal225: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal226: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal227: "snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal228: "snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal229: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal230: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE MD (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal231: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE MD (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal232: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE MD (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal233: "CSTATE SMAD (T [ -=i 0]) 0 \<longrightarrow> nextStore (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 0 \<longrightarrow> nextStore T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal234: "CSTATE SMAD (T [ -=i 0]) 1 \<longrightarrow> nextStore (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 1 \<longrightarrow> nextStore T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal235: "C_msg_P_same IMA nextGOPending nextStore (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same IMA nextGOPending nextStore T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal236: "CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal237: "CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal241: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal242: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal243: "CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 1 \<and> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1 \<and> \<not> ((CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1) \<and> \<not> CSTATE ISA (T [ -=i 0]) 1 \<and> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1 \<or> nextSnoopIs SnpInv (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not> ((CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1 \<and> \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1 \<or> nextSnoopIs SnpInv T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal244: "CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 0 \<and> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0 \<and> \<not> ((CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0) \<and> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 0 \<or> nextSnoopIs SnpInv (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not> ((CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0 \<or> nextSnoopIs SnpInv T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal245: "CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> dthdatas1 (T [ -=i 0]) = [] \<and> (dthdatas2 (T [ -=i 0]) = [] \<or> HSTATE MB (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]))"
proof -
  have pre: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal246: "CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> dthdatas2 (T [ -=i 0]) = [] \<and> (dthdatas1 (T [ -=i 0]) = [] \<or> HSTATE MB (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]))"
proof -
  have pre: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal247: "CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal248: "CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal249: "C_msg_P_same SMA nextGOPending nextStore (T [ -=i 0])"
proof -
  have pre: "C_msg_P_same SMA nextGOPending nextStore T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal250: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal251: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal252: "CSTATE ISD (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<or> CSTATE ISDI (T [ -=i 0]) 0 \<longrightarrow> nextLoad (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal253: "CSTATE ISD (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<or> CSTATE ISDI (T [ -=i 0]) 1 \<longrightarrow> nextLoad (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal254: "CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0 \<longrightarrow> nextStore (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0 \<longrightarrow> nextStore T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal255: "CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1 \<longrightarrow> nextStore (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1 \<longrightarrow> nextStore T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal256: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE Shared (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> (dthdatas1 (T [ -=i 0]) = [] \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 0 \<or> HSTATE SD (T [ -=i 0]))"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<or> CSTATE ISA T 0 \<or> nextHTDDataPending T 0 \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal257: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE Shared (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> (dthdatas2 (T [ -=i 0]) = [] \<or> nextSnpRespIs RspSFwdM (T [ -=i 0]) 1 \<or> HSTATE SD (T [ -=i 0]))"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<or> CSTATE ISA T 1 \<or> nextHTDDataPending T 1 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal258: "CSTATE ISA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal259: "CSTATE ISA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal260: "CSTATE ISDI (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MD (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<or> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal261: "CSTATE ISDI (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0]) \<or> HSTATE MD (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<or> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE SB (T [ -=i 0])"
proof -
  have pre: "CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal262: "CSTATE ISDI (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal263: "CSTATE ISDI (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal264: "CSTATE ISDI (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 1 \<or> \<not> HSTATE ModifiedM (T [ -=i 0])"
proof -
  have pre: "CSTATE ISDI T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 1 \<or> \<not> HSTATE ModifiedM T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal265: "CSTATE ISDI (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 0 \<or> \<not> HSTATE ModifiedM (T [ -=i 0])"
proof -
  have pre: "CSTATE ISDI T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 0 \<or> \<not> HSTATE ModifiedM T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal266: "CSTATE Invalid (T [ -=i 0]) 0 \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal267: "CSTATE Invalid (T [ -=i 0]) 1 \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal268: "CSTATE Shared (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal269: "CSTATE Shared (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal270: "CSTATE Shared (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal271: "CSTATE Shared (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal272: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal273: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal274: "CSTATE SMAD (T [ -=i 0]) 0 \<and> reqresps1 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = [] \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal275: "CSTATE SMAD (T [ -=i 0]) 1 \<and> reqresps2 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = [] \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal276: "nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal277: "nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal278: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<and> CXL_SPG_used (T [ -=i 0]) 0 \<longrightarrow> nextReqIs RdOwn (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal279: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<and> CXL_SPG_used (T [ -=i 0]) 1 \<longrightarrow> nextReqIs RdOwn (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal280: "CSTATE ISD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal281: "CSTATE ISD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal282: "CSTATE ISD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal283: "CSTATE ISD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal284: "HSTATE MD (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal285: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> CSTATE IMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal286: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> CSTATE IMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal287: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict (T [ -=i 0]) 0 \<and> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal288: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict (T [ -=i 0]) 1 \<and> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal289: "HSTATE MD (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal290: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal291: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal292: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal293: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal294: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict (T [ -=i 0]) 0 \<and> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal295: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs CleanEvict (T [ -=i 0]) 1 \<and> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal296: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal297: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal298: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal299: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal300: "(HSTATE SAD (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SA (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0])) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal301: "(HSTATE SAD (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SA (T [ -=i 0]) \<or> HSTATE MA (T [ -=i 0])) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "(HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal302: "nextSnpRespIs RspSFwdM (T [ -=i 0]) 0 \<longrightarrow> CSTATE Shared (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SIA (T [ -=i 0]) 0 \<or> CSTATE SIAC (T [ -=i 0]) 0"
proof -
  have pre: "nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal303: "nextSnpRespIs RspSFwdM (T [ -=i 0]) 1 \<longrightarrow> CSTATE Shared (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SIA (T [ -=i 0]) 1 \<or> CSTATE SIAC (T [ -=i 0]) 1"
proof -
  have pre: "nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal304: "(CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISDI (T [ -=i 0]) 0 \<or> nextReqIs RdOwn (T [ -=i 0]) 0) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "(CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal305: "(CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISDI (T [ -=i 0]) 1 \<or> nextReqIs RdOwn (T [ -=i 0]) 1) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "(CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal306: "CSTATE Modified (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal307: "CSTATE Modified (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal308: "CSTATE Modified (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal309: "CSTATE Modified (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal310: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal311: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal312: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal313: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal314: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal315: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal316: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal317: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal318: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal319: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal320: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal321: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal322: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal323: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal324: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal325: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal326: "CSTATE Modified (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal327: "CSTATE Modified (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal328: "CSTATE Modified (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal329: "CSTATE Modified (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal330: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal331: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal332: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal333: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal334: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 0 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal335: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 1 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal336: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal337: "nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISAD (T [ -=i 0]) 0 \<and> \<not> CSTATE Invalid (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal338: "nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISAD (T [ -=i 0]) 1 \<and> \<not> CSTATE Invalid (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal339: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal340: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal341: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal342: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal343: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal344: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal345: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal346: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal347: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<and> CXL_SPG_used (T [ -=i 0]) 0 \<longrightarrow> nextReqIs CleanEvict (T [ -=i 0]) 0 \<or> nextReqIs CleanEvictNoData (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal348: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<and> CXL_SPG_used (T [ -=i 0]) 1 \<longrightarrow> nextReqIs CleanEvict (T [ -=i 0]) 1 \<or> nextReqIs CleanEvictNoData (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal349: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal350: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal351: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal352: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal353: "HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal354: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs DirtyEvict (T [ -=i 0]) 0 \<longrightarrow> (\<not> CSTATE Modified (T [ -=i 0]) 0 \<or> \<not> CSTATE Modified (T [ -=i 0]) 1) \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal355: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs DirtyEvict (T [ -=i 0]) 1 \<longrightarrow> (\<not> CSTATE Modified (T [ -=i 0]) 0 \<or> \<not> CSTATE Modified (T [ -=i 0]) 1) \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal356: "HSTATE ID (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal357: "HSTATE ID (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal358: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal359: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) (T [ -=i 0])"
proof -
  have pre: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal361: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> CSTATE SIAC (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal362: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> CSTATE SIAC (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal363: "nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 (T [ -=i 0]))"
proof -
  have pre: "nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal364: "nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 (T [ -=i 0]))"
proof -
  have pre: "nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal365: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> nextEvict (T [ -=i 0]) 0"
proof -
  have c308: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c594: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using c308 c594 i1x by (auto split: list.splits)
qed
show goal366: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> nextEvict (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal367: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> nextEvict (T [ -=i 0]) 0"
proof -
  have c308: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c594: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using c308 c594 i1x by (auto split: list.splits)
qed
show goal368: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> nextEvict (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal369: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal370: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal371: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal372: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal373: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal374: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal375: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal376: "HSTATE SharedM (T [ -=i 0]) \<and> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal377: "CSTATE Shared (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal378: "CSTATE Shared (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal379: "nextReqIs DirtyEvict (T [ -=i 0]) 0 \<longrightarrow> nextEvict (T [ -=i 0]) 0"
proof -
  have c308: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c594: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using c308 c594 i1x by (auto split: list.splits)
qed
show goal380: "nextReqIs DirtyEvict (T [ -=i 0]) 1 \<longrightarrow> nextEvict (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal381: "nextReqIs DirtyEvict (T [ -=i 0]) 0 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal382: "nextReqIs DirtyEvict (T [ -=i 0]) 1 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal383: "nextReqIs DirtyEvict (T [ -=i 0]) 0 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal384: "nextReqIs DirtyEvict (T [ -=i 0]) 1 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal385: "nextReqIs DirtyEvict (T [ -=i 0]) 0 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 (T [ -=i 0]))"
proof -
  have pre: "nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal386: "nextReqIs DirtyEvict (T [ -=i 0]) 1 \<and> HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 (T [ -=i 0]))"
proof -
  have pre: "nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal387: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISA (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<or> nextHTDDataPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal388: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISA (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<or> nextHTDDataPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal389: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0]) \<and> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal390: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0]) \<and> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal391: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0]) \<and> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal392: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0]) \<and> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal393: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal394: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal395: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal396: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal397: "nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<or> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> CSTATE SIA (T [ -=i 0]) 0 \<or> CSTATE IIA (T [ -=i 0]) 0 \<or> CSTATE SIAC (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal398: "nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<or> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> CSTATE SIA (T [ -=i 0]) 1 \<or> CSTATE IIA (T [ -=i 0]) 1 \<or> CSTATE SIAC (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal399: "CSTATE Shared (T [ -=i 0]) 0 \<or> CSTATE Shared (T [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE MD (T [ -=i 0])"
proof -
  have pre: "CSTATE Shared T 0 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> HSTATE MD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal400: "CSTATE Shared (T [ -=i 0]) 0 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal401: "CSTATE Shared (T [ -=i 0]) 1 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal402: "nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<or> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> nextEvict (T [ -=i 0]) 0"
proof -
  have c308: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c594: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using c308 c594 i1x by (auto split: list.splits)
qed
show goal403: "nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<or> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> nextEvict (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal404: "nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<or> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal405: "nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<or> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal406: "nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<or> nextReqIs CleanEvict (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal407: "nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<or> nextReqIs CleanEvict (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal408: "CSTATE IIA (T [ -=i 0]) 1 \<and> HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal409: "CSTATE IIA (T [ -=i 0]) 0 \<and> HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal410: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0 \<and> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal411: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> ((CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0)) \<and> \<not> ((CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal412: "nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE InvalidM (T [ -=i 0])"
proof -
  have pre: "nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal413: "CSTATE MIA (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal414: "CSTATE MIA (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal415: "nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal416: "nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal417: "CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal418: "CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<or> HSTATE MB (T [ -=i 0]) \<or> HSTATE MAD (T [ -=i 0]) \<or> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal419: "CSTATE MIA (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal420: "CSTATE MIA (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal421: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal422: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MAD (T [ -=i 0])"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal423: "CSTATE MIA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal424: "CSTATE MIA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal425: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE SharedM (T [ -=i 0]) \<or> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal426: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0 \<and> CSTATE IIA (T [ -=i 0]) 1 \<longrightarrow> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE IB (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal427: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1 \<and> CSTATE IIA (T [ -=i 0]) 0 \<longrightarrow> HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE IB (T [ -=i 0])"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal428: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = [] \<and> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal429: "CSTATE Invalid (T [ -=i 0]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal430: "CSTATE Invalid (T [ -=i 0]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal431: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal432: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal433: "HSTATE MA (T [ -=i 0]) \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal434: "HSTATE MA (T [ -=i 0]) \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal435: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal436: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal437: "HSTATE MA (T [ -=i 0]) \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal438: "HSTATE MA (T [ -=i 0]) \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal439: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal440: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 1 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal441: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal442: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal443: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE IMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal444: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE IMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal445: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal446: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal447: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal448: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal449: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal450: "HSTATE InvalidM (T [ -=i 0]) \<or> HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal451: "CSTATE ISD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal452: "CSTATE ISD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal453: "CSTATE ISA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal454: "CSTATE ISA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal455: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal456: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) \<noteq> [] \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal457: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal458: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal459: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal460: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal461: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal462: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal463: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal464: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal465: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal466: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal467: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal468: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal469: "CSTATE ISD (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<longrightarrow> \<not> HSTATE MD (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal470: "CSTATE ISD (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<longrightarrow> \<not> HSTATE MD (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal471: "CSTATE ISAD (T [ -=i 0]) 0 \<and> (nextHTDDataPending (T [ -=i 0]) 0 \<or> nextGOPending (T [ -=i 0]) 0) \<longrightarrow> \<not> HSTATE MD (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal472: "CSTATE ISAD (T [ -=i 0]) 1 \<and> (nextHTDDataPending (T [ -=i 0]) 1 \<or> nextGOPending (T [ -=i 0]) 1) \<longrightarrow> \<not> HSTATE MD (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal473: "CSTATE ISD (T [ -=i 0]) 0 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal474: "CSTATE ISD (T [ -=i 0]) 1 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal475: "CSTATE ISA (T [ -=i 0]) 0 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal476: "CSTATE ISA (T [ -=i 0]) 1 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal477: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal478: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal479: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 1 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal480: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal481: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal482: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal483: "CSTATE ISD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal484: "CSTATE ISD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal485: "CSTATE ISA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal486: "CSTATE ISA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal487: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal488: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal489: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal490: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> HSTATE MA (T [ -=i 0])"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal491: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal492: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal493: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal494: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal495: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal496: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal497: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal498: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal499: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal500: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal501: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 0 \<and> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal502: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 1 \<and> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal503: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal504: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal505: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal506: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal507: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal508: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal509: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal510: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 1 \<and> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal511: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal512: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal513: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal514: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal515: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal516: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal517: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> snpresps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal518: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal519: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> snpresps2 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal520: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal521: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal522: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal523: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal524: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal525: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal526: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal527: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal528: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal529: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal530: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal531: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal532: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal533: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal534: "HSTATE IB (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal535: "HSTATE IB (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal536: "HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal537: "HSTATE SB (T [ -=i 0]) \<longrightarrow> length (dthdatas1 (T [ -=i 0])) \<le> 1 \<and> length (dthdatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal538: "HSTATE IB (T [ -=i 0]) \<longrightarrow> length (dthdatas1 (T [ -=i 0])) \<le> 1 \<and> length (dthdatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal539: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal540: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal541: "HSTATE MB (T [ -=i 0]) \<longrightarrow> length (dthdatas1 (T [ -=i 0])) \<le> 1 \<and> length (dthdatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal542: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal543: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal544: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal545: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal546: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal547: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal548: "HSTATE SB (T [ -=i 0]) \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal549: "HSTATE IB (T [ -=i 0]) \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal550: "HSTATE MB (T [ -=i 0]) \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal551: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal552: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal553: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal554: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal555: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal556: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal557: "HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal558: "HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal559: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal560: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal561: "HSTATE SharedM (T [ -=i 0]) \<and> lastSharer (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal562: "HSTATE SharedM (T [ -=i 0]) \<and> lastSharer (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal563: "HSTATE SharedM (T [ -=i 0]) \<and> lastSharer (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal564: "HSTATE SharedM (T [ -=i 0]) \<and> lastSharer (T [ -=i 0]) \<and> nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal565: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal566: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal567: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal568: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal569: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal570: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal571: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0) \<and> (\<not> CSTATE SIA (T [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal572: "HSTATE MA (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 0 \<and> \<not> CSTATE SIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal573: "HSTATE MA (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 0 \<and> \<not> CSTATE SIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal574: "HSTATE MD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 0 \<and> \<not> CSTATE SIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal575: "CSTATE MIA (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal576: "CSTATE MIA (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal577: "CSTATE MIA (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal578: "CSTATE MIA (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal579: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal580: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal581: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal582: "HSTATE MD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal583: "HSTATE MA (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal584: "HSTATE MA (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal585: "CSTATE MIA (T [ -=i 0]) 0 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal586: "CSTATE MIA (T [ -=i 0]) 1 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal587: "CSTATE MIA (T [ -=i 0]) 0 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE IMD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal588: "CSTATE MIA (T [ -=i 0]) 1 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE IMD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal589: "CSTATE MIA (T [ -=i 0]) 0 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 1 \<and> (nextGOPending (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1))"
proof -
  have pre: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal590: "CSTATE MIA (T [ -=i 0]) 1 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> (CSTATE IMAD (T [ -=i 0]) 0 \<and> (nextGOPending (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0))"
proof -
  have pre: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal591: "CSTATE MIA (T [ -=i 0]) 0 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal592: "CSTATE MIA (T [ -=i 0]) 1 \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal593: "CSTATE IMD (T [ -=i 0]) 1 \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal594: "CSTATE IMD (T [ -=i 0]) 0 \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal595: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal596: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal597: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal598: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 1 \<and> \<not> CSTATE ISD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal599: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal600: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal601: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE IMD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal602: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE IMD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal603: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal604: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0 \<and> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal605: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal606: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal607: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal608: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal609: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal610: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal611: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal612: "HSTATE ModifiedM (T [ -=i 0]) \<and> nextReqIs RdShared (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal613: "HSTATE SD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal614: "HSTATE SAD (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal615: "HSTATE SAD (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal616: "HSTATE MD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal617: "snpresps1 (T [ -=i 0]) \<noteq> [] \<and> HSTATE MAD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal618: "snpresps2 (T [ -=i 0]) \<noteq> [] \<and> HSTATE MAD (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal619: "CSTATE IMD (T [ -=i 0]) 0 \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal620: "CSTATE IMD (T [ -=i 0]) 1 \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal621: "nextDTHDataFrom 0 (T [ -=i 0]) \<and> HSTATE MD (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal622: "nextDTHDataFrom 1 (T [ -=i 0]) \<and> HSTATE MD (T [ -=i 0]) \<and> nextReqIs RdOwn (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal623: "HSTATE SAD (T [ -=i 0]) \<and> nextSnpRespIs RspSFwdM (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal624: "HSTATE SAD (T [ -=i 0]) \<and> nextSnpRespIs RspSFwdM (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal625: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal626: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal627: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal628: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal629: "HSTATE SA (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal630: "HSTATE SharedM (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal631: "CSTATE IIA (T [ -=i 0]) 0 \<and> HSTATE SA (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal632: "CSTATE IIA (T [ -=i 0]) 1 \<and> HSTATE SA (T [ -=i 0]) \<longrightarrow> CSTATE ISAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal633: "HSTATE MA (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas1 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal634: "HSTATE MA (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> htddatas2 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal635: "HSTATE MB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 0 \<and> \<not> CSTATE ISD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal636: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<or> CSTATE IMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal637: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE Invalid (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<or> CSTATE IMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal638: "HSTATE MB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal639: "HSTATE MB (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal640: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal641: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal642: "HSTATE MB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 0 \<and> \<not> CSTATE SIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal643: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal644: "HSTATE MB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal645: "HSTATE MB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE ISA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal646: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal647: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<and> HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal648: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal649: "HSTATE IB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal650: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal651: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal652: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal653: "HSTATE SB (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal654: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal655: "HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal656: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal657: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs RdOwn (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal658: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal659: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal660: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal661: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal662: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal663: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal664: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal665: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal666: "CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> CSTATE ISA (T [ -=i 0]) 0 \<or> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE Shared (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE ISAD T 0 \<and> nextGOPending T 0 \<or> CSTATE ISA T 0 \<or> nextHTDDataPending T 0 \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal667: "CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> CSTATE ISA (T [ -=i 0]) 1 \<or> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE Shared (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE ISAD T 1 \<and> nextGOPending T 1 \<or> CSTATE ISA T 1 \<or> nextHTDDataPending T 1 \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal668: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal669: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal670: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal671: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal672: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 0 \<and> \<not> CSTATE SIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal673: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SIA (T [ -=i 0]) 1 \<and> \<not> CSTATE SIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal674: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> (htddatas2 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal675: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> (htddatas1 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal676: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal677: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal678: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal679: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal680: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal681: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> (CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal682: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 1 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal683: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE ISA (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal684: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal685: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal686: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal687: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal688: "CSTATE Invalid (T [ -=i 0]) 0 \<longrightarrow> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 0 \<longrightarrow> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal689: "CSTATE Invalid (T [ -=i 0]) 1 \<longrightarrow> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Invalid T 1 \<longrightarrow> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal690: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> CSTATE ISD (T [ -=i 0]) 1 \<or> CSTATE ISAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal691: "HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> CSTATE ISD (T [ -=i 0]) 0 \<or> CSTATE ISAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal692: "HSTATE SAD (T [ -=i 0]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> \<not> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal693: "HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal694: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0]) \<and> CSTATE ISAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal695: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0]) \<and> CSTATE ISAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal696: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal697: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal698: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal699: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal700: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal701: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<and> HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal702: "CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal703: "CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<and> HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal704: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs DirtyEvict (T [ -=i 0]) 0 \<longrightarrow> CSTATE IIA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal705: "HSTATE InvalidM (T [ -=i 0]) \<and> nextReqIs DirtyEvict (T [ -=i 0]) 1 \<longrightarrow> CSTATE IIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal706: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0) \<and> (\<not> CSTATE SIA (T [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1)"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal707: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal708: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal709: "length (dthdatas1 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (dthdatas1 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal710: "length (dthdatas2 (T [ -=i 0])) \<le> 1"
proof -
  have pre: "length (dthdatas2 T) \<le> 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal711: "HSTATE IB (T [ -=i 0]) \<and> CSTATE IIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal712: "HSTATE IB (T [ -=i 0]) \<and> CSTATE IIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal713: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal714: "HSTATE MAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal715: "HSTATE MA (T [ -=i 0]) \<and> snpresps1 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal716: "HSTATE MA (T [ -=i 0]) \<and> snpresps2 (T [ -=i 0]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared (T [ -=i 0]) 0 \<and> \<not> CSTATE Shared (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal717: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> snpresps1 (T [ -=i 0]) = [] \<and> snps1 (T [ -=i 0]) = [] \<and> reqresps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal718: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> snpresps2 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = [] \<and> reqresps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal719: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> (htddatas2 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal720: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> (htddatas1 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal721: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1 \<and> (htddatas2 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 1)"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal722: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0 \<and> (htddatas1 (T [ -=i 0]) = [] \<or> CSTATE ISDI (T [ -=i 0]) 0)"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal723: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> dthdatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal724: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> dthdatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal725: "nextSnpRespIs RspIHitSE (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 0 \<and> \<not> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal726: "nextSnpRespIs RspIHitSE (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE IMA (T [ -=i 0]) 1 \<and> \<not> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal727: "CSTATE IMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal728: "CSTATE IMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal729: "CSTATE SMD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal730: "CSTATE SMD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal731: "CSTATE IMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal732: "CSTATE IMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal733: "CSTATE SMA (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal734: "CSTATE SMA (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal735: "CSTATE IMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal736: "CSTATE IMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal737: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal738: "HSTATE MD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal739: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal740: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal741: "HSTATE InvalidM (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal742: "HSTATE IB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal743: "HSTATE ID (T [ -=i 0]) \<longrightarrow> \<not> CSTATE SMAD (T [ -=i 0]) 1 \<and> \<not> CSTATE SMAD (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal744: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIHitSE (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal745: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIHitSE (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal746: "CSTATE Modified (T [ -=i 0]) 0 \<longrightarrow> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal747: "CSTATE Modified (T [ -=i 0]) 1 \<longrightarrow> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal748: "HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal749: "CSTATE SMAD (T [ -=i 0]) 0 \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 0 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 1 \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal750: "CSTATE SMAD (T [ -=i 0]) 1 \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextSnoopIs SnpInv (T [ -=i 0]) 1 \<longrightarrow> CSTATE IMAD (T [ -=i 0]) 0 \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal751: "CSTATE SMAD (T [ -=i 0]) 1 \<and> HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal752: "CSTATE SMAD (T [ -=i 0]) 0 \<and> HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal753: "CSTATE SIAC (T [ -=i 0]) 0 \<and> HSTATE SA (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal754: "CSTATE SIAC (T [ -=i 0]) 1 \<and> HSTATE SA (T [ -=i 0]) \<longrightarrow> \<not> CSTATE Modified (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal755: "CSTATE SIAC (T [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal756: "CSTATE SIAC (T [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal757: "CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<longrightarrow> snps2 (T [ -=i 0]) = [] \<and> snpresps2 (T [ -=i 0]) = [] \<and> htddatas1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal758: "CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<longrightarrow> snps1 (T [ -=i 0]) = [] \<and> snpresps1 (T [ -=i 0]) = [] \<and> htddatas2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal759: "(CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal760: "(CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal761: "(CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal762: "(CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) \<noteq> []"
proof -
  have pre: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal763: "(CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1"
proof -
  have pre: "(CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal764: "(CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0"
proof -
  have pre: "(CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal765: "CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<longrightarrow> snps1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> snps1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal766: "CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<longrightarrow> snps2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> snps2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal767: "CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<longrightarrow> reqs1 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0 \<longrightarrow> reqs1 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal768: "CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<longrightarrow> reqs2 (T [ -=i 0]) = []"
proof -
  have pre: "CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1 \<longrightarrow> reqs2 T = []"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal769: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 0"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal770: "HSTATE MA (T [ -=i 0]) \<and> nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<longrightarrow> \<not> nextHTDDataPending (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal771: "HSTATE SB (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1"
proof -
  have pre: "HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal772: "nextReqIs CleanEvictNoData (T [ -=i 0]) 0 \<longrightarrow> CSTATE SIAC (T [ -=i 0]) 0"
proof -
  have pre: "nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal773: "nextReqIs CleanEvictNoData (T [ -=i 0]) 1 \<longrightarrow> CSTATE SIAC (T [ -=i 0]) 1"
proof -
  have pre: "nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal774: "nextSnpRespIs RspIHitSE (T [ -=i 0]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 (T [ -=i 0])"
proof -
  have pre: "nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal775: "nextSnpRespIs RspIHitSE (T [ -=i 0]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 (T [ -=i 0])"
proof -
  have pre: "nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal776: "nextSnpRespIs RspIFwdM (T [ -=i 0]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 0"
proof -
  have pre: "nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal777: "nextSnpRespIs RspIFwdM (T [ -=i 0]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData (T [ -=i 0]) 1"
proof -
  have pre: "nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1"
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal778: "(CSTATE SMA (T [ -=i 0]) 0 \<and> nextSnoopIs SnpData (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<longrightarrow> HSTATE SAD (T [ -=i 0])) "
proof -
  have pre: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal779: "(CSTATE SMA (T [ -=i 0]) 1 \<and> nextSnoopIs SnpData (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<longrightarrow> HSTATE SAD (T [ -=i 0])) "
proof -
  have pre: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal780: "((CSTATE SIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or>(CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1) "
proof -
  have pre: "((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal781: "((CSTATE SIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or>(CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0)   "
proof -
  have pre: "((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal782: "((CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPendingIs GO (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<and> \<not> CSTATE IIA (T [ -=i 0]) 1 \<and> GTS (T [ -=i 0]) 1) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 1 \<or> CSTATE MIA (T [ -=i 0]) 1 \<or> (CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<and> nextGOPending (T [ -=i 0]) 1 \<or>(CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1) \<and> nextGOPending (T [ -=i 0]) 1 \<or> (CSTATE IMD (T [ -=i 0]) 1 \<or> CSTATE SMD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1) "
proof -
  have pre: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal783: "((CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPendingIs GO (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<and> \<not> CSTATE IIA (T [ -=i 0]) 0 \<and> GTS (T [ -=i 0]) 0) \<and> HSTATE ModifiedM (T [ -=i 0]) \<longrightarrow> CSTATE Modified (T [ -=i 0]) 0 \<or> CSTATE MIA (T [ -=i 0]) 0 \<or> (CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<and> nextGOPending (T [ -=i 0]) 0 \<or>(CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0) \<and> nextGOPending (T [ -=i 0]) 0 \<or> (CSTATE IMD (T [ -=i 0]) 0 \<or> CSTATE SMD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0)   "
proof -
  have pre: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal784: "((CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPendingIs GO (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<and> \<not> CSTATE IIA (T [ -=i 0]) 1 \<and> GTS (T [ -=i 0]) 1) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas1 (T [ -=i 0]) \<noteq> []) "
proof -
  have pre: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal785: "((CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPendingIs GO (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<and> \<not> CSTATE IIA (T [ -=i 0]) 0 \<and> GTS (T [ -=i 0]) 0) \<and> HSTATE MD (T [ -=i 0]) \<longrightarrow> dthdatas2 (T [ -=i 0]) \<noteq> [])  "
proof -
  have pre: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> [])  "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal786: "((CSTATE SIAC (T [ -=i 0]) 0 \<and> nextGOPendingIs GO (T [ -=i 0]) 0 \<and> nextGOPendingState Invalid (T [ -=i 0]) 0 \<and> \<not> CSTATE IIA (T [ -=i 0]) 1 \<and> GTS (T [ -=i 0]) 1) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> ((CSTATE IMAD (T [ -=i 0]) 1 \<or> CSTATE SMAD (T [ -=i 0]) 1) \<and> nextHTDDataPending (T [ -=i 0]) 1 \<or> CSTATE IMA (T [ -=i 0]) 1 \<or> CSTATE SMA (T [ -=i 0]) 1)) "
proof -
  have pre: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal787: "((CSTATE SIAC (T [ -=i 0]) 1 \<and> nextGOPendingIs GO (T [ -=i 0]) 1 \<and> nextGOPendingState Invalid (T [ -=i 0]) 1 \<and> \<not> CSTATE IIA (T [ -=i 0]) 0 \<and> GTS (T [ -=i 0]) 0) \<and> HSTATE MA (T [ -=i 0]) \<longrightarrow> ((CSTATE IMAD (T [ -=i 0]) 0 \<or> CSTATE SMAD (T [ -=i 0]) 0) \<and> nextHTDDataPending (T [ -=i 0]) 0 \<or> CSTATE IMA (T [ -=i 0]) 0 \<or> CSTATE SMA (T [ -=i 0]) 0)) "
proof -
  have pre: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal788: "(HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> snps2 (T [ -=i 0]) = []) "
proof -
  have pre: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal789: "(HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> snps1 (T [ -=i 0]) = []) "
proof -
  have pre: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal790: "(HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> reqresps1 (T [ -=i 0]) = []) "
proof -
  have pre: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal791: "(HSTATE SD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> reqresps2 (T [ -=i 0]) = []) "
proof -
  have pre: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal792: "(HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 0 (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1) ) "
proof -
  have pre: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal793: "(HSTATE ID (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0) ) "
proof -
  have pre: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal794: "(CSTATE MIA (T [ -=i 0]) 0 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 0 \<and> HSTATE ID (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 1 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 1)) "
proof -
  have pre: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal795: "(CSTATE MIA (T [ -=i 0]) 1 \<and> nextGOPendingIs GO_WritePull (T [ -=i 0]) 1 \<and> HSTATE ID (T [ -=i 0]) \<longrightarrow> (\<not> CSTATE SIA (T [ -=i 0]) 0 \<or> nextGOPendingIs GO_WritePullDrop (T [ -=i 0]) 0))  "
proof -
  have pre: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0))  "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
show goal796: "(HSTATE SAD (T [ -=i 0]) \<and> nextDTHDataFrom 1 (T [ -=i 0]) \<longrightarrow> \<not> CSTATE MIA (T [ -=i 0]) 0 \<and> \<not> CSTATE MIA (T [ -=i 0]) 1) "
proof -
  have pre: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) "
    by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using pre i1x i2x i3y unfolding SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def by (auto split: list.splits)
qed
qed
qed

lemma InvalidEvict'_coherent: assumes "SWMR_state_machine T" "SA_inv T" shows "Lall (InvalidEvict' T 0) SWMR_state_machine"
  unfolding InvalidEvict'_def
  apply (rule Lall_single_if)
  unfolding clearBuffer_def
  apply (rule InvalidEvict'_coherent_aux_simpler)
  using assms by blast

end
