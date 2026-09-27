theory LiveSARules
  imports LiveEvictDefs
begin

text \<open>Every rule of @{const allTransitions_live2'} preserves @{const SA_inv}, given @{const SWMR_state_machine}.
  Stated for device index 0; LiveEvictTop.thy transfers them to index 1 by device symmetry.\<close>

lemma InvalidLoad_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (InvalidLoad' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding InvalidLoad'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SharedLoad_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SharedLoad' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SharedLoad'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma InvalidStore_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (InvalidStore' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding InvalidStore'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SharedStore_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SharedStore' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SharedStore'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SharedEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SharedEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SharedEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ModifiedEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SharedSnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SharedSnpInv' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SharedSnpInv'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ISDSnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISDSnpInv' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISDSnpInv'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ISDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISDData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISDData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ISDIData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISDIData' T 0) SA_inv"
proof -
  have c457: "(CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISDIData'_def
    apply (rule Lall_single_if)
    using si c457 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma IMADData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IMADData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IMADData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SMADData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SMADData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SMADData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma IMADGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IMADGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IMADGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ISADGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISADGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISADGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ISADData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISADData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISADData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SMADGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SMADGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SMADGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SMAGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SMAGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SMAGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (intro conjI impI; elim conjE; clarsimp split: if_splits list.splits)
qed

lemma SMADSnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SMADSnpInv' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SMADSnpInv'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SMDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SMDData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SMDData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma IMAGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IMAGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IMAGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (intro conjI impI; elim conjE; clarsimp split: if_splits list.splits)
qed

lemma ISAGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ISAGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ISAGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (clarsimp split: if_splits list.splits)
qed

lemma ModifiedStore_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedStore' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedStore'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ModifiedLoad_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedLoad' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedLoad'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SIAGO_WritePull_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SIAGO_WritePull' T 0) SA_inv"
proof -
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SIAGO_WritePull'_def
    apply (rule Lall_single_if)
    using si c826 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def split: list.splits)
qed

lemma SIAGO_WritePullDrop_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SIAGO_WritePullDrop' T 0) SA_inv"
proof -
  have c410: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T \<or> HSTATE ID T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SIAGO_WritePullDrop'_def
    apply (rule Lall_single_if)
    using si c410 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma IIAGO_WritePullDrop_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IIAGO_WritePullDrop' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IIAGO_WritePullDrop'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (intro conjI impI; elim conjE; clarsimp split: if_splits list.splits)
qed

lemma IIAGO_WritePull_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IIAGO_WritePull' T 0) SA_inv"
proof -
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IIAGO_WritePull'_def
    apply (rule Lall_single_if)
    using si c826 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def split: list.splits)
qed

lemma IMDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (IMDData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding IMDData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma MIASnpDataInvalid_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (MIASnpDataInvalid' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding MIASnpDataInvalid'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma MIASnpDataShared_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (MIASnpDataShared' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding MIASnpDataShared'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma MIASnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (MIASnpInv' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding MIASnpInv'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma MIAGO_WritePull_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (MIAGO_WritePull' T 0) SA_inv"
proof -
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding MIAGO_WritePull'_def
    apply (rule Lall_single_if)
    using si c826 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def split: list.splits)
qed

lemma SIASnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SIASnpInv' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SIASnpInv'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma ModifiedSnpInv_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedSnpInv' T 0) SA_inv"
proof -
  have c258: "(CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedSnpInv'_def
    apply (rule Lall_single_if)
    using si c258 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma ModifiedSnpDataShared_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedSnpDataShared' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedSnpDataShared'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma ModifiedSnpDataInvalid_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (ModifiedSnpDataInvalid' T 0) SA_inv"
proof -
  have c258: "(CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding ModifiedSnpDataInvalid'_def
    apply (rule Lall_single_if)
    using si c258 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma HostInvalidRdShared_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostInvalidRdShared' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostInvalidRdShared'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostInvalidRdOwn_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostInvalidRdOwn' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostInvalidRdOwn'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSharedRdShared_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSharedRdShared' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSharedRdShared'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_CleanEvict_NotLastDrop_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_CleanEvict_NotLastDrop' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_CleanEvict_NotLastDrop'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_CleanEvict_NotLastData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_CleanEvict_NotLastData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_CleanEvict_NotLastData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_CleanEvict_Last_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_CleanEvict_Last' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_CleanEvict_Last'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_CleanEvictNoData_NotLast_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_CleanEvictNoData_NotLast' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_CleanEvictNoData_NotLast'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_CleanEvictNoData_Last_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_CleanEvictNoData_Last' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_CleanEvictNoData_Last'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostShared_DirtyEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostShared_DirtyEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostShared_DirtyEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostModifiedDirtyEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostModifiedDirtyEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostModifiedDirtyEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostModifiedRdShared_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostModifiedRdShared' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostModifiedRdShared'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostModifiedRdOwn_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostModifiedRdOwn' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostModifiedRdOwn'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSharedRdOwn_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSharedRdOwn' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSharedRdOwn'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSharedRdOwnSelf_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSharedRdOwnSelf' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSharedRdOwnSelf'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSDData' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSDData'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma HostSADData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSADData' T 0) SA_inv"
proof -
  have c346: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSADData'_def
    apply (rule Lall_single_if)
    using si c346 sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma HostMDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMDData' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMDData'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma HostIDData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostIDData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostIDData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMADData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMADData' T 0) SA_inv"
proof -
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMADData'_def
    apply (rule Lall_single_if)
    using si  sw0 unfolding SA_inv_def SWMR_def
    by (auto simp: Let_def)
qed

lemma HostSADRspIFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSADRspIFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSADRspIFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSADRspSFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSADRspSFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSADRspSFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMADRspIFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMADRspIFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMADRspIFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMARspIFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMARspIFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMARspIFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSARspIFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSARspIFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSARspIFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSARspSFwdM_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSARspSFwdM' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSARspSFwdM'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostIBDataPrevious_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostIBDataPrevious' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostIBDataPrevious'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSBData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSBData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSBData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMBData_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMBData' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMBData'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostInvalidDirtyEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostInvalidDirtyEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostInvalidDirtyEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMARspIHitSE_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMARspIHitSE' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMARspIHitSE'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma SIACGO_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (SIACGO' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding SIACGO'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (clarsimp split: if_splits list.splits)
qed

lemma HostModifiedDirtyEvictPrevious_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostModifiedDirtyEvictPrevious' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostModifiedDirtyEvictPrevious'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostIDDataLate_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostIDDataLate' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostIDDataLate'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSBDataLate_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSBDataLate' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSBDataLate'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostIBDataLate_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostIBDataLate' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostIBDataLate'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostMBDataLate_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostMBDataLate' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostMBDataLate'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSharedRdOwnSMAD_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSharedRdOwnSMAD' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSharedRdOwnSMAD'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma HostSharedRdOwnIMAD_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (HostSharedRdOwnIMAD' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding HostSharedRdOwnIMAD'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

lemma InvalidEvict_SA0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T" shows "Lall (InvalidEvict' T 0) SA_inv"
proof -
  have c218: "(HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c296: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1))"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c438: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c439: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c447: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c448: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c826: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c828: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c829: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c950: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c951: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c248: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c249: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c304: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c305: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0)"
    by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  have sw0: "SWMR T" by (insert sw, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis unfolding InvalidEvict'_def
    apply (rule Lall_single_if)
    using si c218 c296 c438 c439 c447 c448 c826 c828 c829 c950 c951 c248 c249 c304 c305 sw0 unfolding SA_inv_def SWMR_def
    by (auto split: if_splits list.splits)
qed

theorem SA_rules_dev0: assumes sw: "SWMR_state_machine T" and si: "SA_inv T"
  shows "\<forall>T' \<in> set (concat (map (\<lambda>f. f T 0) allTransitions_live2')). SA_inv T'"
proof -
  note c = InvalidLoad_SA0[OF sw si] SharedLoad_SA0[OF sw si] InvalidStore_SA0[OF sw si] SharedStore_SA0[OF sw si] SharedEvict_SA0[OF sw si] ModifiedEvict_SA0[OF sw si] SharedSnpInv_SA0[OF sw si] ISDSnpInv_SA0[OF sw si] ISDData_SA0[OF sw si] ISDIData_SA0[OF sw si] IMADData_SA0[OF sw si] SMADData_SA0[OF sw si] IMADGO_SA0[OF sw si] ISADGO_SA0[OF sw si] ISADData_SA0[OF sw si] SMADGO_SA0[OF sw si] SMAGO_SA0[OF sw si] SMADSnpInv_SA0[OF sw si] SMDData_SA0[OF sw si] IMAGO_SA0[OF sw si] ISAGO_SA0[OF sw si] ModifiedStore_SA0[OF sw si] ModifiedLoad_SA0[OF sw si] SIAGO_WritePull_SA0[OF sw si] SIAGO_WritePullDrop_SA0[OF sw si] IIAGO_WritePullDrop_SA0[OF sw si] IIAGO_WritePull_SA0[OF sw si] IMDData_SA0[OF sw si] MIASnpDataInvalid_SA0[OF sw si] MIASnpDataShared_SA0[OF sw si] MIASnpInv_SA0[OF sw si] MIAGO_WritePull_SA0[OF sw si] SIASnpInv_SA0[OF sw si] ModifiedSnpInv_SA0[OF sw si] ModifiedSnpDataShared_SA0[OF sw si] ModifiedSnpDataInvalid_SA0[OF sw si] HostInvalidRdShared_SA0[OF sw si] HostInvalidRdOwn_SA0[OF sw si] HostSharedRdShared_SA0[OF sw si] HostShared_CleanEvict_NotLastDrop_SA0[OF sw si] HostShared_CleanEvict_NotLastData_SA0[OF sw si] HostShared_CleanEvict_Last_SA0[OF sw si] HostShared_CleanEvictNoData_NotLast_SA0[OF sw si] HostShared_CleanEvictNoData_Last_SA0[OF sw si] HostShared_DirtyEvict_SA0[OF sw si] HostModifiedDirtyEvict_SA0[OF sw si] HostModifiedRdShared_SA0[OF sw si] HostModifiedRdOwn_SA0[OF sw si] HostSharedRdOwn_SA0[OF sw si] HostSharedRdOwnSelf_SA0[OF sw si] HostSDData_SA0[OF sw si] HostSADData_SA0[OF sw si] HostMDData_SA0[OF sw si] HostIDData_SA0[OF sw si] HostMADData_SA0[OF sw si] HostSADRspIFwdM_SA0[OF sw si] HostSADRspSFwdM_SA0[OF sw si] HostMADRspIFwdM_SA0[OF sw si] HostMARspIFwdM_SA0[OF sw si] HostSARspIFwdM_SA0[OF sw si] HostSARspSFwdM_SA0[OF sw si] HostIBDataPrevious_SA0[OF sw si] HostSBData_SA0[OF sw si] HostMBData_SA0[OF sw si] HostInvalidDirtyEvict_SA0[OF sw si] HostMARspIHitSE_SA0[OF sw si] SIACGO_SA0[OF sw si] HostModifiedDirtyEvictPrevious_SA0[OF sw si] HostIDDataLate_SA0[OF sw si] HostSBDataLate_SA0[OF sw si] HostIBDataLate_SA0[OF sw si] HostMBDataLate_SA0[OF sw si] HostSharedRdOwnSMAD_SA0[OF sw si] HostSharedRdOwnIMAD_SA0[OF sw si] InvalidEvict_SA0[OF sw si]
  show ?thesis unfolding allTransitions_live2'_def allTransitions_live'_def allTransitions'_def liveTransitions'_def
    by (simp only: map_append concat_append list.map concat.simps set_append ball_Un Ball_Lall empty_set ball_empty c simp_thms Lall.simps(1) append_Nil2)
qed

end
