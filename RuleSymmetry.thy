theory RuleSymmetry imports Toggle begin

text \<open>Every transition rule commutes with swapping the two devices: the instance of a rule for
device 2 is the mirror image of its instance for device 1. Together with \<open>symmetry\<close> (Toggle.thy) this
transfers the rule lemmas, which are proved for device index 0, to device index 1.\<close>

lemma nat_to_id_1 [simp]: "nat_to_id 1 = Dev2"
  by (simp add: One_nat_def)

lemma InvalidLoadp_toggle: "InvalidLoad' T 1 = map toggle (InvalidLoad' (toggle T) 0)"
  by (cases T) (simp add: InvalidLoad'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SharedLoadp_toggle: "SharedLoad' T 1 = map toggle (SharedLoad' (toggle T) 0)"
  by (cases T) (simp add: SharedLoad'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma InvalidStorep_toggle: "InvalidStore' T 1 = map toggle (InvalidStore' (toggle T) 0)"
  by (cases T) (simp add: InvalidStore'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SharedStorep_toggle: "SharedStore' T 1 = map toggle (SharedStore' (toggle T) 0)"
  by (cases T) (simp add: SharedStore'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SharedEvictp_toggle: "SharedEvict' T 1 = map toggle (SharedEvict' (toggle T) 0)"
  by (cases T) (simp add: SharedEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SharedEvictDatap_toggle: "SharedEvictData' T 1 = map toggle (SharedEvictData' (toggle T) 0)"
  by (cases T) (simp add: SharedEvictData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedEvictp_toggle: "ModifiedEvict' T 1 = map toggle (ModifiedEvict' (toggle T) 0)"
  by (cases T) (simp add: ModifiedEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SharedSnpInvp_toggle: "SharedSnpInv' T 1 = map toggle (SharedSnpInv' (toggle T) 0)"
  by (cases T) (simp add: SharedSnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISDSnpInvp_toggle: "ISDSnpInv' T 1 = map toggle (ISDSnpInv' (toggle T) 0)"
  by (cases T) (simp add: ISDSnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISDDatap_toggle: "ISDData' T 1 = map toggle (ISDData' (toggle T) 0)"
  by (cases T) (simp add: ISDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISDIDatap_toggle: "ISDIData' T 1 = map toggle (ISDIData' (toggle T) 0)"
  by (cases T) (simp add: ISDIData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IMADDatap_toggle: "IMADData' T 1 = map toggle (IMADData' (toggle T) 0)"
  by (cases T) (simp add: IMADData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SMADDatap_toggle: "SMADData' T 1 = map toggle (SMADData' (toggle T) 0)"
  by (cases T) (simp add: SMADData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IMADGOp_toggle: "IMADGO' T 1 = map toggle (IMADGO' (toggle T) 0)"
  by (cases T) (simp add: IMADGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISADGOp_toggle: "ISADGO' T 1 = map toggle (ISADGO' (toggle T) 0)"
  by (cases T) (simp add: ISADGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISADDatap_toggle: "ISADData' T 1 = map toggle (ISADData' (toggle T) 0)"
  by (cases T) (simp add: ISADData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SMADGOp_toggle: "SMADGO' T 1 = map toggle (SMADGO' (toggle T) 0)"
  by (cases T) (simp add: SMADGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SMAGOp_toggle: "SMAGO' T 1 = map toggle (SMAGO' (toggle T) 0)"
  by (cases T) (simp add: SMAGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SMADSnpInvp_toggle: "SMADSnpInv' T 1 = map toggle (SMADSnpInv' (toggle T) 0)"
  by (cases T) (simp add: SMADSnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SMDDatap_toggle: "SMDData' T 1 = map toggle (SMDData' (toggle T) 0)"
  by (cases T) (simp add: SMDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IMAGOp_toggle: "IMAGO' T 1 = map toggle (IMAGO' (toggle T) 0)"
  by (cases T) (simp add: IMAGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ISAGOp_toggle: "ISAGO' T 1 = map toggle (ISAGO' (toggle T) 0)"
  by (cases T) (simp add: ISAGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedStorep_toggle: "ModifiedStore' T 1 = map toggle (ModifiedStore' (toggle T) 0)"
  by (cases T) (simp add: ModifiedStore'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedLoadp_toggle: "ModifiedLoad' T 1 = map toggle (ModifiedLoad' (toggle T) 0)"
  by (cases T) (simp add: ModifiedLoad'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SIAGO_WritePullp_toggle: "SIAGO_WritePull' T 1 = map toggle (SIAGO_WritePull' (toggle T) 0)"
  by (cases T) (simp add: SIAGO_WritePull'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SIAGO_WritePullDropp_toggle: "SIAGO_WritePullDrop' T 1 = map toggle (SIAGO_WritePullDrop' (toggle T) 0)"
  by (cases T) (simp add: SIAGO_WritePullDrop'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IIAGO_WritePullDropp_toggle: "IIAGO_WritePullDrop' T 1 = map toggle (IIAGO_WritePullDrop' (toggle T) 0)"
  by (cases T) (simp add: IIAGO_WritePullDrop'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IIAGO_WritePullp_toggle: "IIAGO_WritePull' T 1 = map toggle (IIAGO_WritePull' (toggle T) 0)"
  by (cases T) (simp add: IIAGO_WritePull'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma IMDDatap_toggle: "IMDData' T 1 = map toggle (IMDData' (toggle T) 0)"
  by (cases T) (simp add: IMDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma MIASnpDataInvalidp_toggle: "MIASnpDataInvalid' T 1 = map toggle (MIASnpDataInvalid' (toggle T) 0)"
  by (cases T) (simp add: MIASnpDataInvalid'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma MIASnpDataSharedp_toggle: "MIASnpDataShared' T 1 = map toggle (MIASnpDataShared' (toggle T) 0)"
  by (cases T) (simp add: MIASnpDataShared'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma MIASnpInvp_toggle: "MIASnpInv' T 1 = map toggle (MIASnpInv' (toggle T) 0)"
  by (cases T) (simp add: MIASnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma MIAGO_WritePullp_toggle: "MIAGO_WritePull' T 1 = map toggle (MIAGO_WritePull' (toggle T) 0)"
  by (cases T) (simp add: MIAGO_WritePull'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SIASnpInvp_toggle: "SIASnpInv' T 1 = map toggle (SIASnpInv' (toggle T) 0)"
  by (cases T) (simp add: SIASnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedSnpInvp_toggle: "ModifiedSnpInv' T 1 = map toggle (ModifiedSnpInv' (toggle T) 0)"
  by (cases T) (simp add: ModifiedSnpInv'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedSnpDataSharedp_toggle: "ModifiedSnpDataShared' T 1 = map toggle (ModifiedSnpDataShared' (toggle T) 0)"
  by (cases T) (simp add: ModifiedSnpDataShared'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma ModifiedSnpDataInvalidp_toggle: "ModifiedSnpDataInvalid' T 1 = map toggle (ModifiedSnpDataInvalid' (toggle T) 0)"
  by (cases T) (simp add: ModifiedSnpDataInvalid'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostInvalidRdSharedp_toggle: "HostInvalidRdShared' T 1 = map toggle (HostInvalidRdShared' (toggle T) 0)"
  by (cases T) (simp add: HostInvalidRdShared'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostInvalidRdOwnp_toggle: "HostInvalidRdOwn' T 1 = map toggle (HostInvalidRdOwn' (toggle T) 0)"
  by (cases T) (simp add: HostInvalidRdOwn'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSharedRdSharedp_toggle: "HostSharedRdShared' T 1 = map toggle (HostSharedRdShared' (toggle T) 0)"
  by (cases T) (simp add: HostSharedRdShared'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_CleanEvict_NotLastDropp_toggle: "HostShared_CleanEvict_NotLastDrop' T 1 = map toggle (HostShared_CleanEvict_NotLastDrop' (toggle T) 0)"
  by (cases T) (simp add: HostShared_CleanEvict_NotLastDrop'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_CleanEvict_NotLastDatap_toggle: "HostShared_CleanEvict_NotLastData' T 1 = map toggle (HostShared_CleanEvict_NotLastData' (toggle T) 0)"
  by (cases T) (simp add: HostShared_CleanEvict_NotLastData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_CleanEvict_Lastp_toggle: "HostShared_CleanEvict_Last' T 1 = map toggle (HostShared_CleanEvict_Last' (toggle T) 0)"
  by (cases T) (simp add: HostShared_CleanEvict_Last'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_CleanEvictNoData_NotLastp_toggle: "HostShared_CleanEvictNoData_NotLast' T 1 = map toggle (HostShared_CleanEvictNoData_NotLast' (toggle T) 0)"
  by (cases T) (simp add: HostShared_CleanEvictNoData_NotLast'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_CleanEvictNoData_Lastp_toggle: "HostShared_CleanEvictNoData_Last' T 1 = map toggle (HostShared_CleanEvictNoData_Last' (toggle T) 0)"
  by (cases T) (simp add: HostShared_CleanEvictNoData_Last'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostShared_DirtyEvictp_toggle: "HostShared_DirtyEvict' T 1 = map toggle (HostShared_DirtyEvict' (toggle T) 0)"
  by (cases T) (simp add: HostShared_DirtyEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostModifiedDirtyEvictp_toggle: "HostModifiedDirtyEvict' T 1 = map toggle (HostModifiedDirtyEvict' (toggle T) 0)"
  by (cases T) (simp add: HostModifiedDirtyEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)
lemma HostModifiedDirtyEvictPreviousp_toggle: "HostModifiedDirtyEvictPrevious' T 1 = map toggle (HostModifiedDirtyEvictPrevious' (toggle T) 0)"
  by (cases T) (simp add: HostModifiedDirtyEvictPrevious'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostModifiedRdSharedp_toggle: "HostModifiedRdShared' T 1 = map toggle (HostModifiedRdShared' (toggle T) 0)"
  by (cases T) (simp add: HostModifiedRdShared'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostModifiedRdOwnp_toggle: "HostModifiedRdOwn' T 1 = map toggle (HostModifiedRdOwn' (toggle T) 0)"
  by (cases T) (simp add: HostModifiedRdOwn'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSharedRdOwnp_toggle: "HostSharedRdOwn' T 1 = map toggle (HostSharedRdOwn' (toggle T) 0)"
  by (cases T) (simp add: HostSharedRdOwn'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSharedRdOwnSelfp_toggle: "HostSharedRdOwnSelf' T 1 = map toggle (HostSharedRdOwnSelf' (toggle T) 0)"
  by (cases T) (simp add: HostSharedRdOwnSelf'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSDDatap_toggle: "HostSDData' T 1 = map toggle (HostSDData' (toggle T) 0)"
  by (cases T) (simp add: HostSDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSADDatap_toggle: "HostSADData' T 1 = map toggle (HostSADData' (toggle T) 0)"
  by (cases T) (simp add: HostSADData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMDDatap_toggle: "HostMDData' T 1 = map toggle (HostMDData' (toggle T) 0)"
  by (cases T) (simp add: HostMDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostIDDatap_toggle: "HostIDData' T 1 = map toggle (HostIDData' (toggle T) 0)"
  by (cases T) (simp add: HostIDData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMADDatap_toggle: "HostMADData' T 1 = map toggle (HostMADData' (toggle T) 0)"
  by (cases T) (simp add: HostMADData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSADRspIFwdMp_toggle: "HostSADRspIFwdM' T 1 = map toggle (HostSADRspIFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostSADRspIFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSADRspSFwdMp_toggle: "HostSADRspSFwdM' T 1 = map toggle (HostSADRspSFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostSADRspSFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMADRspIFwdMp_toggle: "HostMADRspIFwdM' T 1 = map toggle (HostMADRspIFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostMADRspIFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMARspIFwdMp_toggle: "HostMARspIFwdM' T 1 = map toggle (HostMARspIFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostMARspIFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSARspIFwdMp_toggle: "HostSARspIFwdM' T 1 = map toggle (HostSARspIFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostSARspIFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSARspSFwdMp_toggle: "HostSARspSFwdM' T 1 = map toggle (HostSARspSFwdM' (toggle T) 0)"
  by (cases T) (simp add: HostSARspSFwdM'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostIBDataPreviousp_toggle: "HostIBDataPrevious' T 1 = map toggle (HostIBDataPrevious' (toggle T) 0)"
  by (cases T) (simp add: HostIBDataPrevious'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostSBDatap_toggle: "HostSBData' T 1 = map toggle (HostSBData' (toggle T) 0)"
  by (cases T) (simp add: HostSBData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMBDatap_toggle: "HostMBData' T 1 = map toggle (HostMBData' (toggle T) 0)"
  by (cases T) (simp add: HostMBData'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostInvalidDirtyEvictp_toggle: "HostInvalidDirtyEvict' T 1 = map toggle (HostInvalidDirtyEvict' (toggle T) 0)"
  by (cases T) (simp add: HostInvalidDirtyEvict'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma HostMARspIHitSEp_toggle: "HostMARspIHitSE' T 1 = map toggle (HostMARspIHitSE' (toggle T) 0)"
  by (cases T) (simp add: HostMARspIHitSE'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma SIACGOp_toggle: "SIACGO' T 1 = map toggle (SIACGO' (toggle T) 0)"
  by (cases T) (simp add: SIACGO'_def Let_def split: list.splits nat.splits option.splits DeviceID.splits)

lemma allTransitions'_toggle:
  "concat (map (\<lambda>f. f T 1) allTransitions') = map toggle (concat (map (\<lambda>f. f (toggle T) 0) allTransitions'))"
  unfolding allTransitions'_def
  by (simp only: list.map concat.simps map_append InvalidLoadp_toggle SharedLoadp_toggle InvalidStorep_toggle SharedStorep_toggle SharedEvictp_toggle SharedEvictDatap_toggle ModifiedEvictp_toggle SharedSnpInvp_toggle ISDSnpInvp_toggle ISDDatap_toggle ISDIDatap_toggle IMADDatap_toggle SMADDatap_toggle IMADGOp_toggle ISADGOp_toggle ISADDatap_toggle SMADGOp_toggle SMAGOp_toggle SMADSnpInvp_toggle SMDDatap_toggle IMAGOp_toggle ISAGOp_toggle ModifiedStorep_toggle ModifiedLoadp_toggle SIAGO_WritePullp_toggle SIAGO_WritePullDropp_toggle IIAGO_WritePullDropp_toggle IIAGO_WritePullp_toggle IMDDatap_toggle MIASnpDataInvalidp_toggle MIASnpDataSharedp_toggle MIASnpInvp_toggle MIAGO_WritePullp_toggle SIASnpInvp_toggle ModifiedSnpInvp_toggle ModifiedSnpDataSharedp_toggle ModifiedSnpDataInvalidp_toggle HostInvalidRdSharedp_toggle HostInvalidRdOwnp_toggle HostSharedRdSharedp_toggle HostShared_CleanEvict_NotLastDropp_toggle HostShared_CleanEvict_NotLastDatap_toggle HostShared_CleanEvict_Lastp_toggle HostShared_CleanEvictNoData_NotLastp_toggle HostShared_CleanEvictNoData_Lastp_toggle HostShared_DirtyEvictp_toggle HostModifiedDirtyEvictp_toggle HostModifiedRdSharedp_toggle HostModifiedRdOwnp_toggle HostSharedRdOwnp_toggle HostSharedRdOwnSelfp_toggle HostSDDatap_toggle HostSADDatap_toggle HostMDDatap_toggle HostIDDatap_toggle HostMADDatap_toggle HostSADRspIFwdMp_toggle HostSADRspSFwdMp_toggle HostMADRspIFwdMp_toggle HostMARspIFwdMp_toggle HostSARspIFwdMp_toggle HostSARspSFwdMp_toggle HostIBDataPreviousp_toggle HostSBDatap_toggle HostMBDatap_toggle HostInvalidDirtyEvictp_toggle HostMARspIHitSEp_toggle SIACGOp_toggle HostModifiedDirtyEvictPreviousp_toggle)

end
