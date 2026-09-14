theory TopLevelTheorem imports BasicInvariants  InitialState RuleSymmetry
FixInvalidLoad
FixSharedLoad
FixInvalidStore
FixSharedStore
FixSharedEvict
FixSharedEvictData
FixModifiedEvict
FixSharedSnpInv
FixISDSnpInv
FixISDData
FixISDIData
FixIMADData
FixISADData
FixIMADGO
FixSMADData
FixISADGO
FixSMADGO
FixSMAGO
FixSMADSnpInv
FixSMDData
FixIMAGO
FixISAGO
FixModifiedStore
FixModifiedLoad
FixSIAGO_WritePull
FixSIAGO_WritePullDrop
FixIIAGO_WritePull
FixIIAGO_WritePullDrop
FixIMDData
FixMIASnpDataInvalid
FixMIASnpDataShared
FixMIASnpInv
FixMIAGO_WritePull
FixSIASnpInv
FixModifiedSnpInv
FixModifiedSnpDataShared
FixModifiedSnpDataInvalid
FixModifiedDirtyEvict
FixInvalidRdShared
FixInvalidRdOwn
FixSharedRdShared
FixShared_CleanEvict_NotLastData
FixShared_CleanEvict_NotLastDrop
FixShared_CleanEvict_Last
FixShared_CleanEvictNoData_Last
FixShared_CleanEvictNoData_NotLast
FixSharedDirtyEvict
FixModifiedDirtyEvict
FixModifiedRdShared
FixModifiedRdOwn
FixSharedRdOwn
FixSharedRdOwnSelf
FixSDData
FixSADData
FixMDData
FixIDData
FixMADData
FixSADRspIFwdM
FixSADRspSFwdM
FixMADRspIFwdM
FixMARspIFwdM
FixSARspIFwdM
FixSARspSFwdM
FixSBData
FixIBData
FixMBData
FixInvalidDirtyEvict
FixMARspIHitSE
FixSIACGO

begin

thm image_insert

find_theorems "\<forall> _ \<in> set (_ @ _) . _ "

lemma my_map_concat: shows "List.concat (List.map (\<lambda>f. f T 0) ([t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28, t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40, t41, t42, t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54, t55, t56, t57, t58, t59, t60, t61, t62, t63, t64, t65, t66, t67, t68] )) =
   t1 T 0 @ t2 T 0 @ t3 T 0 @ t4 T 0 @ t5 T 0 @ t6 T 0 @ t7 T 0 @ t8 T 0 @ t9 T 0 @ t10 T 0 @ t11 T 0 @ t12 T 0 @ t13 T 0 @ t14 T 0 @ t15 T 0 @ t16 T 0 @ t17 T 0 @ t18 T 0 @ t19 T 0 @ t20 T 0 @ t21 T 0 @ t22 T 0 @ t23 T 0 @ t24 T 0 @ t25 T 0 @ t26 T 0 @ t27 T 0 @ t28 T 0 @ t29 T 0 @ t30 T 0 @ t31 T 0 @ t32 T 0 @ t33 T 0 @ t34 T 0 @ t35 T 0 @ t36 T 0 @ t37 T 0 @ t38 T 0 @ t39 T 0 @ t40 T 0 @ t41 T 0 @ t42 T 0 @ t43 T 0 @ t44 T 0 @ t45 T 0 @ t46 T 0 @ t47 T 0 @ t48 T 0 @ t49 T 0 @ t50 T 0 @ t51 T 0 @ t52 T 0 @ t53 T 0 @ t54 T 0 @ t55 T 0 @ t56 T 0 @ t57 T 0 @ t58 T 0 @ t59 T 0 @ t60 T 0 @ t61 T 0 @ t62 T 0 @ t63 T 0 @ t64 T 0 @ t65 T 0 @ t66 T 0 @ t67 T 0 @ t68 T 0"
  by simp




lemma my_set_concat_split_66elems: shows "(\<forall> T' \<in> set (l1 @ l2 @ l3 @ l4 @ l5 @ l6 @ l7 @ l8 @ l9 @ l10 @ l11 @ l12 @ l13 @ l14 @ l15 @ l16 @ l17 @ l18 @ l19 @ l20 @ l21 @ l22 @ l23 @ l24 @ l25 @ l26 @ l27 @ l28 @ l29 @ l30 @ l31 @ l32 @ l33 @ l34 @ l35 @ l36 @ l37 @ l38 @ l39 @ l40 @ l41 @ l42 @ l43 @ l44 @ l45 @ l46 @ l47 @ l48 @ l49 @ l50 @ l51 @ l52 @ l53 @ l54 @ l55 @ l56 @ l57 @ l58 @ l59 @ l60 @ l61 @ l62 @ l63 @ l64 @ l65 @ l66 @ l67 @ l68). P T') = ((\<forall> T' \<in> set l1. P T') \<and> (\<forall> T' \<in> set l2. P T') \<and> (\<forall> T' \<in> set l3. P T') \<and> (\<forall> T' \<in> set l4. P T') \<and> (\<forall> T' \<in> set l5. P T') \<and> (\<forall> T' \<in> set l6. P T') \<and> (\<forall> T' \<in> set l7. P T') \<and> (\<forall> T' \<in> set l8. P T') \<and> (\<forall> T' \<in> set l9. P T') \<and> (\<forall> T' \<in> set l10. P T') \<and> (\<forall> T' \<in> set l11. P T') \<and> (\<forall> T' \<in> set l12. P T') \<and> (\<forall> T' \<in> set l13. P T') \<and> (\<forall> T' \<in> set l14. P T') \<and> (\<forall> T' \<in> set l15. P T') \<and> (\<forall> T' \<in> set l16. P T') \<and> (\<forall> T' \<in> set l17. P T') \<and> (\<forall> T' \<in> set l18. P T') \<and> (\<forall> T' \<in> set l19. P T') \<and> (\<forall> T' \<in> set l20. P T') \<and> (\<forall> T' \<in> set l21. P T') \<and> (\<forall> T' \<in> set l22. P T') \<and> (\<forall> T' \<in> set l23. P T') \<and> (\<forall> T' \<in> set l24. P T') \<and> (\<forall> T' \<in> set l25. P T') \<and> (\<forall> T' \<in> set l26. P T') \<and> (\<forall> T' \<in> set l27. P T') \<and> (\<forall> T' \<in> set l28. P T') \<and> (\<forall> T' \<in> set l29. P T') \<and> (\<forall> T' \<in> set l30. P T') \<and> (\<forall> T' \<in> set l31. P T') \<and> (\<forall> T' \<in> set l32. P T') \<and> (\<forall> T' \<in> set l33. P T') \<and> (\<forall> T' \<in> set l34. P T') \<and> (\<forall> T' \<in> set l35. P T') \<and> (\<forall> T' \<in> set l36. P T') \<and> (\<forall> T' \<in> set l37. P T') \<and> (\<forall> T' \<in> set l38. P T') \<and> (\<forall> T' \<in> set l39. P T') \<and> (\<forall> T' \<in> set l40. P T') \<and> (\<forall> T' \<in> set l41. P T') \<and> (\<forall> T' \<in> set l42. P T') \<and> (\<forall> T' \<in> set l43. P T') \<and> (\<forall> T' \<in> set l44. P T') \<and> (\<forall> T' \<in> set l45. P T') \<and> (\<forall> T' \<in> set l46. P T') \<and> (\<forall> T' \<in> set l47. P T') \<and> (\<forall> T' \<in> set l48. P T') \<and> (\<forall> T' \<in> set l49. P T') \<and> (\<forall> T' \<in> set l50. P T') \<and> (\<forall> T' \<in> set l51. P T') \<and> (\<forall> T' \<in> set l52. P T') \<and> (\<forall> T' \<in> set l53. P T') \<and> (\<forall> T' \<in> set l54. P T') \<and> (\<forall> T' \<in> set l55. P T') \<and> (\<forall> T' \<in> set l56. P T') \<and> (\<forall> T' \<in> set l57. P T') \<and> (\<forall> T' \<in> set l58. P T') \<and> (\<forall> T' \<in> set l59. P T') \<and> (\<forall> T' \<in> set l60. P T') \<and> (\<forall> T' \<in> set l61. P T') \<and> (\<forall> T' \<in> set l62. P T') \<and> (\<forall> T' \<in> set l63. P T') \<and> (\<forall> T' \<in> set l64. P T') \<and> (\<forall> T' \<in> set l65. P T') \<and> (\<forall> T' \<in> set l66. P T') \<and> (\<forall> T' \<in> set l67. P T') \<and> (\<forall> T' \<in> set l68. P T'))"
  proof (-)
  show goal1: "(\<forall>T'\<in>set (l1 @ l2 @ l3 @ l4 @ l5 @ l6 @ l7 @ l8 @ l9 @ l10 @ l11 @ l12 @ l13 @ l14 @ l15 @ l16 @ l17 @ l18 @ l19 @ l20 @ l21 @ l22 @ l23 @ l24 @ l25 @ l26 @ l27 @ l28 @ l29 @ l30 @ l31 @ l32 @ l33 @ l34 @ l35 @ l36 @ l37 @ l38 @ l39 @ l40 @ l41 @ l42 @ l43 @ l44 @ l45 @ l46 @ l47 @ l48 @ l49 @ l50 @ l51 @ l52 @ l53 @ l54 @ l55 @ l56 @ l57 @ l58 @ l59 @ l60 @ l61 @ l62 @ l63 @ l64 @ l65 @ l66 @ l67 @ l68). P T') = ((\<forall>T'\<in>set l1. P T') \<and> (\<forall>T'\<in>set l2. P T') \<and> (\<forall>T'\<in>set l3. P T') \<and> (\<forall>T'\<in>set l4. P T') \<and> (\<forall>T'\<in>set l5. P T') \<and> (\<forall>T'\<in>set l6. P T') \<and> (\<forall>T'\<in>set l7. P T') \<and> (\<forall>T'\<in>set l8. P T') \<and> (\<forall>T'\<in>set l9. P T') \<and> (\<forall>T'\<in>set l10. P T') \<and> (\<forall>T'\<in>set l11. P T') \<and> (\<forall>T'\<in>set l12. P T') \<and> (\<forall>T'\<in>set l13. P T') \<and> (\<forall>T'\<in>set l14. P T') \<and> (\<forall>T'\<in>set l15. P T') \<and> (\<forall>T'\<in>set l16. P T') \<and> (\<forall>T'\<in>set l17. P T') \<and> (\<forall>T'\<in>set l18. P T') \<and> (\<forall>T'\<in>set l19. P T') \<and> (\<forall>T'\<in>set l20. P T') \<and> (\<forall>T'\<in>set l21. P T') \<and> (\<forall>T'\<in>set l22. P T') \<and> (\<forall>T'\<in>set l23. P T') \<and> (\<forall>T'\<in>set l24. P T') \<and> (\<forall>T'\<in>set l25. P T') \<and> (\<forall>T'\<in>set l26. P T') \<and> (\<forall>T'\<in>set l27. P T') \<and> (\<forall>T'\<in>set l28. P T') \<and> (\<forall>T'\<in>set l29. P T') \<and> (\<forall>T'\<in>set l30. P T') \<and> (\<forall>T'\<in>set l31. P T') \<and> (\<forall>T'\<in>set l32. P T') \<and> (\<forall>T'\<in>set l33. P T') \<and> (\<forall>T'\<in>set l34. P T') \<and> (\<forall>T'\<in>set l35. P T') \<and> (\<forall>T'\<in>set l36. P T') \<and> (\<forall>T'\<in>set l37. P T') \<and> (\<forall>T'\<in>set l38. P T') \<and> (\<forall>T'\<in>set l39. P T') \<and> (\<forall>T'\<in>set l40. P T') \<and> (\<forall>T'\<in>set l41. P T') \<and> (\<forall>T'\<in>set l42. P T') \<and> (\<forall>T'\<in>set l43. P T') \<and> (\<forall>T'\<in>set l44. P T') \<and> (\<forall>T'\<in>set l45. P T') \<and> (\<forall>T'\<in>set l46. P T') \<and> (\<forall>T'\<in>set l47. P T') \<and> (\<forall>T'\<in>set l48. P T') \<and> (\<forall>T'\<in>set l49. P T') \<and> (\<forall>T'\<in>set l50. P T') \<and> (\<forall>T'\<in>set l51. P T') \<and> (\<forall>T'\<in>set l52. P T') \<and> (\<forall>T'\<in>set l53. P T') \<and> (\<forall>T'\<in>set l54. P T') \<and> (\<forall>T'\<in>set l55. P T') \<and> (\<forall>T'\<in>set l56. P T') \<and> (\<forall>T'\<in>set l57. P T') \<and> (\<forall>T'\<in>set l58. P T') \<and> (\<forall>T'\<in>set l59. P T') \<and> (\<forall>T'\<in>set l60. P T') \<and> (\<forall>T'\<in>set l61. P T') \<and> (\<forall>T'\<in>set l62. P T') \<and> (\<forall>T'\<in>set l63. P T') \<and> (\<forall>T'\<in>set l64. P T') \<and> (\<forall>T'\<in>set l65. P T') \<and> (\<forall>T'\<in>set l66. P T') \<and> (\<forall>T'\<in>set l67. P T') \<and> (\<forall>T'\<in>set l68. P T'))" apply  (auto)
 done
qed

(*
lemma my_set_concat_Lall: shows "(\<forall> T' \<in> set (l1 @ l2 @ l3). P T') = ((Lall l1 P) \<and> (Lall  l2 P) \<and> (Lall l3 P))"
  sorry
*)

lemma Ball_Lall: shows "Ball (set ls) P = Lall ls P"
  apply(induct ls)
   apply simp
  by (smt (verit) Lall.elims(1) Lall.simps(2) Lall.simps(3) list.set_cases list.set_intros(1) list.set_intros(2) set_ConsD)



theorem all_transitions_coherent: assumes "SWMR_state_machine T"
  shows " \<forall> T' \<in> set (List.concat (List.map (\<lambda> f. f T 0) allTransitions')). SWMR_state_machine T'"
  unfolding allTransitions'_def my_map_concat my_set_concat_split_66elems 
  apply(simp only: Ball_Lall)
  apply(insert assms)

  proof (intro conjI)
  show goal1: "Lall (InvalidLoad' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) InvalidLoad_coherent assms) done
  show goal2: "Lall (SharedLoad' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SharedLoad_coherent assms) done
  show goal3: "Lall (InvalidStore' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) InvalidStore_coherent assms) done
  show goal4: "Lall (SharedStore' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SharedStore_coherent assms) done
  show goal5: "Lall (SharedEvict' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SharedEvict_coherent assms) done
  show goal6: "Lall (ModifiedEvict' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ModifiedEvict_coherent assms) done
  show goal7: "Lall (SharedSnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SharedSnpInv_coherent assms) done
  show goal8: "Lall (ISDSnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISDSnpInv_coherent assms) done
  show goal9: "Lall (ISDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISDData_coherent assms) done
  show goal10: "Lall (ISDIData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISDIData_coherent assms) done
  show goal11: "Lall (IMADData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IMADData_coherent assms) done
  show goal12: "Lall (SMADData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SMADData_coherent assms) done
  show goal13: "Lall (IMADGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IMADGO_coherent assms) done
  show goal14: "Lall (ISADGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISADGO_coherent assms) done
  show goal15: "Lall (ISADData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISADData_coherent assms) done
  show goal16: "Lall (SMADGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SMADGO_coherent assms) done
  show goal17: "Lall (SMAGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SMAGO_coherent assms) done
  show goal18: "Lall (SMADSnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SMADSnpInv_coherent assms) done
  show goal19: "Lall (SMDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SMDData_coherent assms) done
  show goal20: "Lall (IMAGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IMAGO_coherent assms) done
  show goal21: "Lall (ISAGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ISAGO_coherent assms) done
  show goal22: "Lall (ModifiedStore' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ModifiedStore_coherent assms) done
  show goal23: "Lall (ModifiedLoad' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ModifiedLoad_coherent assms) done
  show goal24: "Lall (SIAGO_WritePull' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SIAGO_WritePull_coherent assms) done
  show goal25: "Lall (SIAGO_WritePullDrop' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SIAGO_WritePullDrop_coherent assms) done
  show goal26: "Lall (IIAGO_WritePullDrop' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IIAGO_WritePullDrop_coherent assms) done
  show goal27: "Lall (IIAGO_WritePull' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IIAGO_WritePull_coherent assms) done
  show goal28: "Lall (IMDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) IMDData_coherent assms) done
  show goal29: "Lall (MIASnpDataInvalid' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) MIASnpDataInvalid'_coherent assms) done
  show goal30: "Lall (MIASnpDataShared' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) MIASnpDataShared'_coherent assms) done
  show goal31: "Lall (MIASnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) MIASnpInv'_coherent assms) done
  show goal32: "Lall (MIAGO_WritePull' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) MIAGO_WritePull_coherent assms) done
  show goal33: "Lall (SIASnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) SIASnpInv_coherent assms) done
  show goal34: "Lall (ModifiedSnpInv' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) ModifiedSnpInv'_coherent assms) done
  show goal35: "Lall (ModifiedSnpDataShared' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) FixModifiedSnpDataShared.ModifiedSnpDataInvalid'_coherent assms) done
  show goal36: "Lall (ModifiedSnpDataInvalid' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) FixModifiedSnpDataInvalid.ModifiedSnpDataInvalid'_coherent assms) done
  show goal37: "Lall (HostInvalidRdShared' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostInvalidRdShared'_coherent assms) done
  show goal38: "Lall (HostInvalidRdOwn' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostInvalidRdOwn'_coherent assms) done
  show goal39: "Lall (HostSharedRdShared' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSharedRdShared'_coherent assms) done
  show goal40: "Lall (HostShared_CleanEvict_NotLastDrop' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_CleanEvict_NotLastDrop'_coherent assms) done
  show goal41: "Lall (HostShared_CleanEvict_NotLastData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_CleanEvict_NotLastData'_coherent assms) done
  show goal42: "Lall (HostShared_CleanEvict_Last' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_CleanEvict_Last'_coherent assms) done
  show goal43: "Lall (HostShared_CleanEvictNoData_NotLast' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_CleanEvictNoData_NotLast'_coherent assms) done
  show goal44: "Lall (HostShared_CleanEvictNoData_Last' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_CleanEvictNoData_Last'_coherent assms) done
  show goal45: "Lall (HostShared_DirtyEvict' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostShared_DirtyEvict'_coherent assms) done
  show goal46: "Lall (HostModifiedDirtyEvict' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostModifiedDirtyEvict'_coherent assms) done
  show goal47: "Lall (HostModifiedRdShared' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostModifiedRdShared'_coherent assms) done
  show goal48: "Lall (HostModifiedRdOwn' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostModifiedRdOwn'_coherent assms) done
  show goal49: "Lall (HostSharedRdOwn' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSharedRdOwn'_coherent assms) done
  show goal50: "Lall (HostSharedRdOwnSelf' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSharedRdOwnSelf'_coherent assms) done
  show goal51: "Lall (HostSDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSDData'_coherent assms) done
  show goal52: "Lall (HostSADData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSADData'_coherent assms) done
  show goal53: "Lall (HostMDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMDData'_coherent assms) done
  show goal54: "Lall (HostIDData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostIDData'_coherent assms) done
  show goal55: "Lall (HostMADData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMADData'_coherent assms) done
  show goal56: "Lall (HostSADRspIFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSADRspIFwdM_coherent assms) done
  show goal57: "Lall (HostSADRspSFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSADRspSFwdM_coherent assms) done
  show goal58: "Lall (HostMADRspIFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMADRspIFwdM_coherent assms) done
  show goal59: "Lall (HostMARspIFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMARspIFwdM_coherent assms) done
  show goal60: "Lall (HostSARspIFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSARspIFwdM'_coherent assms) done
  show goal61: "Lall (HostSARspSFwdM' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSARspSFwdM'_coherent assms) done
  show goal62: "Lall (HostIBDataPrevious' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostIBDataPrevious'_coherent assms) done
  show goal63: "Lall (HostSBData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostSBData'_coherent assms) done
  show goal64: "Lall (HostMBData' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMBData'_coherent assms) done
  show goal65: "Lall (HostInvalidDirtyEvict' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostInvalidDirtyEvict'_coherent assms) done
  show goal66: "Lall (HostMARspIHitSE' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that apply (smt (verit) HostMARspIHitSE_coherent assms) done
  show goal67: "Lall (SIACGO' T 0) SWMR_state_machine"
    if "SWMR_state_machine T"
    using that by (metis SIACGO_coherent) 
  show goal68: "Lall (SharedEvictData' T 0) SWMR_state_machine"
    by (metis SharedEvictData_coherent assms)
qed
thm allTransitions'_def

text \<open>The rule lemmas above are stated for device index 0.  The instance of every rule for
device index 1 is the mirror image of its instance for index 0 (@{thm allTransitions'_toggle}),
and the invariant is symmetric under swapping the two devices (@{thm symmetry}), so the
index-1 instances preserve the invariant as well.\<close>

theorem all_transitions_coherent_dev2: assumes "SWMR_state_machine T"
  shows "\<forall> T' \<in> set (List.concat (List.map (\<lambda> f. f T 1) allTransitions')). SWMR_state_machine T'"
proof
  fix T' assume "T' \<in> set (List.concat (List.map (\<lambda> f. f T 1) allTransitions'))"
  then obtain T'' where T'': "T'' \<in> set (List.concat (List.map (\<lambda> f. f (toggle T) 0) allTransitions'))"
    and T'_eq: "T' = toggle T''"
    by (auto simp only: allTransitions'_toggle set_map image_iff)
  have sym: "SWMR_state_machine (toggle T)" using assms by (rule symmetry)
  have "SWMR_state_machine T''" using all_transitions_coherent[OF sym] T'' by blast
  then show "SWMR_state_machine T'" unfolding T'_eq by (rule symmetry)
qed

lemma set_concat_both:
  "set (concat (map (\<lambda>f. f T 0 @ f T 1) L)) = set (concat (map (\<lambda>f. f T 0) L)) \<union> set (concat (map (\<lambda>f. f T 1) L))"
  by (induct L) auto

theorem all_transitions_coherent_both: assumes "SWMR_state_machine T"
  shows "\<forall> T' \<in> set (concat (map (\<lambda> f. f T 0 @ f T 1) allTransitions')). SWMR_state_machine T'"
  using all_transitions_coherent[OF assms] all_transitions_coherent_dev2[OF assms]
  unfolding set_concat_both by blast

text \<open>Reachability: zero or more transitions of either device.\<close>

inductive allTransStar :: "Type1State \<Rightarrow> Type1State \<Rightarrow> bool" where
  refl: "allTransStar T T"
| step: "allTransStar T T' \<Longrightarrow> T'' \<in> set (concat (map (\<lambda>f. f T' 0 @ f T' 1) allTransitions')) \<Longrightarrow> allTransStar T T''"

theorem SWMR_state_machine_CXL_cache: assumes "allTransStar T T'" and "initial_state T" shows "SWMR_state_machine T'"
  using assms
proof (induct rule: allTransStar.induct)
  case (refl T)
  then show ?case using initial_valid by blast
next
  case (step T T' T'')
  then show ?case using all_transitions_coherent_both by blast
qed

corollary SWMR_CXL_cache: assumes "allTransStar T T'" and "initial_state T" shows "SWMR T'"
proof -
  have SWMR_plus: "SWMR_state_machine T'"
    by (metis SWMR_state_machine_CXL_cache assms(1) assms(2))
  show ?thesis
    apply(insert SWMR_plus)
    unfolding SWMR_state_machine_def
    apply(elim conjE)
    by assumption
qed

(*this is the "SWMR" definition in paper*)
definition SWMR_pp :: "Type1State \<Rightarrow> bool" where [simp]: 
  "SWMR_pp T = ( (CSTATE Modified T 0 \<longrightarrow>  \<not> CSTATE Shared T 1) \<and>  
              (CSTATE Modified T 1 \<longrightarrow>  \<not> CSTATE Shared T 0) \<and> 
              (CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1) \<and>
              (CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0) )"

corollary SWMR_pplus_cache: assumes "allTransStar T T'" and "initial_state T" shows "SWMR_pp T'"
proof -
  have inv: "SWMR_state_machine T'"
    by (metis SWMR_state_machine_CXL_cache assms(1) assms(2))
  have a: "SWMR T'" by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have b: "CSTATE Modified T' 0 \<longrightarrow> \<not>CSTATE Modified T' 1"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  have c: "CSTATE Modified T' 1 \<longrightarrow> \<not>CSTATE Modified T' 0"
    by (insert inv, unfold SWMR_state_machine_def, elim conjE, assumption)
  show ?thesis using a b c unfolding SWMR_pp_def SWMR_def by auto
qed

end
