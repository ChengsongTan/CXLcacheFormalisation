theory FixISDIData  imports BasicInvariants Super2023 begin
sledgehammer_params[timeout=10, dont_minimize, "try0" = false]


lemma devcache2_sequals1_invariant: shows "devcache2 ( T [ 0 s= Invalid] ) = devcache2 T"
  by simp



lemma devcache2_copy_hdata1_invariant: shows "devcache2 ( T [ 0 :=dd msg] ) = devcache2 T"
  by simp

lemma devcache2_copy_perform1_invariant: shows "devcache2 ( T [ -=i 0] ) = devcache2 T"
  apply simp
  apply(case_tac "program1 T")
   apply simp
  apply simp 
  done

lemma devcache2_consume_hdata1_invariant: shows "devcache2 ( T [ 0 -=devd ] ) = devcache2 T"
  by simp



lemma devcache1_ISDIData_invariant_aux1: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] )) \<noteq> Modified" 
  apply(case_tac "program1 T")
   apply simp+
  done
  


lemma devcache1_ISDIData_invariant_aux: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T  [ -=i 0] [ 0 -=devd ])) \<noteq> Modified" 
  using devcache1_ISDIData_invariant_aux1 by auto

  


lemma devcache1_ISDIData_invariant: shows "CLEntry.block_state  (devcache1 T) = Shared \<Longrightarrow> 
  CLEntry.block_state (devcache1 ( T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) \<noteq> Modified" 
  apply(subgoal_tac "CLEntry.block_state  (devcache1 (T  [ 0 :=dd msg ])) = Shared")
  using devcache1_ISDIData_invariant_aux apply blast
  by simp



lemma CSTATE_ISDIData_otherside: shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
  
  using CSTATE_def devcache2_consume_hdata1_invariant devcache2_copy_hdata1_invariant devcache2_copy_perform1_invariant devcache2_sequals1_invariant by presburger

lemma ISDIData_Shared_aux1: shows "nextLoad T 0 \<Longrightarrow> CSTATE X T 0 = CSTATE X (T [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
 apply simp
  apply(case_tac x2)
  apply(case_tac n)
  apply simp+
  done

lemma nextLoad_devstate: shows "nextLoad T i = nextLoad (T [0 s= mesi]) i"
  by simp


lemma ISDIData_Shared: shows " CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
  apply(case_tac "program1 T")
   apply simp+
  done


lemma reqs1_ISDIData: shows "reqs1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs1 T"
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
 apply simp
  apply(case_tac x2)
  apply(case_tac n)
  apply simp+
  done

lemma reqs2_ISDIData: shows "reqs2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = reqs2 T"
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
 apply simp
  apply(case_tac x2)
  apply(case_tac n)
  apply simp+
  done

lemma nextReqIs_ISDIData: shows "nextReqIs X T i = nextReqIs X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
  apply(case_tac i) 
  using nextReqIs_def reqs1_ISDIData apply presburger  
  using nextReqIs_def old.nat.distinct(2) reqs2_ISDIData by presburger

lemma ISDIData_nextGOPendingIs: shows "nextGOPendingIs X T i = nextGOPendingIs X ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
  apply(case_tac i)
   apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  by simp+

lemma ISDIData_nextEvict: shows "nextEvict T 1 = nextEvict ( T [ 0 s= mesi] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"

   apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done


lemma ISDIData_nextLoad: shows "nextLoad T 1 = nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
  apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done


lemma ISDIData_HSTATE: shows "(HSTATE X ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = HSTATE X T"
  apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done

lemma ISDIData_HSTATES: shows "(HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or>
  HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) = (HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ModifiedM T)"
  apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done

lemma ISDIData_nextSnoopIs: shows "nextSnoopIs  X T i = nextSnoopIs X ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i"
  apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done

lemma ISDIData_nextStore_otherside: shows "nextStore T 1 = nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
   apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done




lemma device_perform_op_snps2:   " snps2  T  = snps2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done


lemma device_perform_op_snps1:   " snps1  T  = snps1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done


lemma device_perform_op_reqs1:   " reqs1  T  = reqs1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

  

lemma device_perform_op_reqs2:   " reqs2  T  = reqs2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
   apply (cases "program1 T")
 apply simp
   apply simp
  done

lemma device_perform_op_reqresps1:   " reqresps1  T  = reqresps1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

  
lemma device_perform_op_reqresps2:   " reqresps2  T  = reqresps2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done



lemma device_perform_op_snpresps1:   " snpresps1  T  = snpresps1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

  
lemma device_perform_op_snpresps2:   " snpresps2  T  = snpresps2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

lemma device_perform_op_dthdatas1:   " dthdatas1  T  = dthdatas1  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

  
lemma device_perform_op_dthdatas2:   " dthdatas2  T  = dthdatas2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done


lemma device_perform_op_htddatas1:   " length (htddatas1  T) \<le> 1 \<Longrightarrow>   (htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) = []"
  apply (cases "program1 T")  
  apply simp
subgoal subgoal  apply (auto split: List.list.split) done  done
(* \./proofs/NewISDIData\111413361672714192\.txt *)

 apply simp
   apply(case_tac a)
 apply simp+ 
 apply (metis bot_nat_0.extremum le_Suc_eq le_antisym length_0_conv length_Cons list.sel(2) list.sel(3) nat.inject neq_Nil_conv tl_def)
   apply simp
   apply(case_tac x2)
 apply simp
 apply(case_tac n)
  apply simp
  apply (metis bot_nat_0.extremum length_Cons list.exhaust list.sel(2) list.sel(3) not_less_eq_eq tl_def)
 apply simp
  apply (metis Nat.add_0_right le_add2 length_Cons list.exhaust list.sel(2) list.sel(3) not_less_eq_eq tl_def)
   apply simp
  apply (metis bot_nat_0.extremum length_Cons list.exhaust list.sel(2) list.sel(3) not_less_eq_eq tl_def)
  apply(simp)
  by (metis Suc_le_mono bot_nat_0.extremum le_antisym length_Cons list.exhaust list.sel(2) list.sel(3) nat.distinct(1) tl_def)


  
lemma device_perform_op_htddatas2:   " htddatas2  T  = htddatas2  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
 apply (cases "program1 T")
 apply simp
   apply simp
  done

lemma device_perform_op_nextHTDDataPending:   " nextHTDDataPending  T 1 = nextHTDDataPending  ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
   apply(case_tac "program1 T")
 apply simp
   apply(case_tac a)
  apply simp
 apply(case_tac x2)
  apply(case_tac n)
  apply simp
  apply simp
 apply simp
   apply simp
  done





lemma nextGOPending_DeviceISDIData: "nextGOPending (  T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) i = nextGOPending T i"
apply(case_tac i)
  using device_perform_op_reqresps1 nextGOPending_def apply presburger  
  using device_perform_op_reqresps2 nextGOPending_def by presburger








lemma nextLoad_DeviceISDIData: "nextLoad (  T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ] ) 1 = nextLoad T 1"  
  using ISDIData_nextLoad by presburger


lemma ISDIData'_coherent_aux_simpler: assumes "SWMR_state_machine T \<and> CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 " shows 
"SWMR_state_machine ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
proof -
have i0: "SWMR T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i1x: "CSTATE ISDI T 0"  by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i2x: "nextHTDDataPending T 0"  by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i3: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i4: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i5: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i6: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i10: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i11: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i12: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i13: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i14: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i15: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i16: "C_H_state IMAD (nextReqIs RdOwn) Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i17: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i18: "C_H_state IMAD (nextReqIs RdOwn) Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i19: "C_H_state Invalid nextStore Modified SAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i20: "C_H_state Invalid nextStore Modified SA T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i21: "C_H_state Invalid nextStore Modified SD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i22: "HSTATE SharedM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i23: "HSTATE SD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i24: "HSTATE MD T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i25: "C_msg_not RdShared IMAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i26: "C_msg_not RdShared Invalid T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i27: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i28: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i29: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i30: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i31: "C_state_not MIA RdShared T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i35: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i36: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i37: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i39: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i40: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i41: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i46: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i47: "C_msg_state RdShared ISAD T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i49: "C_not_C_msg Modified ISAD nextGOPending T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i50: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i51: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i52: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i55: "snps2 T \<noteq> [] \<longrightarrow> reqs1 T = [] \<and> snpresps2 T = [] \<and> dthdatas2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i56: "snps1 T \<noteq> [] \<longrightarrow> reqs2 T = [] \<and> snpresps1 T = [] \<and> dthdatas1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i57: "length (reqs1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i58: "length (reqs2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i59: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i60: "length (snps2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i61: "length (snps1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611old: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612old: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613old: "(CSTATE Invalid T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614old: "(CSTATE Invalid T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615old: "(CSTATE Shared T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616old: "(CSTATE Shared T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617old: "(CSTATE IIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618old: "(CSTATE IIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i68: "CSTATE Invalid T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i69: "CSTATE Invalid T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i70: "CSTATE Shared T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i71: "CSTATE Shared T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i72: "CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i73: "CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i74: "CSTATE ISD T 0 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i75: "CSTATE ISD T 1 \<longrightarrow> \<not>HSTATE ModifiedM T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i76: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) T" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i77: "length (htddatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i78: "length (htddatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i79: "CSTATE ISD T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i80: "CSTATE ISD T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)



have i81: "CSTATE ISD T 0 \<longrightarrow> reqs1 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i82: "CSTATE ISD T 1 \<longrightarrow> reqs2 T = []" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i83: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i84: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> reqs2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i85: "(length (reqresps1 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i86: "(length (reqresps2 T) \<le> 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i87: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0)  \<longrightarrow> snps1 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i88: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1)  \<longrightarrow> snps2 T = [] )" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)

have i89: "(CSTATE MIA T 0 \<and> (nextGOPendingIs GO_WritePull T 0) \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i90: "(CSTATE MIA T 1 \<and> (nextGOPendingIs GO_WritePull T 1) \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i91: "(CSTATE ISAD T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i92: "(CSTATE ISAD T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i93: "(C_msg_P_same MIA  (nextReqIs DirtyEvict) (nextEvict) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i94: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i95: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i98: "(reqs1 T \<noteq> [] \<longrightarrow> snpresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i99: "(reqs2 T \<noteq> [] \<longrightarrow> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i100: "(reqs1 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i101: "(reqs2 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i751old: " (CSTATE ISD T 0 \<longrightarrow> nextLoad T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+
have i752old: " (CSTATE ISD T 1 \<longrightarrow> nextLoad T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)+

 
 have i104: "(reqs1 T \<noteq> [] \<longrightarrow> reqresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i105: "(reqs2 T \<noteq> [] \<longrightarrow> reqresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i106: "(HSTATE SAD T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISAD T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i107: "(HSTATE ModifiedM T \<longrightarrow> \<not>CSTATE Shared T 0 \<and> \<not>CSTATE Shared T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i108: "(HSTATE SD T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i109: "(HSTATE SD T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i110: "(length (dthdatas1 T ) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i111: "(length (dthdatas2 T ) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i112: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE ISAD T 1 \<or> CSTATE ISD T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i113: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE ISAD T 0 \<or> CSTATE ISD T 0)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i114: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 \<or> CSTATE ISA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i115: "(HSTATE SA T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 \<or> CSTATE ISA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 
 
 have i118: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i119: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i120: "(length (snpresps1 T) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i121: "(length (snpresps2 T) \<le> 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i126: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i127: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i128: "(HSTATE MD T \<and> reqs1 T \<noteq> [] \<longrightarrow> dthdatas1 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i129: "(HSTATE MD T \<and> reqs2 T \<noteq> [] \<longrightarrow> dthdatas2 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i130: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i131: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i132: "(HSTATE ID T \<and> dthdatas1 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i133: "(HSTATE ID T \<and> dthdatas2 T \<noteq> [] \<longrightarrow> \<not>CSTATE MIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i136: "(dthdatas1 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i137: "(dthdatas2 T \<noteq> [] \<and> HSTATE SD T \<longrightarrow> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i138: "(CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i139: "(CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i142: "(C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i143: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i144: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SD T \<or> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i145: "(CSTATE ISAD T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i146: "(CSTATE ISAD T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i147: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i148: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i149: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i150: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i153: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i154: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i159: "(HSTATE ModifiedM T \<longrightarrow> snpresps2 T = [] \<and> snpresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i160: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISAD T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i161: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISAD T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i164: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i165: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i166: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i167: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i168: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqs2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i169: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqs1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i170: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i171: "(HSTATE SharedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i172: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i173: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i178: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i179: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i180: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i181: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE InvalidM T \<or> HSTATE ModifiedM T \<or> HSTATE SB T \<or> HSTATE ID T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i182: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i183: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i186: "(HSTATE SharedM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i187: "(CSTATE MIA T 1 \<longrightarrow> \<not>CSTATE MIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i188: "(CSTATE MIA T 0 \<longrightarrow> \<not>CSTATE MIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i189: "(HSTATE ModifiedM T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i190: "(nextDTHDataFrom  0 T \<longrightarrow> \<not> nextHTDDataPending T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i191: "(nextDTHDataFrom  1 T \<longrightarrow> \<not> nextHTDDataPending T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i192: "(nextDTHDataFrom 0 T \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i193: "(nextDTHDataFrom 1 T \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i194: "(HSTATE SA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i195: "(HSTATE SD T \<longrightarrow> \<not> CSTATE IIA T 0 \<or> \<not> CSTATE IIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i196: "(HSTATE SAD T \<longrightarrow> (\<not> CSTATE IIA T 0 \<or> nextSnpRespIs RspIFwdM T 0) \<and> (\<not> CSTATE IIA T 1 \<or> nextSnpRespIs RspIFwdM T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i197: "(CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i198: "(CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i199: "(CSTATE IIA T 0 \<longrightarrow> \<not> CSTATE IIA T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i200: "(CSTATE IIA T 1 \<longrightarrow> \<not> CSTATE IIA T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i301: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i302: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i305: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i306: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i307: "(HSTATE SharedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i308: "(HSTATE SharedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i309: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i310: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i313: "(HSTATE ModifiedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i314: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i315: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i316: "(CSTATE SIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i317: "(CSTATE SIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i318: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i319: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i320: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> HSTATE IB T \<or> HSTATE SB T \<or> HSTATE MB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i321: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i322: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextDTHDataFrom 1 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i323: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextDTHDataFrom 0 T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i324: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i325: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i326: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i327: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i328: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T \<or> HSTATE IB T \<or> HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i329: "(C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i332: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i333: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i334: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE SharedM T \<or> HSTATE SA T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i335: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextHTDDataPending T 1)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i336: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextHTDDataPending T 0)) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i337: "(C_not_C_msg Modified IMAD nextGOPending T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i338: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i339: "(CSTATE IMAD T 0 \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i340: "(CSTATE IMAD T 1 \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i341: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i342: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] ) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i343: "(snpresps1 T \<noteq> [] \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i344: "(snpresps2 T \<noteq> [] \<longrightarrow> reqresps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i345: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MA T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i346: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i347: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i348: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE MD T \<or> HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i349: "(CSTATE SMAD T 0 \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i350: "(CSTATE SMAD T 1 \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i351: "(C_msg_P_same IMA (nextGOPending) nextStore T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i352: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i353: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i354: "(C_msg_P_oppo IMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i355: "(C_msg_P_oppo SMA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i356: "(C_msg_P_oppo ISA (nextGOPending) (\<lambda> T i. \<not>nextSnoopPending T i) T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i357: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i358: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 
 
 have i365: "(C_msg_P_same SMA (nextGOPending) nextStore T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i366: "((CSTATE SMA T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SMD T 0 \<and> nextHTDDataPending T 0) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i367: "((CSTATE SMA T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SMD T 1 \<and> nextHTDDataPending T 1) \<longrightarrow>  HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE SAD T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i368: "(CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE ISA T 0 \<or> CSTATE ISDI T 0 \<longrightarrow> nextLoad T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i369: "(CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE ISA T 1 \<or> CSTATE ISDI T 1 \<longrightarrow> nextLoad T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i370: "(CSTATE IMD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMD T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0  \<longrightarrow> nextStore T 0) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i371: "(CSTATE IMD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMD T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1  \<longrightarrow> nextStore T 1) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i374: "(CSTATE ISA T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i375: "(CSTATE ISA T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SharedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i376: "(CSTATE ISDI T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i377: "(CSTATE ISDI T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i378: "(CSTATE ISDI T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps2 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i379: "(CSTATE ISDI T 0 \<longrightarrow> \<not>nextReqIs RdOwn T 1 \<or> \<not>HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i380: "(CSTATE ISDI T 1 \<longrightarrow> \<not>nextReqIs RdOwn T 0 \<or> \<not>HSTATE ModifiedM T) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i381: "(CSTATE Invalid T 0 \<longrightarrow> reqresps1 T = []) "   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
 have i382: "(CSTATE Invalid T 1 \<longrightarrow> reqresps2 T = [])"   by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i383: "(CSTATE ISDI T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> HSTATE ModifiedM T \<or> HSTATE MAD T  \<or> HSTATE MA T \<or> HSTATE MD T\<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i384: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i385: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i388: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i389: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i390: "(CSTATE SMAD T 0 \<and> reqresps1 T = [] \<and> htddatas1 T = [] \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i391: "(CSTATE SMAD T 1 \<and> reqresps2 T = [] \<and> htddatas2 T = [] \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i392: "(nextReqIs RdOwn T 0 \<longrightarrow> CSTATE SMAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i393: "(nextReqIs RdOwn T 1 \<longrightarrow> CSTATE SMAD T 1 \<or> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i396: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i397: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i400: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i401: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i406: "(CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0)  \<longrightarrow> dthdatas1 T = [] \<and> (dthdatas2 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i407: "(CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1)  \<longrightarrow> dthdatas2 T = [] \<and> (dthdatas1 T = [] \<or> HSTATE MB T \<or> HSTATE ModifiedM T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i408: "(HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)


have i415: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i416: "(HSTATE ModifiedM T  \<and> nextReqIs RdOwn T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i417: "((CSTATE Invalid T 0 \<or> CSTATE ISDI T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i418: "((CSTATE Invalid T 1 \<or> CSTATE ISDI T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i419: "(CSTATE IIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i420: "(CSTATE IIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i421: "(HSTATE MD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i422: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1 \<and> nextGOPending T 1 \<or> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i423: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0 \<and> nextGOPending T 0 \<or> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i424: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i425: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i426: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i427: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i430: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i431: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Modified T 1 \<and> reqs1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i432: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i433: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i435: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i436: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i437: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i438: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i441: "(nextSnpRespIs RspSFwdM T 0 \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i442: "(nextSnpRespIs RspSFwdM T 1 \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i443: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i444: "((HSTATE SAD T \<or> HSTATE MAD T \<or> HSTATE SA T \<or> HSTATE MA T) \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i445: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspSFwdM T 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i446: "(HSTATE SAD T \<and> (nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspSFwdM T 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i449: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> dthdatas1 T \<noteq> [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i450: "(HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> dthdatas2 T \<noteq> [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i451: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i452: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i453: "(nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE MIA T 0 \<or>  CSTATE SIA T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i454: "(nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE MIA T 1 \<or>  CSTATE SIA T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i455: "(HSTATE MA T \<longrightarrow> dthdatas2 T = [] \<and> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i456: "((nextSnpRespIs RspIFwdM T 0 \<or> nextSnpRespIs RspIHitSE T 0) \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISDI T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i457: "((nextSnpRespIs RspIFwdM T 1 \<or> nextSnpRespIs RspIHitSE T 1) \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISDI T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i460: "((CSTATE Invalid T 0  \<or> CSTATE ISDI T 0 \<or> nextReqIs RdOwn T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i461: "((CSTATE Invalid T 1  \<or> CSTATE ISDI T 1 \<or> nextReqIs RdOwn T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i462: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> (dthdatas1 T = [] \<or> nextSnpRespIs RspSFwdM T 0 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i463: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> (dthdatas2 T = [] \<or> nextSnpRespIs RspSFwdM T 1 \<or> HSTATE SD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i465: "(CSTATE IMD T 0 \<or> CSTATE SMD T 0 \<or> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<longrightarrow> ((\<not> CSTATE ISD T 1) \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1 \<and> \<not>( (CSTATE ISAD T 1 \<or> CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<and> \<not>CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> (  nextHTDDataPending T 1) \<and>  \<not> CSTATE Shared T 1 \<and> \<not> CSTATE Modified T 1) \<or> nextSnoopIs SnpInv T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i466: "(CSTATE IMD T 1 \<or> CSTATE SMD T 1 \<or> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextGOPending T 1) \<longrightarrow> ((\<not> CSTATE ISD T 0) \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and> \<not>( (CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextGOPending T 0) \<and> \<not>CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> (  nextHTDDataPending T 0) \<and>  \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Modified T 0) \<or> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i467: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i468: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i469: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i470: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i471: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i472: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i473: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 0 \<and> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i474: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow>  \<not> nextReqIs CleanEvict T 1 \<and> \<not> nextReqIs CleanEvictNoData T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i475: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i476: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i477: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i478: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i479: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i480: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i481: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i482: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i483: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i484: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i485: "(CSTATE Modified T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i486: "(CSTATE Modified T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0 ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i487: "(CSTATE Modified T 0 \<longrightarrow> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i488: "(CSTATE Modified T 1 \<longrightarrow> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i489: "(CSTATE Modified T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i490: "(CSTATE Modified T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i491: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i492: "(HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> dthdatas1 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i493: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i494: "(nextReqIs RdOwn T 0 \<longrightarrow> \<not> CSTATE ISAD T 0 \<and> \<not> CSTATE Invalid T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i495: "(nextReqIs RdOwn T 1 \<longrightarrow> \<not> CSTATE ISAD T 1 \<and> \<not> CSTATE Invalid T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i496: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i497: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i498: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i499: "(HSTATE InvalidM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i500: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i501: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i502: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i503: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i504: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<and> CXL_SPG_used T 0 \<longrightarrow> (nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i505: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<and> CXL_SPG_used T 1 \<longrightarrow> (nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 )) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i506: "(CSTATE SIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i507: "(CSTATE SIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i508: "(CSTATE SMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i509: "(CSTATE SMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i510: "(HSTATE ID T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i511: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i512: "(HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> (\<not> CSTATE Modified T 0 \<or> \<not> CSTATE Modified T 1) \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i513: "(HSTATE ID T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i514: "(HSTATE ID T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i515: "(CSTATE SMAD T 0 \<and> nextGOPending T 0\<longrightarrow> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i516: "(CSTATE SMAD T 1 \<and> nextGOPending T 1\<longrightarrow> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i517: "(C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i518: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i519: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i522: "(nextGOPendingIs GO_WritePull T 0 \<and> HSTATE InvalidM T \<longrightarrow> reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i523: "(nextGOPendingIs GO_WritePull T 1 \<and> HSTATE InvalidM T \<longrightarrow> reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i524: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i525: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i526: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i527: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> nextEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i528: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i529: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i530: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i531: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i532: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i533: "(HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i534: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 0 \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i535: "(HSTATE SharedM T \<and> nextReqIs CleanEvict T 1 \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i536: "(CSTATE Shared T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i537: "(CSTATE Shared T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i538: "(nextReqIs DirtyEvict T 0 \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i539: "(nextReqIs DirtyEvict T 1 \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i540: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i541: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i542: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i543: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i544: "(nextReqIs DirtyEvict T 0 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps2 T = [] \<or> nextReqRespStateIs Invalid (reqresps2 T))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i545: "(nextReqIs DirtyEvict T 1 \<and> HSTATE InvalidM T \<longrightarrow> (reqresps1 T = [] \<or> nextReqRespStateIs Invalid (reqresps1 T)))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i546: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not>(CSTATE ISA T 1 \<or> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i547: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not>(CSTATE ISA T 0 \<or> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i548: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i549: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T \<and> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i550: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i551: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i552: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i553: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i554: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i555: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i556: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> (CSTATE SIA T 0 \<or> CSTATE IIA T 0 \<or> CSTATE SIAC T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i557: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> (CSTATE SIA T 1 \<or> CSTATE IIA T 1 \<or> CSTATE SIAC T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i558: "((CSTATE Shared T 0 \<or> CSTATE Shared T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i559: "(CSTATE Shared T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i560: "(CSTATE Shared T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i561: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> nextEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i562: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> nextEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i563: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i564: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i565: "((nextReqIs CleanEvictNoData T 0 \<or> nextReqIs CleanEvict T 0) \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i566: "((nextReqIs CleanEvictNoData T 1 \<or> nextReqIs CleanEvict T 1) \<longrightarrow> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i567: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> reqs2 T = [] \<or> nextReqIs CleanEvict T 1 \<or> nextReqIs CleanEvictNoData T 1 \<or> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i568: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> reqs1 T = [] \<or> nextReqIs CleanEvict T 0 \<or> nextReqIs CleanEvictNoData T 0 \<or> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i569: "(CSTATE IIA T 0 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 1 \<or> CSTATE SIA T 1 \<or> CSTATE SMAD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1 \<and> nextGOPending T 1 \<or> CSTATE ISD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i570: "(CSTATE IIA T 1 \<and> HSTATE SharedM T \<longrightarrow> CSTATE Shared T 0 \<or> CSTATE SIA T 0 \<or> CSTATE SMAD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0 \<and> nextGOPending T 0 \<or> CSTATE ISD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i571: "(CSTATE IIA T 1 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 0 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i572: "(CSTATE IIA T 0 \<and> HSTATE InvalidM T \<and> nextReqIs RdShared T 1 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i573: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0 \<and>  \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i574: "(HSTATE InvalidM T \<longrightarrow> \<not> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0)) \<and> \<not> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i575: "(nextGOPendingIs GO_WritePull T 0 \<or> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> HSTATE InvalidM T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i576: "(CSTATE MIA T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i577: "(CSTATE MIA T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> \<not> nextHTDDataPending T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i578: "(nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i579: "(nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i580: "((CSTATE IMA T 0 \<or> CSTATE SMA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i581: "((CSTATE IMA T 1 \<or> CSTATE SMA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1) \<longrightarrow> (HSTATE MA T \<or> HSTATE ModifiedM T \<or> HSTATE MB T \<or> HSTATE MAD T \<or> HSTATE SAD T))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i582: "(CSTATE MIA T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i583: "(CSTATE MIA T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = [])" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i584: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i585: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i586: "(CSTATE MIA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i587: "(CSTATE MIA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i588: "((HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE ModifiedM T) \<longrightarrow> (\<not> nextGOPendingIs GO_WritePull T 0) \<and> (\<not> nextGOPendingIs GO_WritePull T 1))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i589: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0 \<and> CSTATE IIA T 1 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i590: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1 \<and> CSTATE IIA T 0 \<longrightarrow> HSTATE InvalidM T \<or> HSTATE IB T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i591: "(HSTATE InvalidM T \<longrightarrow> dthdatas1 T = [] \<and> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i592: "(CSTATE Invalid T 0 \<longrightarrow> \<not> nextSnoopIs SnpInv T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i593: "(CSTATE Invalid T 1 \<longrightarrow> \<not> nextSnoopIs SnpInv T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i594: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i595: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i596: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> [] \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i597: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> [] \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i598: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i599: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i600: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i601: "(HSTATE MA T \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i602: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i603: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i604: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i605: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE SMD T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i606: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE IMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i607: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i608: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i609: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i610: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i611: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i612: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i613: "(HSTATE InvalidM T \<or> HSTATE ID T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i614: "(CSTATE ISD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i615: "(CSTATE ISD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i616: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i617: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i618: "(CSTATE ISAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> htddatas2 T \<noteq> []) \<or> ((CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> htddatas2 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i619: "(CSTATE ISAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> htddatas1 T \<noteq> []) \<or> ((CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> htddatas1 T = [])) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i620: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i621: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i622: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i623: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i624: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i625: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i626: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i627: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i628: "(CSTATE SMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i629: "(CSTATE SMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i630: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i631: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i632: "(CSTATE ISD T 0 \<or> CSTATE ISA T 0 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i633: "(CSTATE ISD T 1 \<or> CSTATE ISA T 1 \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i634: "(CSTATE ISAD T 0 \<and> (nextHTDDataPending T 0 \<or> nextGOPending T 0) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i635: "(CSTATE ISAD T 1 \<and> (nextHTDDataPending T 1 \<or> nextGOPending T 1) \<longrightarrow> \<not> HSTATE MD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i636: "(CSTATE ISD T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i637: "(CSTATE ISD T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i638: "(CSTATE ISA T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i639: "(CSTATE ISA T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i640: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i641: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i642: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i643: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i644: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i645: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i646: "(CSTATE ISA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i647: "(CSTATE ISA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i648: "(CSTATE ISAD T 0 \<and> nextGOPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i649: "(CSTATE ISAD T 1 \<and> nextGOPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i650: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MA T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i651: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MA T)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i652: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i653: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i654: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i655: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i656: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i657: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i658: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i659: "(HSTATE SharedM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i660: "(HSTATE SharedM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i661: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i662: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i663: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISD T 1 \<and> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i664: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i665: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i666: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i667: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i668: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i669: "(HSTATE InvalidM T \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i670: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i671: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i672: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i673: "(HSTATE InvalidM T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i674: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i675: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i676: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i677: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps2 T = [] \<and> reqresps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i678: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps1 T = [] \<and> reqresps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i679: "(CSTATE IMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<longrightarrow> snpresps2 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i680: "(CSTATE IMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<longrightarrow> snpresps1 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i681: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i682: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i683: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i684: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i685: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i686: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i687: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i688: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i689: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i690: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i691: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i692: "(CSTATE IMD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i693: "(CSTATE IMD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i694: "(CSTATE IMAD T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i695: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i696: "(CSTATE IMA T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i697: "(CSTATE IMA T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> HSTATE MAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i698: "(CSTATE IMAD T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i699: "(HSTATE IB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i700: "(HSTATE IB T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i701: "(HSTATE IB T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i702: "(HSTATE SB T \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i703: "(HSTATE SB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i704: "(HSTATE IB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i705: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i706: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i707: "(HSTATE MB T \<longrightarrow> length (dthdatas1 T) \<le> 1 \<and> length (dthdatas2 T) \<le> 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i708: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i709: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i710: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i711: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i712: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i713: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i714: "(HSTATE SB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i715: "(HSTATE IB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i716: "(HSTATE MB T \<longrightarrow> snps2 T = [] \<and> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i717: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i718: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i719: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i720: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i721: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i722: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i723: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i724: "(HSTATE SB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i725: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i726: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMD T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i727: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i728: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i729: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i730: "(HSTATE SharedM T \<and> lastSharer T \<and> nextReqIs CleanEvictNoData T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0))" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i731: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i732: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i733: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i734: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i735: "(CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i736: "(CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<and> HSTATE MA T \<longrightarrow> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i737: "(HSTATE ModifiedM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i738: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i739: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i740: "(HSTATE MD T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i741: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i742: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i743: "(CSTATE MIA T 0 \<longrightarrow> \<not> (CSTATE SMAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i744: "(CSTATE MIA T 1 \<longrightarrow> \<not> (CSTATE SMAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i745: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i746: "(HSTATE ModifiedM T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i747: "(HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i748: "(HSTATE MD T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i749: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i750: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i751: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i752: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i753: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i754: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i755: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 1 \<and> (nextGOPending T 1 \<or> nextHTDDataPending T 1))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i756: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> (CSTATE IMAD T 0 \<and> (nextGOPending T 0 \<or> nextHTDDataPending T 0))) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i757: "(CSTATE MIA T 0 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i758: "(CSTATE MIA T 1 \<and> HSTATE ModifiedM T \<longrightarrow> \<not> CSTATE SMAD T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i759: "(CSTATE IMD T 1 \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i760: "(CSTATE IMD T 0 \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i761: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i762: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i763: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i764: "(HSTATE IB T \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i765: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 0 \<and> \<not> CSTATE SMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i766: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMA T 1 \<and> \<not> CSTATE SMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i767: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE IMD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i768: "(HSTATE IB T \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE IMD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i769: "(HSTATE IB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i770: "(HSTATE IB T \<longrightarrow> \<not> nextHTDDataPending T 0 \<and> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i771: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i772: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i773: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i774: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i775: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i776: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i777: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 0 \<longrightarrow> \<not> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i778: "(HSTATE ModifiedM T \<and> nextReqIs RdShared T 1 \<longrightarrow> \<not> CSTATE ISDI T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i779: "(HSTATE SD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i780: "(HSTATE SAD T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i781: "(HSTATE SAD T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i782: "(HSTATE MD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i783: "(snpresps1 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i784: "(snpresps2 T \<noteq> [] \<and> HSTATE MAD T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i785: "(CSTATE IMD T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i786: "(CSTATE IMD T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i787: "(nextDTHDataFrom 0 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 0 \<longrightarrow> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i788: "(nextDTHDataFrom 1 T \<and> HSTATE MD T \<and> nextReqIs RdOwn T 1 \<longrightarrow> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i789: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 0 \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i790: "(HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T 1 \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i791: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE Modified T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i792: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE Modified T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i793: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i794: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i795: "(HSTATE SA T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i796: "(HSTATE SharedM T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i797: "(CSTATE IIA T 0 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 1 \<and> nextHTDDataPending T 1 \<or> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i798: "(CSTATE IIA T 1 \<and> HSTATE SA T \<longrightarrow> CSTATE ISAD T 0 \<and> nextHTDDataPending T 0 \<or> CSTATE ISA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i799: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> htddatas1 T = [] \<or> CSTATE ISDI T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i800: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> htddatas2 T = [] \<or> CSTATE ISDI T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i801: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i802: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISD T 0 \<and> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i803: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i804: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE Invalid T 1 \<or> CSTATE ISAD T 1 \<or> CSTATE IMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i805: "(HSTATE MB T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i806: "(HSTATE MB T \<longrightarrow> snpresps1 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i807: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i808: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i809: "(HSTATE MB T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i810: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i811: "(HSTATE MB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i812: "(HSTATE MB T \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE ISA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i813: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i814: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i815: "(HSTATE IB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i816: "(HSTATE IB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i817: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i818: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i819: "(HSTATE SB T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i820: "(HSTATE SB T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i821: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i822: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i823: "(CSTATE Modified T 0 \<longrightarrow> \<not> nextReqIs RdOwn T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i824: "(CSTATE Modified T 1 \<longrightarrow> \<not> nextReqIs RdOwn T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i825: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i826: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i827: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i828: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i829: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i830: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i831: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i832: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i833: "((CSTATE ISAD T 0 \<and> nextGOPending T 0) \<or> CSTATE ISA T 0 \<or> ( nextHTDDataPending T 0) \<or> CSTATE Shared T 0 \<longrightarrow> \<not> (CSTATE IMA T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i834: "((CSTATE ISAD T 1 \<and> nextGOPending T 1) \<or> CSTATE ISA T 1 \<or> ( nextHTDDataPending T 1) \<or> CSTATE Shared T 1 \<longrightarrow> \<not> (CSTATE IMA T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i835: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i836: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i837: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i838: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i839: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SIA T 0 \<and> \<not> CSTATE SIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i840: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SIA T 1 \<and> \<not> CSTATE SIA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i841: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i842: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i843: "(CSTATE Modified T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i844: "(CSTATE Modified T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i845: "(CSTATE Modified T 0 \<longrightarrow> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i846: "(CSTATE Modified T 1 \<longrightarrow> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i847: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> (CSTATE ISAD T 1 \<and> nextGOPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i848: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> (CSTATE ISAD T 0 \<and> nextGOPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i849: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE ISA T 1 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i850: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE ISA T 0 \<and> \<not> CSTATE Shared T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i851: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i852: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i853: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i854: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i855: "(CSTATE Invalid T 0 \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i856: "(CSTATE Invalid T 1 \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i857: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> CSTATE ISD T 1 \<or> CSTATE ISAD T 1 \<and> nextGOPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i858: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> CSTATE ISD T 0 \<or> CSTATE ISAD T 0 \<and> nextGOPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i859: "(HSTATE SAD T \<longrightarrow> \<not> nextGOPendingIs GO_WritePull T 0 \<and> \<not> nextGOPendingIs GO_WritePull T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i860: "(HSTATE SAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i861: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpData T 0 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i862: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpData T 1 \<longrightarrow> HSTATE SAD T \<and> CSTATE ISAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i863: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i864: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i865: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> snps2 T = [] \<and> snpresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i866: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> snps1 T = [] \<and> snpresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i867: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i868: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE IB T \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i869: "(CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i870: "(CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i871: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 0 \<longrightarrow> CSTATE IIA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i872: "(HSTATE InvalidM T \<and> nextReqIs DirtyEvict T 1 \<longrightarrow> CSTATE IIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i873: "(HSTATE InvalidM T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) \<and> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i874: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i875: "(HSTATE MA T  \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i876: "(HSTATE MB T \<and> nextDTHDataFrom 0 T \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i877: "(HSTATE MB T \<and> CSTATE IIA T 0 \<longrightarrow> (CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i878: "(HSTATE MB T \<and> CSTATE IIA T 1 \<longrightarrow> (CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i883: "length (dthdatas1 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i884: "length (dthdatas2 T) \<le> 1" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i885: "(HSTATE IB T \<and> CSTATE IIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i886: "(HSTATE IB T \<and> CSTATE IIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i887: "(HSTATE MAD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i888: "(HSTATE MAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i889: "(HSTATE MA T \<and> snpresps1 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i890: "(HSTATE MA T \<and> snpresps2 T \<noteq> [] \<longrightarrow> \<not> CSTATE Shared T 0 \<and> \<not> CSTATE Shared T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i891: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<and> HSTATE MD T \<longrightarrow> snpresps1 T = [] \<and> snps1 T = [] \<and> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i892: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<and> HSTATE MD T \<longrightarrow> snpresps2 T = [] \<and> snps2 T = [] \<and> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i893: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i894: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i895: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1 \<and> (htddatas2 T = [] \<or> CSTATE ISDI T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i896: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0 \<and> (htddatas1 T = [] \<or> CSTATE ISDI T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i897: "(CSTATE Modified T 0 \<longrightarrow> dthdatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i898: "(CSTATE Modified T 1 \<longrightarrow> dthdatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i899: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> CSTATE IMA T 0 \<and> \<not> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i900: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> CSTATE IMA T 1 \<and> \<not> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i901: "(CSTATE IMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i902: "(CSTATE IMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i903: "(CSTATE SMD T 0 \<and> nextHTDDataPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i904: "(CSTATE SMD T 1 \<and> nextHTDDataPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i905: "(CSTATE IMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i906: "(CSTATE IMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i907: "(CSTATE SMA T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i908: "(CSTATE SMA T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i909: "(CSTATE IMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i910: "(CSTATE IMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i911: "(HSTATE MD T \<and> nextDTHDataFrom 0 T \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i912: "(HSTATE MD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i913: "(CSTATE SMAD T 0 \<and> nextGOPending T 0 \<longrightarrow> \<not> CSTATE SMAD T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i914: "(CSTATE SMAD T 1 \<and> nextGOPending T 1 \<longrightarrow> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i915: "(HSTATE InvalidM T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i916: "(HSTATE IB T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i917: "(HSTATE ID T \<longrightarrow> \<not> CSTATE SMAD T 1 \<and> \<not> CSTATE SMAD T 0)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i918: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i919: "(HSTATE MA T \<and> nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i920: "(CSTATE Modified T 0 \<longrightarrow> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i921: "(CSTATE Modified T 1 \<longrightarrow> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i922: "(HSTATE ModifiedM T \<longrightarrow> snps1 T = [] \<and> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i923: "(CSTATE SMAD T 0 \<and> nextHTDDataPending T 0 \<and> nextSnoopIs SnpInv T 0 \<longrightarrow> CSTATE IMAD T 1 \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i924: "(CSTATE SMAD T 1 \<and> nextHTDDataPending T 1 \<and> nextSnoopIs SnpInv T 1 \<longrightarrow> CSTATE IMAD T 0 \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i925: "(CSTATE SMAD T 1 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs DirtyEvict T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i926: "(CSTATE SMAD T 0 \<and> HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs DirtyEvict T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i927: "(CSTATE SIAC T 0 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i928: "(CSTATE SIAC T 1 \<and> HSTATE SA T \<longrightarrow> \<not> CSTATE Modified T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i929: "(CSTATE SIAC T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i930: "(CSTATE SIAC T 1 \<longrightarrow> \<not> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i931: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps2 T = [] \<and> snpresps2 T = [] \<and> htddatas1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i932: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps1 T = [] \<and> snpresps1 T = [] \<and> htddatas2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i933: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or> (CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i934: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or> (CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i935: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i936: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i937: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i938: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) \<and> HSTATE MA T \<longrightarrow>(CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i939: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i940: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i941: "((CSTATE SIAC T 0 \<and> nextGOPending T 0 \<and> nextGOPendingState Invalid T 0) --> reqs1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i942: "((CSTATE SIAC T 1 \<and> nextGOPending T 1 \<and> nextGOPendingState Invalid T 1) --> reqs2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i943: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextHTDDataPending T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i944: "(HSTATE MA T \<and> nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextHTDDataPending T 1)" by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i945: "(HSTATE SB T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i946: "(nextReqIs CleanEvictNoData T 0 \<longrightarrow> CSTATE SIAC T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i947: "(nextReqIs CleanEvictNoData T 1 \<longrightarrow> CSTATE SIAC T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i948: "(nextSnpRespIs RspIHitSE T 0 \<longrightarrow> \<not> nextDTHDataFrom 0 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i949: "(nextSnpRespIs RspIHitSE T 1 \<longrightarrow> \<not> nextDTHDataFrom 1 T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i950: "(nextSnpRespIs RspIFwdM T 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 0) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i951: "(nextSnpRespIs RspIFwdM T 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData T 1)  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i952: "(CSTATE SMA T 0 \<and> nextSnoopIs SnpData T 0 \<and> nextGOPending T 0 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i953: "(CSTATE SMA T 1 \<and> nextSnoopIs SnpData T 1 \<and> nextGOPending T 1 \<longrightarrow> HSTATE SAD T) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i954: "((CSTATE SIA T 0 \<and> nextGOPendingIs GO_WritePullDrop T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i955: "((CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i956: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 1 \<or> CSTATE MIA T 1 \<or> (CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<and> nextGOPending T 1 \<or>(CSTATE IMA T 1 \<or> CSTATE SMA T 1) \<and> nextGOPending T 1 \<or> (CSTATE IMD T 1 \<or> CSTATE SMD T 1) \<and> nextHTDDataPending T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i957: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE ModifiedM T \<longrightarrow> CSTATE Modified T 0 \<or> CSTATE MIA T 0 \<or> (CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<and> nextGOPending T 0 \<or>(CSTATE IMA T 0 \<or> CSTATE SMA T 0) \<and> nextGOPending T 0 \<or> (CSTATE IMD T 0 \<or> CSTATE SMD T 0) \<and> nextHTDDataPending T 0)   " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i958: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MD T \<longrightarrow> dthdatas1 T \<noteq> []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i959: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MD T \<longrightarrow> dthdatas2 T \<noteq> [])  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i960: "((CSTATE SIAC T 0 \<and> nextGOPendingIs GO T 0 \<and> nextGOPendingState Invalid T 0 \<and> \<not> CSTATE IIA T 1 \<and> GTS T 1) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 1 \<or> CSTATE SMAD T 1) \<and> nextHTDDataPending T 1 \<or> CSTATE IMA T 1 \<or> CSTATE SMA T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i961: "((CSTATE SIAC T 1 \<and> nextGOPendingIs GO T 1 \<and> nextGOPendingState Invalid T 1 \<and> \<not> CSTATE IIA T 0 \<and> GTS T 0) \<and> HSTATE MA T \<longrightarrow> ((CSTATE IMAD T 0 \<or> CSTATE SMAD T 0) \<and> nextHTDDataPending T 0 \<or> CSTATE IMA T 0 \<or> CSTATE SMA T 0)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i962: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> snps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i963: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> snps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i964: "(HSTATE SD T \<and> nextDTHDataFrom 0 T \<longrightarrow> reqresps1 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i965: "(HSTATE SD T \<and> nextDTHDataFrom 1 T \<longrightarrow> reqresps2 T = []) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i966: "(HSTATE ID T \<and> nextDTHDataFrom 0 T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i967: "(HSTATE ID T \<and> nextDTHDataFrom 1 T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0) ) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i968: "(CSTATE MIA T 0 \<and> nextGOPendingIs GO_WritePull T 0 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 1 \<or> nextGOPendingIs GO_WritePullDrop T 1)) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i969: "(CSTATE MIA T 1 \<and> nextGOPendingIs GO_WritePull T 1 \<and> HSTATE ID T \<longrightarrow> (\<not> CSTATE SIA T 0 \<or> nextGOPendingIs GO_WritePullDrop T 0))  " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)
have i970: "(HSTATE SAD T \<and> nextDTHDataFrom 1 T \<longrightarrow> \<not> CSTATE MIA T 0 \<and> \<not> CSTATE MIA T 1) " by (insert assms, unfold SWMR_state_machine_def, elim conjE, assumption)






(*BigHeaderEnd*)







  have i220: "HSTATE ModifiedM T \<or> HSTATE MAD T \<or> HSTATE MA T \<or> HSTATE MD T \<or> HSTATE ID T \<or> HSTATE InvalidM T \<or> HSTATE SharedM T \<or> HSTATE SB T"
 
 by (metis assms i1x i376)
 have i221: " CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"  
   

   using ISDIData_Shared by blast
 have i222: "nextLoad T 0" 
 
   using i1x i368 by blast
   have aux_r39:  "(CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and>
  nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow>
  nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) "
  

  using CSTATE_inequality_invariant i221 by blast
   have aux_r42: "(CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and>
  nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow>
  \<not> nextDTHDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
  

  using CSTATE_inequality_invariant i221 by blast
   have aux3_r42: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1  = CSTATE IIA T 1"
  
  using CSTATE_ISDIData_otherside by blast
   have aux4_r42: "
  nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 =
  nextGOPendingIs GO_WritePull T 1"
  
  using ISDIData_nextGOPendingIs by blast
   have aux5_r42: "
   nextDTHDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 = 
  nextDTHDataPending T 1"
  

  using device_perform_op_dthdatas2 nextDTHDataPending_def by presburger
   have aux2_r42: "(CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and>
  nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow>
  \<not> nextDTHDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
  
  using C_msg_P_same_def aux3_r42 aux4_r42 aux5_r42 i40 by presburger
  have aux_r93: "(CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and>
  nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow>
  nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 using CSTATE_inequality_invariant i221 by blast
  have g39aux: "htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply(insert i77)

 by (metis htddatas1_empty_if_minus_rule_2_0 i77)
  have g39aux1: "\<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 by (metis g39aux nextHTDDataPending_various_forms1)
  have aux429: "snps1 T = []"
 
 by (metis i1x i377)
  (*ReplaceFrom*)

  show ?thesis
unfolding SWMR_state_machine_def

(*BigLemmaEnd*)

proof (intro conjI)
  show goal1: "SWMR ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_various_forms1 MESI_State.distinct(5) MESI_State.distinct(95) i221) done
  show goal2: "C_msg_P_oppo ISD nextHTDDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) g39aux1 i221) done
  show goal3: "H_msg_P_same SD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i23) done
  show goal4: "H_msg_P_same SAD nextDTHDataPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_otherside_rule_5_0 MESI_State.distinct(5) i221 i2x i921 nextHTDDataPending_def) done
  show goal5: "C_msg_P_oppo ISAD nextGOPending (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) MESI_State.distinct(5) i221) done
  show goal6: "H_msg_P_same SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i22 i221) done
  show goal7: "H_msg_P_oppo SharedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i22 i221) done
  show goal8: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> CSTATE Modified T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) assms i221 i778 nextReqIs_ISDIData) done
  show goal9: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HSTATE_rule_6 i100 i1x i2x i778 nextHTDDataPending_def nextReqIs_general_rule_7_0 nextReqIs_not_various_forms1) done
  show goal10: "H_msg_P_oppo ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HSTATE_rule_6 HTDDataPending_htddatas_invariant1 i100 i1x i2x i778 nextReqIs_general_rule_7_0 nextReqIs_not_various_forms1) done
  show goal11: "H_msg_P_same ModifiedM (nextReqIs RdShared) (\<lambda>T i. \<not> nextSnpRespIs RspIFwdM T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) HSTATE_rule_6 HTDDataPending_htddatas_invariant1 i100 i1x i2x i778 nextReqIs_general_rule_7_0 nextReqIs_not_various_forms1) done
  show goal12: "C_H_state IMAD (nextReqIs RdOwn) Modified SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i23) done
  show goal13: "C_H_state IMAD (nextReqIs RdOwn) Modified SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(5) i221) done
  show goal14: "C_H_state IMAD (nextReqIs RdOwn) Modified SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(5) i221) done
  show goal15: "C_H_state Invalid nextStore Modified SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_otherside_rule_5_0 MESI_State.distinct(5) i221 i2x i921 nextHTDDataPending_def) done
  show goal16: "C_H_state Invalid nextStore Modified SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_otherside_rule_5_0 HTDDataPending_htddatas_invariant1 MESI_State.distinct(5) i221 i2x i921) done
  show goal17: "C_H_state Invalid nextStore Modified SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i23) done
  show goal18: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i22 i221) done
  show goal19: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i23) done
  show goal20: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i24) done
  show goal21: "C_msg_not RdShared IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_not_def MESI_State.distinct(147) i221 i25 nextReqIs_ISDIData) done
  show goal22: "C_msg_not RdShared Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(143) MESI_State.distinct(259) assms i47 nextReqIs_ISDIData) done
  show goal23: "H_msg_P_same ModifiedM (nextReqIs DirtyEvict) (\<lambda>T i. CSTATE MIA T i \<or> CSTATE IIA T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis HSTATE_rule_6 HTDDataPending_htddatas_invariant1 empty_no_snoop i100 i1x i2x i417 i466 i577 i833 i852 i921 i922 nextReqIs_general_rule_7_0 nextReqIs_not_various_forms1) done
  show goal24: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (\<lambda>T. \<not> HSTATE ModifiedM T) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i313 i578) done
  show goal25: "C_msg_P_same MIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal26: "C_msg_P_host MIA (nextGOPendingIs GO_WritePull) (HSTATE ID) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal27: "C_state_not MIA RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal28: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant C_msg_P_same_def ISDIData_nextEvict ISDIData_nextGOPendingIs MESI_State.distinct(163) aux3_r42 i221 i32) done
  show goal29: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(163) MESI_State.distinct(277) aux3_r42 i221 i47 nextReqIs_ISDIData) done
  show goal30: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (smt (verit) CSTATE_disj1 C_msg_P_same_def ISDIData_nextGOPendingIs MESI_State.distinct(163) aux3_r42 aux5_r42 i221 i35)

  show goal31: "H_C_state_msg_same ModifiedM Modified (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) assms i221 i778 nextReqIs_ISDIData) done
  show goal32: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant C_msg_P_same_def ISDIData_nextEvict MESI_State.distinct(163) aux3_r42 aux4_r42 i221 i37) done
  show goal33: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(163) MESI_State.distinct(277) aux3_r42 i221 i47 nextReqIs_ISDIData) done
  show goal34: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) aux2_r42 aux_r42) done
  show goal35: "H_C_state_msg_oppo ModifiedM IIA (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(13) MESI_State.distinct(295) MESI_State.distinct(297) MESI_State.distinct(299) MESI_State.distinct(307) MESI_State.distinct(315) MESI_State.distinct(317) MESI_State.distinct(319) assms i1x i420 i778 nextReqIs_general_rule_7_0) done
  show goal36: "C_msg_P_host Shared (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE ISDIData_nextSnoopIs MESI_State.distinct(95) i221 i385) done
  show goal37: "C_msg_state RdShared ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(259) assms i47 nextReqIs_ISDIData) done
  show goal38: "C_not_C_msg Modified ISAD nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) MESI_State.distinct(5) i221) done
  show goal39: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (metis CSTATE_otherside_rule_8 C_msg_P_same_def g39aux1 i50 nextHTDDataPending_otherside_rule_2_0 nextStore_otherside_rule_3_0) 
 
  show goal40: "C_msg_P_same Invalid nextStore (\<lambda>T i. \<not> nextSnoopIs SnpInv T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 using snps1_general_rule_7_0 
 by (metis CSTATE_otherside_rule_5_0 C_msg_P_same_def aux429 empty_no_snoop2 empty_no_snoop_variant i51 i856 snps2_general_rule_7_0)

  show goal41: "C_msg_P_same ISAD nextGOPending (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (smt (verit) C_msg_P_same_def C_msg_not_def C_msg_state_def goal22 i221 i47 i52 nextGOPending_DeviceISDIData nextReqIs_ISDIData)
  show goal42: "snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal43: "snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms g39aux i377) done
  show goal44: "length (reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 i57) done
  show goal45: "length (reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs2 i58) done
  show goal46: "length (snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms i377 i60) done
  show goal47: "length (snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms i377 i60) done
  show goal48: "C_msg_P_same Shared (nextSnoopIs SnpInv) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms g39aux1 i352 i468) done
  show goal49: "C_msg_P_same IIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (smt (z3) CSTATE_different1 C_msg_P_same_def MESI_State.distinct(163) aux3_r42 aux4_r42 i221 i37 i39 i40 i611old nextSnoopPending_general_rule_7_0)

  show goal50: "C_msg_P_oppo Invalid nextStore (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (metis C_msg_P_oppo_def assms aux429 i377 nextSnoopPending_def nextSnoopPending_empty_not_rule_7_0 snps1_general_rule_7_flipped_1 snps2_general_rule_7_0)


  show goal51: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal52: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i377 i382 i614old) done
  show goal53: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal54: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i377 i614old i616old) done
  show goal55: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal56: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 aux3_r42 i618old) done
  show goal57: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 HTDDataPending_htddatas_invariant1 assms i100) done
  show goal58: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs2 i69) done
  show goal59: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 HTDDataPending_htddatas_invariant1 assms i100) done
  show goal60: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs2 i71) done
  show goal61: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal62: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal63: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i221) done
  show goal64: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i75) done
  show goal65: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i221) done
  show goal66: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i752old nextLoad_DeviceISDIData) done
  show goal67: "C_msg_P_host ISD (nextSnoopIs SnpInv) (HSTATE MA) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (metis CSTATE_assign_rule_6 CSTATE_disj1 CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(139) i401 nextSnoopIs_general_rule_7_0) done
  show goal68: "length (htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) assms g39aux i377 i60) done
  show goal69: "length (htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_htddatas2 i78) done
  show goal70: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal71: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i377 i80) done
  show goal72: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 HTDDataPending_htddatas_invariant1 assms i100) done
  show goal73: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs2 i82) done
  show goal74: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal75: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending FixISDIData.device_perform_op_reqs2 i84) done
  show goal76: "length (reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms i377 i60) done
  show goal77: "length (reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 i86) done
  show goal78: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms g39aux i377) done
  show goal79: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal80: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal81: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal82: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal83: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i92 nextReqIs_ISDIData) done
  show goal84: "C_msg_P_same MIA (nextReqIs DirtyEvict) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) ISDIData_nextEvict aux_r93 i539 nextReqIs_ISDIData) done
  show goal85: "reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal86: "reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_reqs2 g39aux i95) done
  show goal87: "reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal88: "reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs2 FixISDIData.device_perform_op_snpresps1 g39aux i99) done
  show goal89: "reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal90: "reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_reqs2 g39aux i101) done
  show goal91: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_8 HSTATE_general_rule_5_0 assms i2x i380 i415 i547 i577 i643 i745 i833 nextGOPending_General_rule_4_1 nextHTDDataPending_otherside_rule_2_0 nextReqIs_general_rule_7_0) done
  show goal92: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i379 nextReqIs_ISDIData) done
  show goal93: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal94: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis HOST_State.distinct(265) HOST_State.distinct(285) HSTATE_invariant4 HTDDataPending_htddatas_invariant1 ISDIData_HSTATE assms i165 i182 i191 i1x i22 i332 i352 i366 i376 i417 i423 i493 i510 i577 i582 i702 i801 i833 i852 i921 nextDTHDataFrom_general_rule_4_0) done
  show goal95: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal96: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 HOST_State.distinct(243) HOST_State.distinct(265) HOST_State.distinct(285) HOST_State.distinct(303) HOST_State.distinct(375) HSTATE_invariant3 HSTATE_invariant4 HTDDataPending_htddatas_invariant1 ISDIData_HSTATE assms i1x i22 i24 i2x i352 i376 i417 i510 i577 i618old i654 i656 i658 i660 i672 i702 i833 i852 i878 i921 i945 nextHTDDataPending_various_forms2) done
  show goal97: "reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal98: "reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_reqs2 g39aux i95) done
  show goal99: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 CSTATE_otherside_rule_5_0 HSTATE_general_rule_5_0 MESI_State.distinct(259) i106 i1x) done
  show goal100: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(95) i107 i221) done
  show goal101: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_htddatas2 ISDIData_HSTATE g39aux i108) done
  show goal102: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal103: "length (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 i883) done
  show goal104: "length (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas2 i884) done
  show goal105: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal106: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 HSTATE_rule_6 MESI_State.distinct(185) MESI_State.distinct(259) i113 i1x nextDTHDataFrom_general_rule_4_0) done
  show goal107: "HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i114 nextSnpRespIs_general_rule_7_0) done
  show goal108: "HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(259) assms i115 i352 nextSnpRespIs_general_rule_7_0) done
  show goal109: "nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i221) done
  show goal110: "nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside aux3_r42 i457 nextSnpRespIs_general_rule_7_0) done
  show goal111: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(307) MESI_State.distinct(311) MESI_State.distinct(323) assms i453 nextReqIs_ISDIData) done
  show goal112: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms aux3_r42 i454 i577 nextReqIs_ISDIData) done
  show goal113: "snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 g39aux i118) done
  show goal114: "snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal115: "length (snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 i120) done
  show goal116: "length (snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms i377 i60) done
  show goal117: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(259) assms i106) done
  show goal118: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(259) assms i438 nextSnpRespIs_general_rule_7_0) done
  show goal119: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i190 i2x i449 nextDTHDataFrom_def nextSnpRespIs_general_rule_7_0 remove_instr_HSTATE) done
  show goal120: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i450 nextHTDDataPending_various_forms1 nextSnpRespIs_general_rule_7_0 remove_instr_HSTATE) done
  show goal121: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps1 hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i451 remove_instr_HSTATE) done
  show goal122: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps2 MESI_State.distinct(295) MESI_State.distinct(315) assms hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i352 i452 remove_instr_HSTATE) done
  show goal123: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE g39aux i126) done
  show goal124: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal125: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE assms i153) done
  show goal126: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas2 FixISDIData.device_perform_op_reqs2 ISDIData_HSTATE i129) done
  show goal127: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i221) done
  show goal128: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE i131) done
  show goal129: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal130: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal131: "dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_snpresps2 ISDIData_HSTATE g39aux i136) done
  show goal132: "dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas2 FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE g39aux i137) done
  show goal133: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal134: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i752old nextLoad_DeviceISDIData) done
  show goal135: "C_msg_P_same IIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (smt (z3) CSTATE_different1 C_msg_P_same_def ISDIData_nextGOPendingIs MESI_State.distinct(163) aux3_r42 i142 i221 i32 i34 i35 nextSnoopPending_general_rule_7_0)


  show goal136: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal137: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i143 i144 nextGOPending_DeviceISDIData) done
  show goal138: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal139: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i146 nextLoad_DeviceISDIData) done
  show goal140: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal141: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i148) done
  show goal142: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal143: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms i150 i377 nextGOPending_DeviceISDIData) done
  show goal144: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_8 HSTATE_general_rule_5_0 assms i2x i417 i547 i577 i643 i833 nextGOPending_General_rule_4_1 nextHTDDataPending_otherside_rule_2_0) done
  show goal145: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_8 HSTATE_general_rule_5_0 MESI_State.distinct(147) MESI_State.distinct(169) MESI_State.distinct(295) MESI_State.distinct(315) MESI_State.distinct(39) assms i2x i352 i417 i418 i465 i546 i547 i576 i577 i593 i595 i642 i643 i72 i757 i833 i843 i901) done
  show goal146: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE assms i153) done
  show goal147: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE i154) done
  show goal148: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snpresps2 ISDIData_HSTATE g39aux i159) done
  show goal149: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal150: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HSTATE_rule_6 i165 i2x nextDTHDataFrom_general_rule_4_0 nextHTDDataPending_def) done
  show goal151: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal152: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal153: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal154: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 ISDIData_HSTATE i167 nextDTHDataFrom_general_rule_4_0) done
  show goal155: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal156: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 ISDIData_HSTATE i169 nextDTHDataFrom_general_rule_4_0) done
  show goal157: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i392 i656 i658 i756 nextReqIs_ISDIData) done
  show goal158: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE g39aux i186 i591) done
  show goal159: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE g39aux i186 i591) done
  show goal160: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE g39aux i186 i591) done
  show goal161: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant MESI_State.distinct(163)) done
  show goal162: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_8 HSTATE_general_rule_5_0 MESI_State.distinct(31) MESI_State.distinct(343) MESI_State.distinct(531) MESI_State.distinct(533) assms i2x i417 i547 i577 i643 i833) done
  show goal163: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i221) done
  show goal164: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 ISDIData_HSTATE assms aux3_r42 g39aux i392 i563 i568 i656 i658 i756) done
  show goal165: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i221) done
  show goal166: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms aux3_r42 aux4_r42 i178 i179 i770) done
  show goal167: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i221) done
  show goal168: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs assms aux3_r42 i180 i181 i672) done
  show goal169: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal170: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i182 i183) done
  show goal171: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal172: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 HSTATE_rule_6 MESI_State.distinct(103) MESI_State.distinct(185) MESI_State.distinct(259) aux3_r42 i1x i2x i316 i352 i570 i658 i929 nextHTDDataPending_def) done
  show goal173: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE g39aux i186) done
  show goal174: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal175: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal176: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE g39aux i189) done
  show goal177: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE g39aux i455) done
  show goal178: "nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal179: "nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_nextHTDDataPending i191 nextDTHDataFrom_general_rule_4_0) done
  show goal180: "nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal181: "nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal182: "HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE g39aux i194) done
  show goal183: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal184: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> (\<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant CSTATE_otherside_rule_8 HSTATE_rule_6 ISDIData_Shared_aux1 MESI_State.distinct(163) SharedSnpInv'_CSTATE_invariant5 i196 i222 nextLoad_devstate nextSnpRespIs_general_rule_7_0) done
  show goal185: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal186: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal187: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal188: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal189: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal190: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal191: "snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal192: "snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal193: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs i796) done
  show goal194: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE aux4_r42 i796) done
  show goal195: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs i309 nextDTHDataFrom_general_rule_4_0) done
  show goal196: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal197: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE aux4_r42 i859) done
  show goal198: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> (nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs i859) done
  show goal199: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i313) done
  show goal200: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_P_same_def ISDIData_nextEvict MESI_State.distinct(175) aux4_r42 i221 i314) done
  show goal201: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(175) MESI_State.distinct(289) i221 i47 nextReqIs_ISDIData) done
  show goal202: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal203: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i317 i377) done
  show goal204: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 by (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant CSTATE_otherside_rule_8 C_msg_P_same_def ISDIData_nextGOPendingIs MESI_State.distinct(175) i318 i579 nextSnoopPending_general_rule_7_0)  (* proof in multi-steps*)

  show goal205: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i221) done
  show goal206: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms aux4_r42 i319 i320 i770 i809) done
  show goal207: "C_msg_P_same SIA (nextGOPendingIs GO_WritePull) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (smt (verit) CSTATE_disj1 CSTATE_otherside_rule_5_0 C_msg_P_same_def MESI_State.distinct(175) aux4_r42 aux5_r42 i178 i221 i2x i313 i320 i323 i770 i809 i818 i820 nextDTHDataFrom_def nextDTHDataPending_def)


  show goal208: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i221) done
  show goal209: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal210: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_P_same_def ISDIData_nextEvict ISDIData_nextGOPendingIs MESI_State.distinct(175) i221 i324) done
  show goal211: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextReqIs RdShared T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant C_msg_state_def MESI_State.distinct(175) MESI_State.distinct(289) i221 i47 nextReqIs_ISDIData) done
  show goal212: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant CSTATE_otherside_rule_5_0 C_msg_P_same_def ISDIData_nextGOPendingIs MESI_State.distinct(175) i326 nextSnoopPending_general_rule_7_0)  (* proof in multi-steps*)

  show goal213: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i221) done
  show goal214: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextGOPendingIs assms i327 i328 i672 i770) done
  show goal215: "C_msg_P_same SIA (nextGOPendingIs GO_WritePullDrop) (\<lambda>T i. \<not> nextDTHDataPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant CSTATE_otherside_rule_8 C_msg_P_same_def ISDIData_nextGOPendingIs MESI_State.distinct(175) i329 nextDTHDataPending_other_rule_5_0)  (* proof in multi-steps*)

  show goal216: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal217: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal218: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i333 i334) done
  show goal219: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal220: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal221: "C_not_C_msg Modified IMAD nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(5) i221) done
  show goal222: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal223: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal224: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_nextStore_otherside i340) done
  show goal225: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal226: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms i342 i377 nextGOPending_DeviceISDIData) done
  show goal227: "snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal228: "snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal229: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i332 i345) done
  show goal230: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i338 i346 nextGOPending_DeviceISDIData) done
  show goal231: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal232: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i347 i348 i914 nextGOPending_DeviceISDIData) done
  show goal233: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal234: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_nextStore_otherside i350) done
  show goal235: "C_msg_P_same IMA nextGOPending nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextStore_otherside MESI_State.distinct(149) i221 i371) done
  show goal236: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal237: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending i353) done
  show goal238: "C_msg_P_oppo IMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant MESI_State.distinct(149) assms i221 i829 i833 nextGOPending_DeviceISDIData) done
  show goal239: "C_msg_P_oppo SMA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_different1 CSTATE_otherside_rule_5_0 MESI_State.distinct(169) i221 i2x i852 nextGOPending_General_rule_4_1 nextHTDDataPending_def) done
  show goal240: "C_msg_P_oppo ISA nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 
 by (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant C_msg_P_oppo_def MESI_State.distinct(141) aux429 i356 nextSnoopPending_empty_not_rule_14_0 nextSnoopPending_general_rule_14_0 nextSnoopPending_general_rule_7_0)

  show goal241: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal242: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal243: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> ((CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(171)) done
  show goal244: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> ((CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_8 i2x i466 nextGOPending_General_rule_4_1 nextSnoopIs_general_rule_7_0) done
  show goal245: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) g39aux1 i221) done
  show goal246: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_8 FixISDIData.device_perform_op_dthdatas2 HTDDataPending_htddatas_invariant1 dthdatas1_general_rule_4_0 g39aux1 i190 i191 i2x i407 nextDTHDataFrom_def nextHTDDataPending_def nextHTDDataPending_otherside_rule_2_0 nextHTDDataPending_remove_op) done
  show goal247: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant MESI_State.distinct(151) MESI_State.distinct(171) assms i377 nextGOPending_DeviceISDIData reqresps_empty_noGOPending1) done
  show goal248: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_8 FixISDIData.device_perform_op_dthdatas2 i436 nextGOPending_DeviceISDIData) done
  show goal249: "C_msg_P_same SMA nextGOPending nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms , unfold SWMR_def C_msg_P_same_def C_msg_P_oppo_def H_msg_P_same_def C_H_state_def C_msg_not_def H_msg_P_oppo_def C_msg_P_host_def C_state_not_def H_C_state_msg_same_def H_C_state_msg_oppo_def C_msg_state_def C_not_C_msg_def)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextStore_otherside MESI_State.distinct(169) i221 i371) done
  show goal250: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) g39aux1 i221) done
  show goal251: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE assms i353 i366 i367 i547 i643 nextGOPending_DeviceISDIData) done
  show goal252: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) MESI_State.distinct(141) MESI_State.distinct(143) MESI_State.distinct(145) i221) done
  show goal253: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextLoad ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i146 i369 i752old nextLoad_DeviceISDIData) done
  show goal254: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) MESI_State.distinct(149) MESI_State.distinct(151) MESI_State.distinct(167) MESI_State.distinct(169) MESI_State.distinct(171) i221) done
  show goal255: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextStore ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_nextStore_otherside i340 i350 i371) done
  show goal256: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_8 dthdatas1_general_rule_4_0 i190 i2x i462 nextDTHDataFrom_def) done
  show goal257: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant CSTATE_otherside_rule_8 FixISDIData.device_perform_op_dthdatas2 FixISDIData.device_perform_op_htddatas2 HTDDataPending_htddatas_invariant2 MESI_State.distinct(5) SARspSFwdM_invariant2 i109 i2x i463 nextGOPending_DeviceISDIData nextHTDDataPending_various_forms1 nextHTDDataPending_various_forms2 nextSnpRespIs_general_rule_7_0 nextSnpRespIs_invariant2 nextSnpRespIs_invariant_variant1 nextSnpRespIs_remove_op)done
  show goal258: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i221) done
  show goal259: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms i376 i383 i603 i611 i672 i747 i748) done
  show goal260: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal261: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i220 i672) done
  show goal262: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps1 FixISDIData.device_perform_op_snps2 assms i377) done
  show goal263: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 FixISDIData.device_perform_op_snps2 assms g39aux i377 i378) done
  show goal264: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> \<not> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i379 nextReqIs_ISDIData) done
  show goal265: "CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> \<not> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i380 nextReqIs_ISDIData) done
  show goal266: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal267: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqresps2 g39aux i382) done
  show goal268: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i221) done
  show goal269: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i385) done
  show goal270: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i221) done
  show goal271: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms i352 i468 i509) done
  show goal272: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal273: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 ISDIData_nextSnoopIs assms g39aux i377 i389) done
  show goal274: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i377 snps1_empty_not_nextSnoopIs_rule_7_0) done
  show goal275: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_reqresps2 ISDIData_HSTATE ISDIData_nextSnoopIs i391) done
  show goal276: "nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(295) MESI_State.distinct(315) assms i392 nextReqIs_ISDIData) done
  show goal277: "nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i393 nextReqIs_ISDIData) done
  show goal278: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> CXL_SPG_used ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal279: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> CXL_SPG_used ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CXL_SPG_used_general_rule_4_0 ISDIData_nextSnoopIs i397 nextReqIs_ISDIData) done
  show goal280: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i221) done
  show goal281: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i401) done
  show goal282: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i221) done
  show goal283: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms i352 i470 i509) done
  show goal284: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snpresps2 ISDIData_HSTATE g39aux i408) done
  show goal285: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal286: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(295) MESI_State.distinct(299) assms i423 nextDTHDataFrom_general_rule_4_0) done
  show goal287: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal288: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE i472 nextDTHDataFrom_general_rule_4_0 nextReqIs_ISDIData) done
  show goal289: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i421) done
  show goal290: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal291: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(295) assms i425 nextDTHDataFrom_general_rule_4_0) done
  show goal292: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal293: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE i427 nextDTHDataFrom_general_rule_4_0) done
  show goal294: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal295: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE i474 nextDTHDataFrom_general_rule_4_0 nextReqIs_ISDIData) done
  show goal296: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal297: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs1 ISDIData_HSTATE g39aux i431 nextDTHDataFrom_general_rule_4_0) done
  show goal298: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal299: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 ISDIData_HSTATE g39aux i433 nextDTHDataFrom_general_rule_4_0) done
  show goal300: "(HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal301: "(HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal302: "nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(103) MESI_State.distinct(315) MESI_State.distinct(323) assms i441 i929 nextSnpRespIs_general_rule_7_0) done
  show goal303: "nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i442 nextSnpRespIs_general_rule_7_0) done
  show goal304: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 HSTATE_general_rule_5_0 assms i460 nextHTDDataPending_otherside_rule_2_0) done
  show goal305: "(CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_different1 CSTATE_otherside_rule_8 HSTATE_rule_6 MESI_State.distinct(295) MESI_State.distinct(315) i1x i2x i352 i461 nextReqIs_general_rule_7_0) done
  show goal306: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal307: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i476) done
  show goal308: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal309: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i478) done
  show goal310: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal311: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i693) done
  show goal312: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal313: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_otherside_rule_5_0 i2x i623 nextHTDDataPending_various_forms1 nextSnoopIs_general_rule_7_0) done
  show goal314: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal315: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i695) done
  show goal316: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal317: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_otherside_rule_5_0 i2x i621 nextHTDDataPending_various_forms1 nextSnoopIs_general_rule_7_0) done
  show goal318: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal319: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i697) done
  show goal320: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal321: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_otherside_rule_5_0 i2x i625 nextHTDDataPending_various_forms1 nextSnoopIs_general_rule_7_0) done
  show goal322: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal323: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal324: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal325: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal326: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal327: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i484) done
  show goal328: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal329: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(259) assms i486) done
  show goal330: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 HTDDataPending_htddatas_invariant1 assms i100) done
  show goal331: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs2 i488) done
  show goal332: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal333: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_reqresps2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i377 i490 i614old) done
  show goal334: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal335: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal336: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal337: "nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(295) MESI_State.distinct(315) assms i392 nextReqIs_ISDIData) done
  show goal338: "nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i495 nextReqIs_ISDIData) done
  show goal339: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal340: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal341: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal342: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal343: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal344: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i317 i377) done
  show goal345: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i221) done
  show goal346: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i503) done
  show goal347: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> CXL_SPG_used ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i221) done
  show goal348: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> CXL_SPG_used ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CXL_SPG_used_general_rule_4_0 ISDIData_nextSnoopIs i505 nextReqIs_ISDIData) done
  show goal349: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(175) i221) done
  show goal350: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)
    by (metis CSTATE_disj1 CSTATE_otherside_rule_5_0 MESI_State.distinct(565) MESI_State.distinct(575) goal304 goal317 goal321 goal346 i221)
  show goal351: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal352: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms i352 i509) done
  show goal353: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) MESI_State.distinct(95) i221 i510) done
  show goal354: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (\<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) MESI_State.distinct(95) i107 i221) done
  show goal355: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (\<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) MESI_State.distinct(95) i107 i221) done
  show goal356: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i513 i574 i609 i613 nextReqIs_ISDIData) done
  show goal357: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i514 nextReqIs_ISDIData) done
  show goal358: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal359: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending i516 i914 nextGOPending_DeviceISDIData) done
  show goal360: "C_msg_P_oppo SMAD nextGOPending (\<lambda>T i. \<not> nextSnoopPending T i) ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 unfolding C_msg_P_oppo_def
proof (intro conjI)
  show goal1: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextSnoopPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (-)(**)apply (smt (verit) g39aux1 goal358) done
  show goal2: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextSnoopPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
  apply  (cases "program1 T") apply  (auto)
apply (smt (verit) aux429) 
apply (smt (verit) aux429) 
 done

qed
  show goal361: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i929 i946 nextReqIs_ISDIData) done
  show goal362: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i947 nextReqIs_ISDIData) done
  show goal363: "nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal364: "nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal365: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal366: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextEvict i525 nextReqIs_ISDIData) done
  show goal367: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i561 i563 nextReqIs_ISDIData) done
  show goal368: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextEvict i527 nextReqIs_ISDIData) done
  show goal369: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal370: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i529 nextReqIs_ISDIData) done
  show goal371: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i561 i563 nextReqIs_ISDIData) done
  show goal372: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i531 nextReqIs_ISDIData) done
  show goal373: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal374: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal375: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i561 i563 nextReqIs_ISDIData) done
  show goal376: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal377: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i221) done
  show goal378: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms i352 i468 i509) done
  show goal379: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(307) MESI_State.distinct(311) MESI_State.distinct(323) assms i453 nextReqIs_ISDIData) done
  show goal380: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_nextEvict i539 nextReqIs_ISDIData) done
  show goal381: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal382: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal383: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal384: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal385: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqRespStateIs Invalid (reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal386: "nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> nextReqRespStateIs Invalid (reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]))"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal387: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal388: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i547) done
  show goal389: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal390: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i547 i904) done
  show goal391: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal392: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i367 i547) done
  show goal393: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal394: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i547 i553) done
  show goal395: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal396: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i547 i555) done
  show goal397: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 i929 i946 nextReqIs_ISDIData) done
  show goal398: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside aux3_r42 i557 i564 i947 nextReqIs_ISDIData) done
  show goal399: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(95) i221 i558) done
  show goal400: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(95) i221) done
  show goal401: "CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_different1 CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(295) MESI_State.distinct(315) i1x i2x i352 i560) done
  show goal402: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i561 i563 nextReqIs_ISDIData) done
  show goal403: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> nextEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_nextEvict i562 nextReqIs_ISDIData) done
  show goal404: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal405: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i564 nextReqIs_ISDIData) done
  show goal406: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 i565 nextReqIs_ISDIData) done
  show goal407: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextReqIs CleanEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal408: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal409: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal410: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal411: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> ((CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)) \<and> \<not> ((CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal412: "nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal413: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal414: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal415: "nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_nextGOPendingIs aux4_r42 i578) done
  show goal416: "nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_nextGOPendingIs aux4_r42 i578) done
  show goal417: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) g39aux1 i221) done
  show goal418: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 HSTATE_general_rule_5_0 i183 i345 i581 nextHTDDataPending_otherside_rule_2_0) done
  show goal419: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal420: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal421: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal422: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal423: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal424: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal425: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs assms aux4_r42 i313 i672 i796) done
  show goal426: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i221) done
  show goal427: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i221) done
  show goal428: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done

  show goal429: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply(insert i1x i377) 
 by (metis aux429 snps1_empty_not_nextSnoopIs_rule_7_0)

  show goal430: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_nextSnoopIs i593) done
  show goal431: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal432: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal433: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 FixISDIData.device_perform_op_htddatas2 HTDDataPending_htddatas_invariant2 hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i353 i596 i600 nextHTDDataPending_various_forms2 nextSnoopIs_general_rule_7_0 remove_instr_HSTATE) done
  show goal434: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis CSTATE_disj1 MESI_State.distinct(295) MESI_State.distinct(315) assms hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i352 i601 nextSnoopIs_general_rule_7_0 remove_instr_HSTATE) done
  show goal435: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal436: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms i377 i599 i914 nextGOPending_DeviceISDIData) done
  show goal437: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 HSTATE_rule_6 i600 nextHTDDataPending_otherside_rule_2_0 nextSnoopIs_general_rule_7_0) done
  show goal438: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis HSTATE_general_rule_5_0 i1x i2x i352 i460 i597 i621 i625 i631 i924 nextSnoopIs_general_rule_7_0) done
  show goal439: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) MESI_State.distinct(141) i221) done
  show goal440: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms i602 i603 i672) done
  show goal441: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) MESI_State.distinct(171) i221) done
  show goal442: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms i604 i605 i672) done
  show goal443: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(151) i221) done
  show goal444: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms i606 i607 i672) done
  show goal445: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal446: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal447: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal448: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE assms i608 i611 i672 nextGOPending_DeviceISDIData) done
  show goal449: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE assms i609 i612 i672 nextGOPending_DeviceISDIData) done
  show goal450: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<or> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE assms i672 i915 i917) done
  show goal451: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i221) done
  show goal452: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) MESI_State.distinct(315) assms i352 i470 i509) done
  show goal453: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i221) done
  show goal454: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis assms empty_no_snoop2 i377 snps2_general_rule_7_0) done
  show goal455: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal456: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (metis assms empty_no_snoop2 i377 snps2_general_rule_7_0) done
  show goal457: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal458: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621) done
  show goal459: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal460: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621 i623) done
  show goal461: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal462: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621 i625) done
  show goal463: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal464: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i352 i509 i914 nextGOPending_DeviceISDIData) done
  show goal465: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(171) i221) done
  show goal466: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621 i629) done
  show goal467: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal468: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621 i631) done
  show goal469: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) MESI_State.distinct(141) i221) done
  show goal470: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i633 i748) done
  show goal471: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<longrightarrow> \<not> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal472: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<longrightarrow> \<not> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i635 nextGOPending_DeviceISDIData) done
  show goal473: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(139) i221) done
  show goal474: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_different1 CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(295) MESI_State.distinct(315) i1x i2x i352 i637) done
  show goal475: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i221) done
  show goal476: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different2 CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(227) MESI_State.distinct(247) i1x i353 i460) done
  show goal477: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal478: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i641 i643) done
  show goal479: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal480: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i643) done
  show goal481: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal482: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i643 i645) done
  show goal483: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(139) i221) done
  show goal484: "CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i401) done
  show goal485: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) i221) done
  show goal486: "CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i647) done
  show goal487: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal488: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i148) done
  show goal489: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal490: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i148) done
  show goal491: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) i221) done
  show goal492: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i653) done
  show goal493: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) MESI_State.distinct(171) i221) done
  show goal494: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i655) done
  show goal495: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal496: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i657 nextGOPending_DeviceISDIData) done
  show goal497: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal498: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i659 nextGOPending_DeviceISDIData) done
  show goal499: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal500: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal501: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal502: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal503: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal504: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal505: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal506: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal507: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal508: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal509: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal510: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal511: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal512: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal513: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal514: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal515: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal516: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal517: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal518: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i643 i678) done
  show goal519: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal520: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i342 i377 nextGOPending_DeviceISDIData) done
  show goal521: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal522: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(259) assms i682) done
  show goal523: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal524: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(259) assms i684) done
  show goal525: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal526: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_nextSnoopIs MESI_State.distinct(259) assms i686) done
  show goal527: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal528: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i688) done
  show goal529: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal530: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i690) done
  show goal531: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal532: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i698) done
  show goal533: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal534: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal535: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal536: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(5) i221 i702) done
  show goal537: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> length (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1 \<and> length (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 i883 i884) done
  show goal538: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> length (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1 \<and> length (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal539: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal540: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal541: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> length (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1 \<and> length (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 FixISDIData.device_perform_op_dthdatas2 i883 i884) done
  show goal542: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal543: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE i709 nextDTHDataFrom_general_rule_4_0) done
  show goal544: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal545: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal546: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal547: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE i794 nextDTHDataFrom_general_rule_4_0) done
  show goal548: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal549: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal550: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal551: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal552: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 ISDIData_HSTATE g39aux i718 nextDTHDataFrom_general_rule_4_0) done
  show goal553: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal554: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps2 ISDIData_HSTATE g39aux i720 nextDTHDataFrom_general_rule_4_0) done
  show goal555: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal556: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal557: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) MESI_State.distinct(171) i221) done
  show goal558: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i724) done
  show goal559: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal560: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal561: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> lastSharer ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal562: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> lastSharer ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant MESI_State.distinct(137) MESI_State.distinct(95) i221 i947 nextReqIs_ISDIData) done
  show goal563: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> lastSharer ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) assms i561 i563 nextReqIs_ISDIData) done
  show goal564: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> lastSharer ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal565: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal566: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal567: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal568: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE i734 nextDTHDataFrom_general_rule_4_0) done
  show goal569: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal570: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_different1 CSTATE_otherside_rule_5_0 HSTATE_rule_6 MESI_State.distinct(315) i1x i2x i336 i352 i736 nextHTDDataPending_otherside_rule_2_0) done
  show goal571: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (metis CSTATE_assign_rule_6 CSTATE_disj1 CSTATE_otherside_rule_5_0 ISDIData_HSTATE ISDIData_nextGOPendingIs MESI_State.distinct(175) i737) done
  show goal572: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE MESI_State.distinct(175) i221 i738) done
  show goal573: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps2 MESI_State.distinct(295) MESI_State.distinct(315) assms hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i352 i452 remove_instr_HSTATE) done
  show goal574: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(175) i221 i740) done
  show goal575: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal576: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal577: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal578: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal579: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) HSTATE_general_rule_5_0 i2x i745 i83 nextReqIs_general_rule_7_0 reqs1_empty_not_nextReqIs_general_invariant) done
  show goal580: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i379 nextReqIs_ISDIData) done
  show goal581: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(141) i221 i747) done
  show goal582: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(141) i221 i748) done
  show goal583: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE MESI_State.distinct(141) i221 i749) done
  show goal584: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps2 MESI_State.distinct(295) MESI_State.distinct(315) assms hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i352 i452 remove_instr_HSTATE) done
  show goal585: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal586: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal587: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal588: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal589: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal590: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0))"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal591: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal592: "CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal593: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqresps2 g39aux i759) done
  show goal594: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 assms g39aux i377) done
  show goal595: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal596: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal597: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal598: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal599: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal600: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal601: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal602: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal603: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal604: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal605: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal606: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i776 nextDTHDataFrom_general_rule_4_0) done
  show goal607: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal608: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i776 nextDTHDataFrom_general_rule_4_0) done
  show goal609: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal610: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal611: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i777 nextReqIs_ISDIData) done
  show goal612: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdShared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i778 nextReqIs_ISDIData) done
  show goal613: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal614: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal615: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal616: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal617: "snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal618: "snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<and> HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal619: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(151) i221) done
  show goal620: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal621: "nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal622: "nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i788 nextDTHDataFrom_general_rule_4_0 nextReqIs_ISDIData) done
  show goal623: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i789 nextSnpRespIs_general_rule_7_0) done
  show goal624: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspSFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal625: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal626: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal627: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal628: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE i794 nextDTHDataFrom_general_rule_4_0) done
  show goal629: "HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i795) done
  show goal630: "HSTATE SharedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i796) done
  show goal631: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(163) i221) done
  show goal632: "CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 HSTATE_general_rule_5_0 MESI_State.distinct(259) aux3_r42 i1x i2x i352 i798) done
  show goal633: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal634: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps2 ISDIData_HSTATE i800) done
  show goal635: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(139) i221 i802) done
  show goal636: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) i221) done
  show goal637: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i804 nextDTHDataFrom_general_rule_4_0) done
  show goal638: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(95) i221 i805) done
  show goal639: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snpresps2 ISDIData_HSTATE g39aux i806) done
  show goal640: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal641: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i807 i808 nextDTHDataFrom_general_rule_4_0) done
  show goal642: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(175) i221 i809) done
  show goal643: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal644: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE i811 nextDTHDataFrom_general_rule_4_0 nextReqIs_ISDIData) done
  show goal645: "HSTATE MB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(141) i221 i812) done
  show goal646: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(175) i221) done
  show goal647: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(163) i221) done
  show goal648: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal649: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal650: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal651: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i817 i818 nextDTHDataFrom_general_rule_4_0) done
  show goal652: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal653: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal654: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal655: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i776 nextDTHDataFrom_general_rule_4_0) done
  show goal656: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal657: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs RdOwn ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i824 nextReqIs_ISDIData) done
  show goal658: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal659: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal660: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal661: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal662: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal663: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal664: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal665: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal666: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal667: "CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal668: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal669: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms g39aux i377) done
  show goal670: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal671: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal672: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal673: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(175) i221 i840 nextDTHDataFrom_general_rule_4_0) done
  show goal674: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal675: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) g39aux i221) done
  show goal676: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal677: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal678: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal679: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 assms g39aux i377) done
  show goal680: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal681: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> (CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(143) i221) done
  show goal682: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal683: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE ISA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(141) MESI_State.distinct(95) i221) done
  show goal684: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal685: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal686: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal687: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal688: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms g39aux i377) done
  show goal689: "CSTATE Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal690: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal691: "HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE ISD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 HSTATE_rule_6 MESI_State.distinct(185) MESI_State.distinct(259) i113 i1x nextDTHDataFrom_general_rule_4_0) done
  show goal692: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE ISDIData_nextGOPendingIs aux4_r42 i859) done
  show goal693: "HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal694: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal695: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE ISAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_otherside_rule_5_0 empty_no_snoop_variant i2x i466 i599 nextGOPending_General_rule_4_1) done
  show goal696: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal697: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i516 i864 i914 nextGOPending_DeviceISDIData nextReqIs_ISDIData) done
  show goal698: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal699: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms i377 i599 i914 nextGOPending_DeviceISDIData) done
  show goal700: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal701: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal702: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i577) done
  show goal703: "CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant Invalid_not_eq_MIA i221) done
  show goal704: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal705: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal706: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal707: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i943 nextSnpRespIs_general_rule_7_0) done
  show goal708: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_different1 HSTATE_general_rule_5_0 MESI_State.distinct(295) MESI_State.distinct(315) i1x i2x i352 i875 nextSnpRespIs_general_rule_7_0) done
  show goal709: "length (dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 i883) done
  show goal710: "length (dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])) \<le> 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas2 i884) done
  show goal711: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal712: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal713: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal714: "HSTATE MAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(295) assms i425 i888 nextDTHDataFrom_general_rule_4_0) done
  show goal715: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps1 ISDIData_HSTATE MESI_State.distinct(95) i221 i889) done
  show goal716: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> [] \<longrightarrow> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE Shared ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant FixISDIData.device_perform_op_snpresps2 MESI_State.distinct(295) MESI_State.distinct(315) assms hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i2x i352 i452 remove_instr_HSTATE) done
  show goal717: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal718: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqresps1 FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal719: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal720: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal721: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> (htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal722: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> (htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<or> CSTATE ISDI ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0)"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) g39aux i221) done
  show goal723: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal724: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_dthdatas2 g39aux i898) done
  show goal725: "nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) MESI_State.distinct(169) i221) done
  show goal726: "nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i900 nextSnpRespIs_general_rule_7_0) done
  show goal727: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal728: "CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i643 i902) done
  show goal729: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal730: "CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending assms i547 i904) done
  show goal731: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(149) i221) done
  show goal732: "CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside assms i829 i833 nextGOPending_DeviceISDIData) done
  show goal733: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(169) i221) done
  show goal734: "CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal735: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(147) i221) done
  show goal736: "CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal737: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal738: "HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside ISDIData_HSTATE i912 nextDTHDataFrom_general_rule_4_0) done
  show goal739: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal740: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal741: "HSTATE InvalidM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i672) done
  show goal742: "HSTATE IB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i770) done
  show goal743: "HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant ISDIData_HSTATE MESI_State.distinct(167) i221 i917) done
  show goal744: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE i918 nextReqIs_ISDIData nextSnpRespIs_general_rule_7_0) done
  show goal745: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE i919 nextReqIs_ISDIData nextSnpRespIs_general_rule_7_0) done
  show goal746: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal747: "CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux) done
  show goal748: "HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal749: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal750: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpInv ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant FixISDIData.device_perform_op_nextHTDDataPending ISDIData_nextSnoopIs MESI_State.distinct(295) assms i621 i924) done
  show goal751: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) ISDIData_HSTATE assms i943 nextSnpRespIs_general_rule_7_0) done
  show goal752: "CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs DirtyEvict ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(167) i221) done
  show goal753: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i221) done
  show goal754: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE SA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_inequality_invariant MESI_State.distinct(5) i221) done
  show goal755: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal756: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending i930) done
  show goal757: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snpresps2 FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal758: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> snpresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = [] \<and> htddatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_htddatas2 FixISDIData.device_perform_op_snpresps1 FixISDIData.device_perform_op_snps1 assms g39aux i377 i932 nextGOPendingStateGeneral_rule_4_1 nextGOPending_DeviceISDIData) done
  show goal759: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (metis CSTATE_otherside_rule_5_0 HSTATE_general_rule_5_0 assms i2x i417 i547 i577 i643 i833 nextGOPending_General_rule_4_1 nextHTDDataPending_otherside_rule_2_0) done
  show goal760: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis ISDIData_HSTATE assms empty_no_snoop_variant i2x i417 i466 i547 i577 i643 i833 i852 i921 i922 nextHTDDataPending_various_forms1) done
  show goal761: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_dthdatas1 ISDIData_HSTATE assms i153) done
  show goal762: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<noteq> []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_dthdatas2 ISDIData_HSTATE i936 nextGOPendingStateGeneral_rule_4_1 nextGOPending_DeviceISDIData) done
  show goal763: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_different1 MESI_State.distinct(179) i221) done
  show goal764: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (metis CSTATE_inequality_invariant CSTATE_otherside_rule_5_0 HSTATE_general_rule_5_0 MESI_State.distinct(295) MESI_State.distinct(315) assms i2x i352 i938 nextGOPendingStateGeneral_rule_4_1 nextGOPending_General_rule_4_1) done
  show goal765: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps1 assms g39aux i377) done
  show goal766: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_snps2 assms g39aux i377) done
  show goal767: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> reqs1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_reqs1 HTDDataPending_htddatas_invariant1 assms i100) done
  show goal768: "CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> reqs2 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) = []"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside FixISDIData.device_perform_op_reqs2 i942 nextGOPendingStateGeneral_rule_4_1 nextGOPending_DeviceISDIData) done
  show goal769: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) g39aux1) done
  show goal770: "HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<and> nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE i944 nextSnpRespIs_general_rule_7_0) done
  show goal771: "HSTATE SB ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside CSTATE_inequality_invariant Invalid_not_eq_MIA assms i221 i577) done
  show goal772: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i929 i946 nextReqIs_ISDIData) done
  show goal773: "nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) CSTATE_ISDIData_otherside i947 nextReqIs_ISDIData) done
  show goal774: "nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) assms i190 nextDTHDataFrom_general_rule_4_0) done
  show goal775: "nextSnpRespIs RspIHitSE ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
 apply  (insert assms)(**)apply (smt (verit) i949 nextDTHDataFrom_general_rule_4_0 nextSnpRespIs_general_rule_7_0) done
  show goal776: "nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
 apply  (insert assms)(**)apply (smt (verit) assms i563 nextReqIs_ISDIData) done
  show goal777: "nextSnpRespIs RspIFwdM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> \<not> nextReqIs CleanEvictNoData ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1"
 apply  (insert assms)(**)apply (smt (verit) i951 nextReqIs_ISDIData nextSnpRespIs_general_rule_7_0) done
  show goal778: "(CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) "

 by (metis CSTATE_assign_rule_6 CSTATE_disj1 MESI_State.distinct(169))
  show goal779: "(CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextSnoopIs SnpData ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<longrightarrow> HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])) "

 by (metis CSTATE_ISDIData_otherside ISDIData_HSTATE ISDIData_nextSnoopIs i953 nextGOPending_DeviceISDIData)
  show goal780: "((CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or>(CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) "

 by (metis CSTATE_ISDIData_otherside FixISDIData.device_perform_op_nextHTDDataPending ISDIData_HSTATE goal144 goal359 i1x i221 i2x i353 i417 i547 i577 i643 i833 nextGOPending_DeviceISDIData)
  show goal781: "((CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or>(CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0)   "
proof (-)
  show goal1: "(CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
  apply  (cases "program1 T") apply  (auto)
apply (metis CSTATE_various_forms6 HSTATE_def i1x i2x i317 i417 i577 i833 i852 i921 nextHTDDataPending_various_forms1 nextHTDDataPending_various_forms2) 
apply (metis CSTATE_different1 CSTATE_various_forms4 HSTATE_various_forms2 MESI_State.distinct(299) MESI_State.distinct(319) assms i377 i489 i582 i737 i955 nextGOPending_various_forms5 nextHTDDataPending_various_forms1 nextReqRespIs.simps(1)) 
 done

qed
  show goal782: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or>(CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) "

 by (metis goal144 goal359 i221)
  show goal783: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or>(CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0)   "
proof (-)
  show goal1: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE ModifiedM ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> CSTATE Modified ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextGOPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> (CSTATE IMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
  apply  (cases "program1 T") apply  (auto)
apply (metis CSTATE_various_forms6 HSTATE_various_forms2 MESI_State.distinct(359) MESI_State.distinct(389) MESI_State.distinct(417) MESI_State.distinct(47) MESI_State.distinct(569) MESI_State.distinct(579) MESI_State.distinct(587) i1x i2x i417 i577) 
apply (metis CSTATE_various_forms3 CSTATE_various_forms6 HOST_State.distinct(15) HSTATE_def HSTATE_various_forms2 MESI_State.distinct(47) MESI_State.distinct(579) assms i1x i2x i352 i417 i466 i475 i548 i577 i692 i694 i741 i757 i833 i843 i901 i903 i909 i910 i913 i930 i934 nextGOPendingState_def nextGOPending_various_forms6) 
 done

qed
  show goal784: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<noteq> []) "

 by (smt (verit) goal146 i221)
  show goal785: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> dthdatas2 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<noteq> [])  "

 by (metis ISDIData_HSTATE assms i153 i190 i2x nextDTHDataFrom_def)
  show goal786: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> ((CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1)) "

 by (metis CSTATE_assign_rule_6 goal304)
  show goal787: "((CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> ((CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0)) "
proof (-)
  show goal1: "(CSTATE SIAC ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingState Invalid ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 1 \<and> \<not> CSTATE IIA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<and> GTS ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> HSTATE MA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (CSTATE IMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMAD ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0) \<and> nextHTDDataPending ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE IMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0 \<or> CSTATE SMA ( T [ 0 s= Invalid] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ]) 0"
  apply  (cases "program1 T") apply  (auto)
apply (metis CSTATE_various_forms6 HSTATE_various_forms2 MESI_State.distinct(579) assms i1x i2x i378 i460 i833 i930 nextGOPending_def nextReqRespIs.simps(1)) 
apply (metis CSTATE_various_forms3 CSTATE_various_forms4 HSTATE_various_forms2 MESI_State.distinct(579) i1x i2x i460 i833 i930 nextGOPending_various_forms4) 
 done

qed


  show goal788: "(HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps2 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = []) "

 by (smt (verit) i190 i2x nextDTHDataFrom_general_rule_4_0)
  show goal789: "(HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> snps1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = []) "

 by (smt (verit) goal688 i221)
  show goal790: "(HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = []) "

 by (smt (verit) goal266 i221)
  show goal791: "(HSTATE SD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> reqresps2 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = []) "

 by (metis FixISDIData.device_perform_op_reqresps2 hstate_invariants(17) hstate_invariants(20) hstate_invariants(24) i965 nextDTHDataFrom_general_rule_4_0 remove_instr_HSTATE)

  show goal792: "(HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 0 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) ) "

 by (metis i190 i2x nextDTHDataFrom_general_rule_4_0)
  show goal793: "(HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0) ) "

 by (metis ISDIData_HSTATE i2x i776 nextDTHDataFrom_general_rule_4_0)
  show goal794: "(CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1)) "

 by (metis CSTATE_assign_rule_6 CSTATE_inequality_invariant Invalid_not_eq_MIA)
  show goal795: "(CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> nextGOPendingIs GO_WritePull ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 \<and> HSTATE ID ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> (\<not> CSTATE SIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<or> nextGOPendingIs GO_WritePullDrop ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0))  "

 by (smt (verit) CSTATE_ISDIData_otherside i2x i577)

  show goal796: "(HSTATE SAD ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<and> nextDTHDataFrom 1 ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) \<longrightarrow> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 \<and> \<not> CSTATE MIA ( T [ 0 s= Invalid] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1) "

    by (metis CSTATE_assign_rule_6 CSTATE_disj1 CSTATE_otherside_rule_8 Invalid_not_eq_MIA goal150 i2x i577)
qed

qed





lemma ISDIData_coherent: shows "
SWMR_state_machine T \<Longrightarrow> Lall (ISDIData' T 0) SWMR_state_machine
"
  unfolding ISDIData'_def copyInDataPerformInstr_def

  using ISDIData'_coherent_aux_simpler 

  by (metis Lall.simps(1) clearBuffer_def general_helper)


end
