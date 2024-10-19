theory BasicInvariants imports BuggyRules begin

\<comment>\<open>
definition "InvalidLoad' T i = (if (CSTATE Invalid T i \<and> nextLoad T i) then [clearBuffer (sendReq RdShared ISAD i T)] else [])"
definition "SharedLoad' T i = (if (CSTATE Shared T i \<and> nextLoad T i) then [ clearBuffer (T[  :=i i  ]) ] else [])"
definition "InvalidStore' T i = (if (CSTATE Invalid T i \<and> nextStore T i) then [clearBuffer (sendReq RdOwn IMAD i T)] else [])"
definition "SharedStore' T i = (if (CSTATE Shared T i \<and> nextStore T i) then [clearBuffer (sendReq RdOwn SMAD i T)] else [])"
definition "SharedEvict' T i = (if (CSTATE Shared T i \<and> nextEvict T i) then [clearBuffer (sendReq CleanEvictNoData SIA i T)] else [])"
definition "ModifiedEvict' T i = (if (CSTATE Modified T i \<and> nextEvict T i) then [clearBuffer (sendReq DirtyEvict MIAD i T)] else [])"
\<comment>\<open>Six "Instruction starting" transitions are grouped together\<close> 
definition "SMADLoad' T i = (if CSTATE SMAD T i \<and> nextLoad T i then [clearBuffer (T[ :=i i])] else [])"
definition "SMALoad' T i = (if CSTATE SMA T i \<and> nextLoad T i then [clearBuffer (T[ :=i i])] else [])"
definition "ModifiedStore' T i = (if  CSTATE Modified T i \<and> nextStore T i then [clearBuffer T[ :=i i]] else [])"
definition "ModifiedLoad' T i = (if CSTATE Modified T i \<and> nextLoad T i then [clearBuffer T [ :=i i]] else [])"
\<comment>\<open>4 device can perform instruction without requesting/upgrading  ownership\<close>
\<close>


lemma nextDTHDataFrom_IXADGO_invariant1: "nextDTHDataFrom j  ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ k -=reqresp ]) = nextDTHDataFrom j T"
  by simp

lemma nextDTHDataFrom_IXADGO_invariant1_neg: "(\<not> nextDTHDataFrom j  ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ k -=reqresp ])) = (\<not> nextDTHDataFrom j T)"
  by simp

lemma dthdatas1_empty_invariant1: "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 T) = 0"
  by simp

lemma dthdatas1_empty_invariant2: "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 T) \<le> 1"
  by simp

lemma dthdatas2_empty_invariant1: "dthdatas2 T = [] \<Longrightarrow> length (dthdatas2 T) = 0"
  by simp

lemma dthdatas2_empty_invariant2: "dthdatas2 T = [] \<Longrightarrow> length (dthdatas2 T) \<le> 1"
  by simp

lemma dthdatas1_minus1_invariant: "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 ( T [ =hv v] [ 5 sHost= h] [ Dev1 -=d2hdHead ]) = []"
  apply(case_tac "dthdatas1 T")
   apply simp+
  done


lemma dthdatas1_minus1_otherside: " dthdatas1 ( T [ =hv v] [ 5 sHost= h] [ Dev2 -=d2hdHead ]) = dthdatas1 T"
  apply(case_tac "dthdatas1 T")
   apply simp+
  done

lemma dthdatas2_minus1_invariant: "length (dthdatas2 T) \<le> 1 \<Longrightarrow> dthdatas2 ( T [ =hv v] [ 5 sHost= h] [ Dev2 -=d2hdHead ]) = []"
  apply(case_tac "dthdatas2 T")
   apply simp+
  done

lemma dthdatas2_minus1_otherside: " dthdatas2 ( T [ =hv v] [ 5 sHost= h] [ Dev1 -=d2hdHead ]) = dthdatas2 T"
  apply(case_tac "dthdatas1 T")
   apply simp+
  done

lemma dthdatas1_minus1_invariant2: "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1 (  T [ di +=h2dd hmsg] [    =hv v] [ 5 sHost= h] [ Dev1 -=d2hdHead ]) = []"
  apply(case_tac "dthdatas1 T")
  apply(cases di)
    apply simp+
  apply(cases di)
  apply simp+
  done

lemma dthdatas2_minus1_invariant2: "length (dthdatas2 T) \<le> 1 \<Longrightarrow> dthdatas2 (  T [ di +=h2dd hmsg] [    =hv v] [ 5 sHost= h] [ Dev2 -=d2hdHead ]) = []"
  apply(case_tac "dthdatas2 T")
  apply(cases di)
    apply simp+
  apply(cases di)
  apply simp+
  done


lemma SARspX_invariant1: "\<not> nextGOPendingIs GO_WritePull T 1 \<Longrightarrow> 
  \<not> nextGOPendingIs GO_WritePull (  T [ 1 +=reqresp GO m txid] [ 5 sHost= h] [ j -=snpresp  ]) 1"
  apply(cases "reqresps2 T")
   apply simp+
  done

lemma SARspX_invariant2: "\<not> nextGOPendingIs GO_WritePull T 0 \<Longrightarrow> 
  \<not> nextGOPendingIs GO_WritePull (  T [ 0 +=reqresp GO m txid] [ 5 sHost= h] [ j -=snpresp  ]) 0"
  apply(cases "reqresps1 T")
   apply simp+
  done

lemma cache_state_invariant [simp]: \<open>  (CLEntry.block_state (devcache2 T)) =  (CLEntry.block_state (devcache2 (T [ i -=snp ])))\<close>
\<open>  (CLEntry.block_state (devcache1 T)) =  (CLEntry.block_state (devcache1 (T [ i -=snp ])))\<close>
  unfolding consume_snoop_def
   apply (simp add: Nitpick.case_nat_unfold)+
  done

lemma reqresps_invariant [simp]: \<open>(reqresps1 T) = (reqresps1 (T [ i -=snp ]))\<close>
              \<open>(reqresps2 T) = (reqresps2 (T [ i -=snp ]))\<close>
  unfolding consume_snoop_def
  by (simp add: Nitpick.case_nat_unfold)+







lemma hstate_invariants [simp]: 
\<open>HSTATE X T = HSTATE X (T [ dv =dm s])\<close> 

\<open>HSTATE X T = HSTATE X (T \<lparr>buffer1 :=
              anyMessage\<rparr> )\<close>
\<open>HSTATE X T = HSTATE X (T \<lparr>buffer2 :=
              anyMessage\<rparr> )\<close>
\<open>HSTATE X T = HSTATE X (T [ i +=rdreq q])\<close> 
\<open>HSTATE X T = HSTATE X (T [i +=snp snptype tid]) \<close>
\<open>HSTATE X T = HSTATE X (T [dv +=h2dreq  snp_msgs]) \<close>
\<open>HSTATE X T = HSTATE X (T [i +=snpresp anysnpresptype tid] )\<close>
\<open> HSTATE X T = HSTATE X (T [ i +=reqresp reqrespt mesi_st tid ])\<close>
\<open> HSTATE X T = HSTATE X (T [ dv +=d2hd  dmsg])\<close>
\<open> HSTATE X T = HSTATE X (T [ dv +=h2dd  dmsg])\<close>
\<open> HSTATE X T = HSTATE X (T [ i +=hostdata  tid])\<close>
\<open>HSTATE X T = HSTATE X (T [i -=snp ] )\<close>
 \<open>HSTATE X T = HSTATE X (T [ i -=req ])\<close> 
\<open> HSTATE X T = HSTATE X (T [ i -=reqresp  ])\<close>
\<open> HSTATE X T = HSTATE X (T [ i -=snpresp  ])\<close>
\<open> HSTATE X T = HSTATE X (T [dv -=d2hdHead ]) \<close>
\<open> HSTATE X T = HSTATE X (T [i -=devd ]) \<close>
\<open> HSTATE X T = HSTATE X (T \<lparr>buffer1 :=
              Some (nextSnoop T i)\<rparr> [i +=snpresp RspIHitI (getTid (getSnoopOrMakeup (getSnoops i T)))] [i -=snp ])\<close>
\<open>HSTATE X T = HSTATE X (T [ i +=rdreq q]  [ dv =dm s])\<close>
\<open>HSTATE X T = HSTATE X (T [i :=dd data_msg])\<close>
\<open>HSTATE X T = HSTATE X (T [dv =dm mesi_st])\<close>
\<open> HSTATE X T = HSTATE X (T [  :=i i ]) \<close>
\<open> HSTATE X T = HSTATE X (T ++c ) \<close>
\<open> HSTATE X T = HSTATE X (T [i s= mesi]) \<close>
\<open> HSTATE X T = HSTATE X (T [ =hv  v] ) \<close>
  
                      apply simp
                      apply(case_tac dv)
                      apply simp
                      apply simp
                      apply simp
                      apply simp
                      apply(case_tac i)
                      apply simp
                      apply simp
  apply(case_tac i)
                      apply simp
                      apply simp
  apply(case_tac dv)
                      apply simp
                     apply simp
  apply(case_tac i)
                     apply simp+
  apply(case_tac i)
                    apply simp+
                  apply(case_tac dv)
                   apply simp+
                 apply(case_tac dv)
                  apply simp+
  apply(case_tac i)
                 apply simp+
  apply(case_tac i)
                apply simp+
  apply(case_tac dv)
            apply simp+
  apply(case_tac i)
          apply simp+
  apply(case_tac dv)
         apply simp+
  apply(case_tac i)
          apply simp+
  apply(case_tac i)
         apply simp+
  apply(case_tac i)
        apply simp+
  apply(case_tac dv)
       apply simp+
  apply(case_tac i)
      apply simp+
      apply(case_tac "program1 T")
       apply simp
  apply(case_tac a)
        apply simp+
       apply(case_tac x2)
        apply simp
  apply(case_tac n)
         apply simp+
      apply(case_tac "program2 T")
       apply simp
  apply(case_tac a)
        apply simp+
       apply(case_tac x2)
        apply simp
  apply(case_tac n)
         apply simp+     
  done




\<comment>\<open>Doing an InvalidLoad' doesn't change state beyond just started
lemma invalid_load_just_started [simp]: \<open>\<lbrakk> CSTATE Invalid T i\<rbrakk> \<Longrightarrow> devJustStarted T i = Lall (InvalidLoad' T i) (\<lambda>T'. devJustStarted T' i)  = True\<close>

  

lemma invalid_load_keeps_Host_same [simp]: \<open>\<lbrakk>CSTATE Invalid T 0 \<rbrakk> \<Longrightarrow> X_means_devStableOrBeginningOrEnding T =  Lall (InvalidLoad' T 0) X_means_devStableOrBeginningOrEnding\<close>

   

lemma GSWMR_invariants_dev_memory_state: shows "\<lbrakk> GSWMR T; InvalidFamily st \<rbrakk>\<Longrightarrow> GSWMR ( T [ devi =dm st] )"
  unfolding GSWMR_def
  unfolding InvalidFamily_def
  unfolding GOwner_def
  unfolding GReader_def
  apply simp
  


lemma GSWMR_invariants_plus_req: shows "GSWMR T \<Longrightarrow> GSWMR ( T [ i +=rdreq anyreqtype] )"
  



lemma allInvalid_invariants_plus_req: shows "\<lbrakk> allInvalid T\<rbrakk> \<Longrightarrow> allInvalid (T [i +=rdreq anyreqtype])"
  

lemma allInvalid_invariants_dev_memory_state: shows "\<lbrakk> allInvalid T; InvalidFamily st \<rbrakk> \<Longrightarrow> allInvalid (T [devi =dm st])"
  

\<close>











lemma [simp]: \<open>Owner (CLEntry.block_state (devcache1 (T [a sHost= b]))) =
     Owner (CLEntry.block_state (devcache1 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache1 (T ++cl))) =
     Owner (CLEntry.block_state (devcache1 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache1 (T [ q -=req] ))) =
     Owner (CLEntry.block_state (devcache1 T))\<close>

\<open>Owner (CLEntry.block_state (devcache2 (T [a sHost= b]))) =
     Owner (CLEntry.block_state (devcache2 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache2 (T [ q -=req] ))) =
     Owner (CLEntry.block_state (devcache2 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache2 (T [ q' +=reqresp t k l] ))) =
     Owner (CLEntry.block_state (devcache2 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache2 (T ++cl))) =
     Owner (CLEntry.block_state (devcache2 T))\<close>
  \<open>Owner (CLEntry.block_state (devcache1 (T [ q' +=reqresp t k l] ))) =
     Owner (CLEntry.block_state (devcache1 T))\<close>
  by (auto simp: change_host_state_def update_clock_def consumeReq_def host_sends_response_def Let_def)




definition "allDevicesInvalid T = ((CSTATE Invalid T 0 \<or> CSTATE ISAD T 0 \<or> CSTATE IMAD T 0 ) \<and> (CSTATE Invalid T 1) \<and>
  (block_state (hostcache T) = InvalidM) )"



lemma snoopsRespsExclusive_general_invariant1: shows "snoopsRespsExclusive T \<Longrightarrow> snoopsRespsExclusive (T [ 0 -=snpresp  ])"
  unfolding snoopsRespsExclusive_def  
  unfolding consume_snoopresp_def
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  apply(rule conjI)
  apply simp
   apply force
  apply(rule conjI)
  apply force
  by (simp add: Type1State.update_convs(6))

lemma snoopsRespsExclusive_general_invariant1_1: shows "snoopsRespsExclusive T \<Longrightarrow> snoopsRespsExclusive (T [ 1 -=snpresp  ])"
  unfolding snoopsRespsExclusive_def  
  unfolding consume_snoopresp_def
  apply(erule conjE)+
  apply(rule conjI)
   apply simp
  apply(rule conjI)
  apply simp
  apply force
  done

lemma snoopsRespsExclusive_general_invariant1_x: shows "snoopsRespsExclusive T \<Longrightarrow> snoopsRespsExclusive (T [ i -=snpresp  ])"
  by (metis consume_snoopresp_def one_neq_zero snoopsRespsExclusive_general_invariant1 snoopsRespsExclusive_general_invariant1_1)

lemma snoopsRespsExclusive_general_invariant2: shows "snoopsRespsExclusive T = snoopsRespsExclusive (T [j sHost= X])"
  by (simp add: snoopsRespsExclusive_def)






lemma no2SnpResps_general_invariant2: shows "no2SnpResps T = no2SnpResps ( T  [ j sHost= mesi]  )"
  
  by (simp add: no2SnpResps_def)

lemma no2SnpResps_general_invariant3: shows "no2SnpResps T \<Longrightarrow> no2SnpResps ( T  [ i -=snpresp  ] )"
  unfolding no2SnpResps_def consume_snoopresp_def
  apply(case_tac i)
   apply simp
  prefer 2
   apply simp
  apply(case_tac "snpresps2 T")
  apply simp
  apply simp
    apply(case_tac "snpresps1 T")
  apply simp  
  by simp


lemma no2Reqs_invariant_general2: shows "no2Reqs T = no2Reqs ( T [ j sHost= mesi] )"
  
  by (simp add: no2Reqs_def)

lemma no2Reqs_invariant_general3: shows "no2Reqs T = no2Reqs ( T [ i -=snpresp ] )"  
  by (simp add: Type1State.update_convs(6) Type1State.update_convs(7) consume_snoopresp_def no2Reqs_def)



lemma snpRespCorrect_invariant_general2: shows "snpRespCorrect T =  snpRespCorrect (T  [ i sHost= mesi]) "
  
  by (simp add: CSTATE_def Type1State.iffs Type1State.surjective Type1State.update_convs(1) change_host_state_def nextSnpRespIs_def snpRespCState_def snpRespCorrect_def)

lemma snpRespCorrect_invariant_general3_aux: shows "snpresps1 T = [] \<Longrightarrow>snpRespCState T 0"
  using nextSnpRespIs_property1 snpRespCState_def by blast

lemma snpRespCorrect_invariant_general3_aux2: shows "snpresps2 T = [] \<Longrightarrow>snpRespCState T 1"
  using nextSnpRespIs_property2 snpRespCState_def by blast




lemma emptied_snpresps_aux1: shows "length ((snpresps1 T)) \<le> 1 \<Longrightarrow> ((snpresps1
           (T\<lparr>reqresps2 := reqresps2 T @ [H2DResp (nextSnoopRespID T 0) GO Shared (clock T)],
                snpresps1 := case snpresps1 T of [] \<Rightarrow> [] | msg' # tail \<Rightarrow> tail\<rparr>) =
          []))"
  apply(case_tac "snpresps1 T")
   apply simp+
  done



lemma SPG_P1_invariant_general3: shows "snoopGORules_transitiveP1 T = snoopGORules_transitiveP1 (T [ i sHost= mesi] )"
  by (simp add: Type1State.iffs Type1State.surjective change_host_state_def snoopGORules_transitiveP1_def)


lemma GOwner_invariant_minus_snpresp: shows 
  "GOwner T i =   GOwner ( T  [ i -=snpresp  ] ) i"
  by (simp add: GOwner_def consume_snoopresp_def)

  



lemma GOwner_invariant_minus_snpresp_general: shows 
  "GOwner T i =   GOwner ( T  [ j -=snpresp  ] ) i"
   
  unfolding GOwner_def
  apply(case_tac i)
   apply(rule if_cong)
     apply simp
    apply(case_tac j)
  
     apply (metis GOwner_def GOwner_invariant_minus_snpresp)
  unfolding consume_snoopresp_def
    apply simp
   apply meson
  by simp


lemma GOwner_invariant_sHost: shows 
  "GOwner T i =   GOwner ( T  [ 5 sHost= SD] ) i"
  unfolding GOwner_def
  apply simp
  done

  

thm if_cong

lemma GOwner_reqresp_invariant_diff_device: shows "\<lbrakk>i \<noteq> j; i = 0 \<rbrakk> \<Longrightarrow> (GOwner T i =   GOwner ( T [ j +=reqresp GO X (nextSnoopRespID T k)] ) i)"
  unfolding GOwner_def
  apply(rule if_cong)
    apply simp+
  done
  

lemma GOwner_reqresp_invariant_diff_device_symm: shows "\<lbrakk>j = 0; i = 1 \<rbrakk> \<Longrightarrow> (GOwner T i =   GOwner ( T [ j +=reqresp GO X (nextSnoopRespID T k)] ) i)"
  by (simp add: GOwner_def)

  

lemma reqresp_updated_value : shows " (reqresps1 (T \<lparr> reqresps1 := y \<rparr>)) = y" "(reqresps2 ( T \<lparr> reqresps2 := y \<rparr>)) = y"
  by simp+


thm Lexists_nonEmpty.simps

\<comment>\<open>
proof (induct rs)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a rs)
  have "Lexists_nonEmpty (a # rs @ rs2) p = p a \<or> Lexists_nonEmpty (rs @ rs2) p"
    also 
  then show ?case 

qed
\<close>
lemma Lexists_nonEmpty_concat: shows "Lexists_nonEmpty (rs @ rs2) p = (Lexists_nonEmpty rs p \<or> Lexists_nonEmpty rs2 p)"

  apply(induct rs  )
   apply simp+
  done



\<comment>\<open>This rturns out to be not true: when Owner X = True, LHS = True, but RHS = False.
In other words, sending a GO granting Ownership is going to change a non-owner into an owner.\<close>
lemma GOwner_invariant_reqrespNonOwner1_0_expanded: shows"((Owner (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Owner (getGrantedState m))) =
     (Owner (CLEntry.block_state (devcache1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>))) \<or>
      Lexists_nonEmpty (reqresps1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>))
       (\<lambda>m. Owner (getGrantedState m)))) =
    ((Owner (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Owner (getGrantedState m))) = Owner X)"
  apply(subst reqresp_updated_value)
  apply(subst Lexists_nonEmpty_concat)
  apply(subgoal_tac "CLEntry.block_state (devcache1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache1 T)")
   apply(erule ssubst)
   apply(case_tac "((Owner (CLEntry.block_state (devcache1 T)) \<or> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Owner (getGrantedState m)))) = True")

  oops

  thm getGrantedState_def



lemma GOwner_invariant_reqrespNonOwner1_0: shows 
  "\<lbrakk>\<not>Owner X; \<not>GOwner T 0\<rbrakk> \<Longrightarrow> (\<not> GOwner (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T k) GO X (clock T)]\<rparr>) 0) "
  unfolding GOwner_def
  apply(subgoal_tac "(0 = 0) = True")
   apply(erule ssubst)
   apply(subst if_True)+
     apply(subst reqresp_updated_value)
  apply(subst Lexists_nonEmpty_concat)
  apply(subgoal_tac "CLEntry.block_state (devcache1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache1 T)")
   apply(erule ssubst)
  apply (simp add: getGrantedState_def)
  by simp+

lemma H: \<open>b = False \<Longrightarrow> (if b then P else Q) = Q\<close>
  by auto




lemma GOwner_invariant_reqrespNonOwner1_1: shows 
  "\<lbrakk>\<not>Owner X; \<not>GOwner T 1\<rbrakk> \<Longrightarrow> (\<not> GOwner (T\<lparr>reqresps2 := reqresps2 T @ [H2DResp (nextSnoopRespID T k) GO X (clock T)]\<rparr>) 1) "
  unfolding GOwner_def
  apply(subst (asm) H)
   apply simp
  apply(subst H)
  apply simp
  apply(subgoal_tac "CLEntry.block_state (devcache1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache1 T)")
   apply(erule ssubst)
  apply(subgoal_tac "CLEntry.block_state (devcache2 (T\<lparr>reqresps2 := reqresps2 T @ [H2DResp (nextSnoopRespID T 1) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache2 T)")
   apply(erule ssubst)

    apply(subst reqresp_updated_value)
  apply(subst Lexists_nonEmpty_concat)
  apply (simp add: getGrantedState_def)
  by simp+

lemma GOwner_invariant_reqrespNonOwner1_j: shows 
  "\<lbrakk>\<not>Owner X; \<not>GOwner T j; j \<noteq> 0\<rbrakk> \<Longrightarrow> (\<not> GOwner (T\<lparr>reqresps2 := reqresps2 T @ [H2DResp (nextSnoopRespID T k) GO X (clock T)]\<rparr>) j) "
  unfolding GOwner_def
  apply(subst (asm) H)
   apply simp
  apply(subst H)
  apply simp
  apply(subgoal_tac "CLEntry.block_state (devcache1 (T\<lparr>reqresps1 := reqresps1 T @ [H2DResp (nextSnoopRespID T 0) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache1 T)")
   apply(erule ssubst)
  apply(subgoal_tac "CLEntry.block_state (devcache2 (T\<lparr>reqresps2 := reqresps2 T @ [H2DResp (nextSnoopRespID T 1) GO X (clock T)]\<rparr>)) = 
    CLEntry.block_state (devcache2 T)")
   apply(erule ssubst)

    apply(subst reqresp_updated_value)
  apply(subst Lexists_nonEmpty_concat)
  apply (simp add: getGrantedState_def)
  by simp+




lemma GOwner_invariant_reqrespNonOwner: shows 
  "\<lbrakk>i = j;  \<not>Owner X ; \<not>GOwner T i\<rbrakk> \<Longrightarrow> (GOwner T i =   GOwner ( T [ j +=reqresp GO X (nextSnoopRespID T k)] ) i)"
  apply(subst Transposed.host_sends_response_def)


  apply(case_tac "j = 0")
  apply(subgoal_tac "i = 0")
    apply(rule ssubst)
     apply (simp (no_asm_simp) )
  using GOwner_invariant_reqrespNonOwner1_0 apply auto[1]
  using GOwner_invariant_reqrespNonOwner1_0 apply blast
  using GOwner_invariant_reqrespNonOwner1_j by auto




lemma GOwner_invariant_reqrespBecomesOwner: shows 
  "\<lbrakk>Owner X;  i = j\<rbrakk> \<Longrightarrow>    GOwner ( T [ j +=reqresp GO X (nextSnoopRespID T k)] ) i"

  oops




lemma HostSADRspIFwdM'_GOwner_equality1: shows 
  "\<lbrakk> i = j ; \<not> GOwner T i \<rbrakk> \<Longrightarrow> GOwner T i =   GOwner ( T [ j +=reqresp GO Shared (nextSnoopRespID T k)] [ 5 sHost= SD] [ i -=snpresp  ] ) i"
  apply(subgoal_tac "\<not> Owner Shared")
  using GOwner_invariant_minus_snpresp GOwner_invariant_reqrespNonOwner GOwner_invariant_sHost
  apply presburger
  by simp


lemma GOwner_equality_addition1: shows "\<lbrakk> \<not> GOwner T 1; \<not> Owner Shared\<rbrakk>
    \<Longrightarrow> \<not> (GOwner ( T [ 1 +=reqresp GO Shared (nextSnoopRespID T 0)]) 1)"
  using GOwner_invariant_reqrespNonOwner by presburger
  

lemma HSTATE_invariant_reqresp: shows "HSTATE X (T [  i +=reqresp rtype mesi txid] ) = HSTATE X T"
      apply(subst HSTATE_def)+ 
  using HSTATE_def hstate_invariants(8) by presburger
 


lemma HSTATE_invariant_msnpresp: shows "HSTATE X (T [ j -=snpresp  ] ) = HSTATE X T"
    apply(subst HSTATE_def)+
  by (simp add: consume_snoopresp_def) 
 

lemma HSTATE_equals_sHost: shows "HSTATE X (T [i sHost= Y]) = (X = Y)"
  apply(subst HSTATE_def)
  apply simp
  by force

lemma snprespInflight_general1: shows "snprespInflight X T i = snprespInflight X ( T [ j s= mesi]) i"
  unfolding snprespInflight_def change_state_def config_differ_dev_mapping_def
  by simp



lemma CSTATE_other_general1: shows "\<lbrakk>i = 0; j = 1 \<rbrakk> \<Longrightarrow> CSTATE mesi T i = CSTATE mesi (T [j s= X]) i"
  unfolding  change_state_def config_differ_dev_mapping_def CSTATE_def
  apply simp
  done

lemma CSTATE_other_general2: shows "\<lbrakk>i = 1; j = 0 \<rbrakk> \<Longrightarrow> CSTATE mesi T i = CSTATE mesi (T [j s= X]) i"
  unfolding  change_state_def config_differ_dev_mapping_def CSTATE_def
  apply simp
  done

lemma CSTATE_dthdata_general1: shows "CSTATE mesi T i = CSTATE mesi (T [ j :=dd x k])  i"
  unfolding CSTATE_def device_copy_in_data_def
  apply(cases i)
   apply(cases j)
    apply simp+
   apply(cases j)
    apply simp+
  done








lemma IMADDATA'_MA_aux1: shows "snpRespNotProcessedInv T 1 = snpRespNotProcessedInv ( T [ 0 s= IMA] ) 1"
  unfolding snpRespNotProcessedInv_def
  apply(case_tac "snprespInflight RspIHitI T 1 \<and> CSTATE Invalid T 1")
   apply(subgoal_tac "(snprespInflight RspIHitI ( T [ 0 s= IMA]) 1 \<and> CSTATE Invalid ( T [ 0 s= IMA]) 1)")
    apply blast
  using CSTATE_other_general2 snprespInflight_general1 apply presburger
  using CSTATE_other_general2 snprespInflight_general1 by presburger


lemma IMADDATA'_MA_aux1_rev: shows "snpRespNotProcessedInv T 0 = snpRespNotProcessedInv ( T [ 1 s= IMA] ) 0"
  unfolding snpRespNotProcessedInv_def
  apply(case_tac "snprespInflight RspIHitI T 0 \<and> CSTATE Invalid T 0")
   apply(subgoal_tac "(snprespInflight RspIHitI ( T [ 1 s= IMA]) 0 \<and> CSTATE Invalid ( T [ 1 s= IMA]) 0)")
    apply blast
  using CSTATE_other_general1 snprespInflight_general1 apply presburger
  using CSTATE_other_general1 snprespInflight_general1 by presburger



lemma IMADDATA'_MA_aux2: shows "snpRespNotProcessedInv T 1 = snpRespNotProcessedInv ( T [ 0 :=dd getHTDDataOrMakeup T 0] ) 1"
  unfolding snpRespNotProcessedInv_def  
  by (simp add: CSTATE_def Type1State.iffs Type1State.surjective Type1State.update_convs(2) device_copy_in_data_def snprespInflight_def)

lemma IMADDATA'_MA_devConsumeData_aux3: shows "snpRespNotProcessedInv T i = snpRespNotProcessedInv ( T [ j -=devd ] ) i"
  unfolding snpRespNotProcessedInv_def  devConsumeData_def
  by (simp add: CSTATE_def Type1State.iffs Type1State.surjective Type1State.update_convs(2) device_copy_in_data_def snprespInflight_def)

lemma snpRespNotProcessedInv_IMADData_general1: shows "snpRespNotProcessedInv T 1 = snpRespNotProcessedInv ( T [ 0 s= IMA] ) 1"  
  using IMADDATA'_MA_aux1 by presburger
  
lemma snpRespNotProcessedInv_IMADData_general1_rev: shows "snpRespNotProcessedInv T 0 = snpRespNotProcessedInv ( T [ 1 s= IMA] ) 0"  
  using IMADDATA'_MA_aux1_rev by presburger


lemma nextSnoopPending_device_state_invariant_general: shows "nextSnoopPending ( T [ i s= IMA]) j =  nextSnoopPending T j" 
  by (simp add: config_differ_dev_mapping_def nextSnoopPending_def)

lemma nextSnoopPending_device_copy_in_data_invariant_general1: shows "nextSnoopPending ( T  [ 0 :=dd msg]) = nextSnoopPending T"
  unfolding device_copy_in_data_def nextSnoopPending_def extractValFromMessage_def
  by force

lemma nextSnoopPending_device_copy_in_data_invariant_general2: shows "nextSnoopPending ( T  [ 1 :=dd msg]) = nextSnoopPending T"
  unfolding device_copy_in_data_def nextSnoopPending_def extractValFromMessage_def
  by simp

lemma nextSnoopPending_devConsume_data_invariant_rev: shows "nextSnoopPending T 0 = nextSnoopPending (T [ 1 -=devd ]) 0"
  unfolding devConsumeData_def nextSnoopPending_def
  by simp

lemma nextSnoopPending_devConsume_data_invariant: shows "nextSnoopPending T 1 = nextSnoopPending (T [ 0 -=devd ]) 1"
  unfolding devConsumeData_def nextSnoopPending_def
  by simp

lemma IMADData_CSTATE_IMA: shows "CSTATE IMA ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ]) 0"
  by simp

lemma IMADData_CSTATE_IMA1: shows "CSTATE IMA ( T [ 0 s= IMA]) 0"
  unfolding config_differ_dev_mapping_def change_state_def
  by simp

lemma CSTATE_equals_sequals_x: shows "i \<le> 1 \<Longrightarrow> CSTATE X (T [i s= X]) i"
  unfolding config_differ_dev_mapping_def change_state_def
  apply(case_tac "i = 0")
  apply simp+
  done

lemma CSTATEInvalid_reqrespsEmpty_nonReader: shows "\<lbrakk> CSTATE Invalid T 0; reqresps1 T = []\<rbrakk> \<Longrightarrow> \<not>GReader T 0"
  unfolding GReader_def  
  by simp

lemma CSTATEInvalid_reqrespsEmpty_nonReader2: shows "\<lbrakk> CSTATE Invalid T 1; reqresps2 T = []\<rbrakk> \<Longrightarrow> \<not>GReader T 1"
  unfolding GReader_def  
  by simp  

lemma Lexists_nonempty_reqresps1_empty: shows "reqresps1 T = [] \<Longrightarrow>\<not> Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Reader (CoherenceProperties.getGrantedState m)) "
  apply(induct "reqresps1 T")
   apply simp+
  done

lemma Lexists_nonempty_reqresps2_empty: shows "reqresps2 T = [] \<Longrightarrow>\<not> Lexists_nonEmpty (reqresps2 T) (\<lambda>m. Reader (CoherenceProperties.getGrantedState m)) "
  apply(induct "reqresps2 T")
   apply simp+
  done

lemma nextGOPendingState_GOwner: shows "nextGOPendingState Modified T i \<Longrightarrow> GOwner T i"
  unfolding GOwner_def
  apply(case_tac i)
   apply(case_tac "reqresps1 T")
    apply simp+
  apply(case_tac "reqresps2 T")
   apply simp+
  done

lemma CSTATE_IMD_GOwner_general: shows "CSTATE IMD T i \<Longrightarrow> GOwner T i"
  apply(case_tac i)
  apply simp
  apply(case_tac nat)
   apply simp+
  done
  


lemma GOwner_requestorAlmostGotOwnership_invariant: shows "requestorAlmostGotOwnership T i \<Longrightarrow> GOwner T i"
  unfolding requestorAlmostGotOwnership_def
  apply(case_tac "CSTATE IMAD T i")
   apply(subgoal_tac "nextGOPendingState Modified T i")
  using nextGOPendingState_GOwner apply presburger 
  oops

lemma IMADData_ModifiedM_aux: shows " reqresps1 T = reqresps1 ( T [ 0 s= IMA] [ 0 :=dd getHTDDataOrMakeup T 0] [ 0 -=devd ])" 
  by simp


  






lemma GOwner_partial_invariant1: shows "Owner (CLEntry.block_state (devcache1 T)) = Owner (CLEntry.block_state (devcache1 (T [1 s= X])))"
  by simp

lemma GOwner_partial_invariant1_rev: shows "Owner (CLEntry.block_state (devcache2 T)) = Owner (CLEntry.block_state (devcache2 (T [0 s= X])))"
  by simp

lemma GOwner_partial_invariant2: shows "Lexists_nonEmpty (reqresps1 T) (\<lambda>m. Owner (CoherenceProperties.getGrantedState m)) = 
  Lexists_nonEmpty (reqresps1 (T [i s= X])) (\<lambda>m. Owner (CoherenceProperties.getGrantedState m))"
  by (simp add: DeviceID.simps(4))

lemma GOwner_partial_invariant2_rev: shows "Lexists_nonEmpty (reqresps2 T) (\<lambda>m. Owner (CoherenceProperties.getGrantedState m)) = 
  Lexists_nonEmpty (reqresps2 (T [i s= X])) (\<lambda>m. Owner (CoherenceProperties.getGrantedState m))"
  by (simp add: DeviceID.simps(4))

\<comment>\<open>SharedSnpInv inspired basic properties\<close>
lemma snpRespInflight_invariant1: shows "
  snprespInflight X (   T\<lparr>buffer1 := Some m\<rparr>) i =
  snprespInflight X T i"
  by simp

lemma snpRespInflight_invariant2: shows "
snprespInflight X (   T[0 +=snpresp X tid]) 0"
  apply simp
  thm snprespInflight_def
  apply(induct "snpresps1 T")
  apply simp
  by (simp add: Lexists_nonEmpty_concat)

lemma snpRespInflight_invariant3: shows "
snprespInflight X T 0 = snprespInflight X (   T [0 -=snp ] ) 0"
  by simp


lemma snpRespInflight_invariant4: shows "
snprespInflight X T 0 = snprespInflight X (   T [ Dev1 +=d2hd dthd]) 0"
  apply simp
  done

lemma snpRespInflight_invariant5: shows "
snprespInflight X T 0 = snprespInflight X (   T  [ 0 s= Invalid] ) 0"
  by simp

lemma ModifiedSnpInv'_htddatas2_aux1: shows "htddatas2 (   T\<lparr>buffer1 := Some m\<rparr> ) =
  htddatas2 T  "
  by simp


lemma ModifiedSnpInv'_htddatas2_aux2: shows "htddatas2 (   T [0 +=snpresp RspIHitSE tid] ) =
  htddatas2 T  "
  by simp

lemma ModifiedSnpInv'_htddatas2_aux3: shows "htddatas2 (   T [0 -=snp ] ) =
  htddatas2 T  "
  by simp

lemma ModifiedSnpInv'_htddatas2_aux4: shows "htddatas2 (   T [ 0 s= Invalid]) =
  htddatas2 T  "
  by simp



lemma SharedSnpInv'_MAD_CSTATE_invariant: shows " CSTATE X (   T\<lparr>buffer1 := Some m\<rparr>) i = CSTATE X T i"
  by simp

lemma SharedSnpInv'_MAD_CSTATE_invariant2: shows " CSTATE X ( T [j +=snpresp snprespt tid]) i = CSTATE X T i"
  apply(case_tac i)
   apply(case_tac j)
  apply simp+
  apply(case_tac j)
   apply simp+
  done



lemma SharedSnpInv'_MAD_CSTATE_invariant3: shows " CSTATE X ( T [j -=snp  ]) i = CSTATE X T i"
  using CSTATE_def cache_state_invariant(1) cache_state_invariant(2) by presburger

lemma SharedSnpInv'_MAD_CSTATE_invariant4: shows " CSTATE X ( T [0 s= Z ]) 1 = CSTATE X T 1"
  using CSTATE_other_general2 by blast

lemma SharedSnpInv'_MAD_CSTATE_invariant5: shows " CSTATE X ( T [ devi +=d2hd msg  ]) i = CSTATE X T i"
    apply(case_tac i)
   apply(case_tac devi)
  apply simp+
  apply(case_tac devi)
   apply simp+
  done


lemma SharedSnpInv'_MAD_aux2_snoopNotInflight_invariant1: shows 
  "snoopNotInflight (   T [ i s= X]) j = snoopNotInflight T j"
  by simp

lemma snoopNotInflight_empty: shows "snoopNotInflight T 0 \<Longrightarrow> snps1 T = []"
  by simp

lemma snoopNotInflight_empty2: shows "snoopNotInflight T 1 \<Longrightarrow> snps2 T = []"
  by simp

lemma SharedSnpInv'_MAD_aux3_dthdataInflight1: shows "  dthdataInflight (   T [ Dev1 +=d2hd dthd]) 0 "
  unfolding dthdataInflight_def config_differ_dthdata_def
  apply(induct "dthdatas1 T")
  by simp+

lemma SharedSnpInv'_MAD_aux3_dthdataInflight1_2: shows "  dthdataInflight (   T [ Dev2 +=d2hd dthd]) 1 "
  unfolding dthdataInflight_def config_differ_dthdata_def
  by simp

lemma SharedSnpInv'_MAD_aux3_dthdataInflight2: shows "  dthdataInflight (   T\<lparr>buffer1 := Some m\<rparr> ) i = dthdataInflight T i "
  by simp

lemma SharedSnpInv'_MAD_aux3_dthdataInflight2_2: shows "  dthdataInflight (   T\<lparr>buffer2 := Some m\<rparr> ) i = dthdataInflight T i "
  by simp

lemma SharedSnpInv'_MAD_aux3_dthdataInflight3: shows " dthdataInflight (   T [i +=snpresp X tid] ) j = dthdataInflight T j "
  apply(case_tac i)
   apply(case_tac j)
  by simp+


lemma SharedSnpInv'_MAD_aux3_dthdataInflight4: shows "
  dthdataInflight (   T [i -=snp ]) j = dthdataInflight T j "
  apply(case_tac i)
  apply(case_tac j)
  by simp+

lemma SharedSnpInv'_MAD_aux3_dthdataInflight5: shows "
  dthdataInflight (   T[ i s= Invalid] ) j = dthdataInflight T j "
  by simp



lemma SharedSnpInv'_CSTATE_invariant5: shows "CSTATE X (T [0 s= X]) 0"
  by simp

lemma SharedSnpInv'_CSTATE_invariant5_2: shows "CSTATE X (T [1 s= X]) 1"
  by simp

lemma SharedSnpInv'_MAD_snps1_length: shows "length (snps1 T) = length (snps1 (T\<lparr>buffer1 := Some m\<rparr> [j +=snpresp X tid] ))"
  apply(case_tac j)
  by simp+

lemma SharedSnpInv'_MAD_snps1_length_2: shows "length (snps2 T) = length (snps2 (T\<lparr>buffer2 := Some m\<rparr> [j +=snpresp X tid] ))"
  apply(case_tac j)
  by simp+


lemma SharedSnpInv'_MAD_aux2_snoopNotInflight: shows "length (snps1 T) \<le> 1 \<Longrightarrow> snoopNotInflight (   T [0 -=snp ]) 0"
    apply(induct "snps1 T")
  apply simp
  apply(case_tac x)
  unfolding snoopNotInflight_def
   apply simp
  apply (metis list.simps(5))
  apply simp
  by (metis bot_nat_0.extremum length_Cons not_less_eq_eq)

lemma SharedSnpInv'_MAD_aux2_snoopNotInflight_2: shows "length (snps2 T) \<le> 1 \<Longrightarrow> snoopNotInflight (   T [1 -=snp ]) 1"
    apply(induct "snps2 T")
  apply simp
  apply(case_tac x)
  unfolding snoopNotInflight_def
   apply simp
  apply (metis list.simps(5))
  apply simp
  by (metis bot_nat_0.extremum length_Cons not_less_eq_eq)

lemma SharedSnpInv'_snpresps1_invariant1: shows "snpresps1 (T\<lparr>buffer1 := Some m\<rparr> ) = snpresps1 T"
  by simp

lemma SharedSnpInv'_snpresps1_invariant1_2: shows "snpresps2 (T\<lparr>buffer2 := Some m\<rparr> ) = snpresps2 T"
  by simp

\<comment>\<open>No dual done from here\<close>
lemma SharedSnpInv'_snpresps1_invariant2: shows "snpresps1 (T [i -=snp ]) = snpresps1 T"
  apply(case_tac i)
  by simp+

lemma SharedSnpInv'_snpresps1_invariant3: shows "snpresps1 T = [] \<Longrightarrow> length (snpresps1 (T [0 +=snpresp X tid])) \<le> 1"
  by simp

lemma SharedSnpInv'_snpresps1_invariant4: shows "length (snpresps1 (T  [i -=snp ] )) = 
  length (snpresps1 T)"
  apply(case_tac i)
  by simp+

lemma SharedSnpInv'_snpresps1_invariant5: shows "length (snpresps1 (T   [ i s= X])) = 
  length (snpresps1 T)"
  by simp 

lemma SharedSnpInv'_snpresps1_invariant6: shows "length (snpresps1 (T  [ devi +=d2hd dthd])) = 
  length (snpresps1 T)"
  apply(case_tac devi)
  by simp+


lemma ModifiedSnpInv'_htddatas2: shows "htddatas2 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) = htddatas2 T"
  by simp


lemma ModifiedSnpInv'_CSTATE: shows "
  CSTATE X (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp RspIHitSE tid] [0 -=snp ] [ 0 s= Invalid]) 1 = CSTATE X T 1"
  by simp

\<comment>\<open>
lemma snpRespCState_invariant: shows "\<lbrakk>X \<noteq> Y; nextSnpRespIs Y i T \<rbrakk> \<Longrightarrow> \<not>nextSnpRespIs X i T"
  apply(case_tac i)
   apply simp
  using startsWithProp.elims(2) apply fastforce
  apply simp
  using startsWithProp.elims(2) by fastforce

lemma snpRespCState_invariant_clauses1: shows "\<lbrakk>nextSnpRespIs RspIHitSE i T; CSTATE Invalid T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses2: shows "\<lbrakk>nextSnpRespIs RspSFwdM i T; CSTATE Shared T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses3: shows "\<lbrakk>nextSnpRespIs RspIHitSE i T; CSTATE Invalid T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses4: shows "\<lbrakk>nextSnpRespIs RspIHitI i T; CSTATE Invalid T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses5: shows "\<lbrakk>nextSnpRespIs RspSHitSE i T; CSTATE Shared T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses6: shows "\<lbrakk>nextSnpRespIs RspVFwdV i T;\<not> CSTATE Invalid T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_clauses7: shows "\<lbrakk>nextSnpRespIs RspVHitV i T; \<not>CSTATE Invalid T i\<rbrakk> \<Longrightarrow> snpRespCState T i"
  using snpRespCState_def snpRespCState_invariant by blast

lemma snpRespCState_invariant_irrelevant0: shows "snpRespCState (   T\<lparr>buffer1 := Some m\<rparr>) 1 = snpRespCState T 1"
  by simp

lemma snpRespCState_invariant_irrelevant1: shows "snpRespCState (   T [0 +=snpresp RspIHitSE tid] ) 1 = snpRespCState T 1"
  by simp


lemma snpRespCState_invariant_irrelevant2: shows "snpRespCState (   T [0 -=snp ] ) 1 = snpRespCState T 1"
  by simp

lemma snpRespCState_invariant_irrelevant3: shows "snpRespCState (   T [ 0 s= Invalid] ) 1 = snpRespCState T 1"
  by simp

lemma snpRespCState_invariant_irrelevant4: shows "snpRespCState (   T[ Dev1 +=d2hd dthd]) 1 = snpRespCState T 1"
  by simp

lemma SharedSnpInv'_nextSnpRespIs_invariant1: shows 
  "nextSnpRespIs X i (   T) = 
   nextSnpRespIs X i (   T\<lparr>buffer1 := Some m\<rparr> )"
  by simp

lemma SharedSnpInv'_nextSnpRespIs_invariant2: shows 
  "snpresps1 T = [] \<Longrightarrow> nextSnpRespIs X 0 (   T  [0 +=snpresp X tid]) "
  by simp


lemma SharedSnpInv'_nextSnpRespIs_invariant3: shows 
  "nextSnpRespIs RspIHitSE i (   T) = 
   nextSnpRespIs RspIHitSE i (   T [ 0 s= Invalid]  )"
  by simp

lemma SharedSnpInv'_nextSnpRespIs_invariant4: shows 
  "nextSnpRespIs RspIHitSE i (   T) = 
   nextSnpRespIs RspIHitSE i (   T [ Dev1 +=d2hd dthd] )"
  by simp

lemma SharedSnpInv'_nextSnpRespIs_invariant5: shows 
  "nextSnpRespIs RspIHitSE i (   T) = 
   nextSnpRespIs RspIHitSE i (   T [ j -=snp ] )"
  by (simp add: Nitpick.case_nat_unfold)

lemma SharedSnpInv'_nextSnpRespIs_invariant6: shows 
  "snpresps1 T = [] \<Longrightarrow> nextSnpRespIs X 0 (   T\<lparr>buffer1 := Some m\<rparr> [0 +=snpresp X tid]) "
  by simp
\<close>

lemma SharedSnpInv'_dthdatas1: shows 
  "dthdatas1 T = [] \<Longrightarrow> length (dthdatas1 (   T [ Dev1 +=d2hd dthd])) \<le> 1 "
  by simp

lemma SharedSnpInv'_dthdatas2: shows 
  "dthdatas2 T = [] \<Longrightarrow> length (dthdatas2 (   T [ Dev2 +=d2hd dthd])) \<le> 1 "
  by simp
\<comment>\<open>SharedSnpInv inspired basic properties end\<close>



lemma empty_no_snoop: shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopIs X T 0"
  by simp

lemma empty_no_snoop2: "snps2 T = [] \<Longrightarrow> \<not> nextSnoopIs X T 1"
  by simp


lemma empty_no_snoop_variant: shows "snps1 T = [] \<Longrightarrow> \<forall>X. \<not> nextSnoopIs X T 0"
  by simp

lemma empty_no_snoop_variant2: "snps2 T = [] \<Longrightarrow> \<forall>X. \<not> nextSnoopIs X T 1"
  by simp

lemma device_perform_op_snps2:   " snps2  T  = snps2  (T [ :=i m])"
   apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma device_perform_op_snps1:   " snps1  T  = snps1  (T [ :=i m])"
   apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma device_perform_op_reqs1:   " reqs1  T  = reqs1  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+
  

lemma device_perform_op_reqs2:   " reqs2  T  = reqs2  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma device_perform_op_reqresps1:   " reqresps1  T  = reqresps1  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+
  
lemma device_perform_op_reqresps2:   " reqresps2  T  = reqresps2  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+


lemma device_perform_op_snpresps1:   " snpresps1  T  = snpresps1  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+
  
lemma device_perform_op_snpresps2:   " snpresps2  T  = snpresps2  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma device_perform_op_dthdatas1:   " dthdatas1  T  = dthdatas1  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+
  
lemma device_perform_op_dthdatas2:   " dthdatas2  T  = dthdatas2  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma device_perform_op_htddatas1:   " htddatas1  T  = htddatas1  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+
  
lemma device_perform_op_htddatas2:   " htddatas2  T  = htddatas2  (T [ :=i m])"
     apply(case_tac m)
    apply (cases "program1 T")
    apply simp
   apply simp
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
      apply simp+
      apply (cases "program2 T")
    apply simp+
   apply(case_tac a)
     apply simp+
    apply(case_tac x2)
     apply simp
  apply(case_tac n)
  by simp+

lemma reqlength1_minus: shows "length (reqs1 T) \<le> 1 \<Longrightarrow> reqs1 (T [ 0 -=req]) = []"
  apply(cases "reqs1 T")
   apply simp+
  done

\<comment>\<open>about perform_op (:=i)\<close>




lemma nextLoad_ModifiedStore: shows "nextLoad T 1 = nextLoad  (T [ :=i 0]) 1"
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
      apply(case_tac n)
       apply simp+
  done


lemma device_perform_op_nextReqIs: shows "nextReqIs X T j = nextReqIs X (T [ :=i m]) j"
  apply(case_tac j)
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
      apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  done


lemma device_perform_op_nextGOPending_aux:   "m > 0 \<Longrightarrow> nextGOPending T j = nextGOPending (T [ :=i m]) j"
  apply (cases "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac j)
    apply(case_tac x2)
  apply(case_tac n)
  apply simp+
    apply(case_tac x2)
    apply(case_tac n)
     apply simp+
  done



lemma device_perform_op_nextGOPending: "nextGOPending T j = nextGOPending (T [ :=i m]) j"
  apply(case_tac j)
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
      apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  done


lemma device_perform_op_nextHTDDataPending:   " nextHTDDataPending T j = nextHTDDataPending (T [ :=i m]) j"
    apply(case_tac j)
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
      apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  done

lemma device_perform_op_nextDTHDataPending:   " nextDTHDataPending T j = nextDTHDataPending (T [ :=i m]) j"
  apply(case_tac j)
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
      apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  apply(case_tac m)
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
       apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp+
  done

lemma device_perform_op_SnpRespIs:   " nextSnpRespIs X T j = nextSnpRespIs  X (T [ :=i m]) j"
  apply(case_tac m)
    apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)

      apply simp+
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)

  apply simp+
  done




lemma device_perform_op_nextGOPendingIs:   " nextGOPendingIs X T j = nextGOPendingIs  X (T [ :=i m]) j"
  apply(case_tac j)
  apply(case_tac m)
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
  apply(case_tac "program2 T")
    apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
      apply simp
  apply simp
  apply simp
   apply simp
  apply(case_tac m)
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
  apply(case_tac "program2 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)
  apply simp+
  done



lemma device_perform_op_nextEvict:   " nextGOPendingIs X T j = nextGOPendingIs  X (T [ :=i m]) j"
  
  using device_perform_op_nextGOPendingIs by blast



  
lemma ModifiedStore_nextReqIs: shows "nextReqIs x (T [ :=i 0]) 1 = nextReqIs x T 1"
  
  using device_perform_op_nextReqIs by presburger

lemma ModifiedStore_nextEvict: shows "nextEvict (T [ :=i 0]) 1 = nextEvict  T 1"
  apply(case_tac "program1 T")
   apply simp
  apply(case_tac a)
    apply simp
   apply(case_tac x2)
  apply(case_tac n)

  apply simp+
  done


lemma remove_instr_HSTATE: shows "HSTATE M T = HSTATE M (T [ -=i j])"
  apply(case_tac j)
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
   apply(case_tac "program2 T")
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



lemma nextGOPending_DeviceModifiedStore: "nextGOPending ( T [ -=i 0] ) i = nextGOPending T i"
  apply(case_tac i)
   apply(case_tac "program1 T")
    apply simp
  apply(case_tac a)
     apply simp+
   apply(case_tac "program1 T")
    apply simp+
  done




lemma CSTATE_remove_op: shows "CSTATE X T i = CSTATE X (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done

lemma nextGOPendingIs_remove_op: shows "nextGOPendingIs X T i = nextGOPendingIs X (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done

lemma nextDTHDataPending_remove_op: shows "nextDTHDataPending  T i = nextDTHDataPending (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done


lemma nextHTDDataPending_remove_op: shows "nextHTDDataPending  T i = nextHTDDataPending (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done

lemma nextReqIs_remove_op: shows "nextReqIs X  T i = nextReqIs X (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done



lemma nextSnpRespIs_remove_op: shows "nextSnpRespIs X  T i = nextSnpRespIs X (T [ -=i j]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
   apply simp
  apply(case_tac j)
    apply(case_tac "program1 T")
     apply simp
  apply simp
    apply(case_tac "program2 T")
     apply simp
  apply simp
  done






lemma nextStore_remove_op: shows "nextStore   T 1 = nextStore  (T [ -=i 0]) 1"
    apply(case_tac "program1 T")
  by simp+


lemma nextStore_remove_op_rev: shows "nextStore   T 0 = nextStore  (T [ -=i 1]) 0"
    apply(case_tac "program2 T")
  by simp+


lemma snps1_remove_op: shows "snps1   T  = snps1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma snps2_remove_op: shows "snps2   T  = snps2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma reqs1_remove_op: shows "reqs1   T  = reqs1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma reqs2_remove_op: shows "reqs2   T  = reqs2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma reqresps1_remove_op: shows "reqresps1   T  = reqresps1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma reqresps2_remove_op: shows "reqresps2   T  = reqresps2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+


lemma snpresps1_remove_op: shows "snpresps1   T  = snpresps1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma snpresps2_remove_op: shows "snpresps2   T  = snpresps2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma dthdatas1_remove_op: shows "dthdatas1   T  = dthdatas1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma dthdatas2_remove_op: shows "dthdatas2   T  = dthdatas2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma htddatas1_remove_op: shows "htddatas1   T  = htddatas1  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+

lemma htddatas2_remove_op: shows "htddatas2   T  = htddatas2  (T [ -=i 0]) "
    apply(case_tac "program1 T")
  by simp+


lemma nextGOPendingIs_invariant1: shows "\<not> nextGOPendingIs X T i \<Longrightarrow> X \<noteq> Y \<Longrightarrow> \<not> nextGOPendingIs X ( T [ j +=reqresp Y txid z]) i"
  apply(case_tac i)
   apply(case_tac j)
    apply(case_tac "reqresps1 T")
     apply simp
    apply simp
   apply simp
  apply(case_tac j)
   apply simp
  apply(case_tac "reqresps2 T")
   apply simp
  apply simp
  done

lemma HSTATE_invariant3: shows "\<lbrakk> HSTATE X T \<or> HSTATE Y T \<or> HSTATE Z T; W \<noteq> X; W \<noteq> Y; W \<noteq> Z \<rbrakk> \<Longrightarrow> \<not> HSTATE W T"
  by force

lemma HSTATE_invariant4: shows "\<lbrakk> HSTATE X T \<or> HSTATE Y T \<or> HSTATE Z T \<or> HSTATE U T; W \<noteq> X; W \<noteq> Y; W \<noteq> Z; W \<noteq> U \<rbrakk> \<Longrightarrow> \<not> HSTATE W T"
  by force

lemma nextSnpRespIs_invariant1: shows "snpresps1 T = [] \<Longrightarrow> nextSnpRespIs X T 0 = False"

  using nextSnpRespIs_property1 by blast

lemma nextSnpRespIs_invariant2: shows "snpresps2 T = [] \<Longrightarrow> nextSnpRespIs X T 1 = False"

  using nextSnpRespIs_property2 by blast

lemma CSTATE_inequality_invariant: shows "CSTATE X T i \<Longrightarrow> X \<noteq> Y  \<Longrightarrow> \<not> CSTATE Y T i"
  apply simp
  done

lemma nextReqIs_invariant: "X \<noteq> Y \<Longrightarrow> nextReqIs X T i \<Longrightarrow> \<not> nextReqIs Y T i"
  apply(case_tac i)
   apply(case_tac "reqs1 T")
    apply simp
  apply simp
  apply(case_tac "reqs2 T")
  by simp+

lemma nextReqIs_invariant_variant1: "nextReqIs X T i \<and> X \<noteq> Y \<Longrightarrow> \<not> nextReqIs Y T i"
  by (metis nextReqIs_invariant)

lemma CSTATE_various_forms1: "CSTATE X T 0 \<Longrightarrow> CLEntry.block_state (devcache1 T) = X"
  by simp

lemma CSTATE_various_forms2: "CLEntry.block_state (devcache1 T) = X \<Longrightarrow> CSTATE X T 0"
  by simp

lemma CSTATE_various_forms3: "CSTATE X T 1 \<Longrightarrow> CLEntry.block_state (devcache2 T) = X"
  by simp

lemma CSTATE_various_forms4: "CLEntry.block_state (devcache2 T) = X \<Longrightarrow> CSTATE X T 1"
  by simp

lemma CSTATE_various_forms5: "\<not> CSTATE X T 1 = (CLEntry.block_state (devcache2 T) \<noteq> X)"
  by simp

lemma CSTATE_various_forms6: "(CLEntry.block_state (devcache2 T) = X) = CSTATE X T 1"
  by simp


lemma HSTATE_various_forms1: "HSTATE X T \<Longrightarrow> HostEntry.block_state (hostcache T) = X"
  by simp

lemma HSTATE_various_forms2: "HostEntry.block_state (hostcache T) = X \<Longrightarrow> HSTATE X T"
  by simp

lemma nextGOPending_various_forms1: "nextGOPending T 0 \<Longrightarrow> nextReqRespIs GO (reqresps1 T)"
  by simp

lemma nextGOPending_various_forms2: "nextReqRespIs GO (reqresps1 T) \<Longrightarrow> nextGOPending T 0"
  by simp

lemma nextGOPending_various_forms3: "nextGOPending T 1 \<Longrightarrow> nextReqRespIs GO (reqresps2 T)"
  by simp

lemma nextGOPending_various_forms4: "nextReqRespIs GO (reqresps2 T) \<Longrightarrow> nextGOPending T 1"
  by simp

lemma nextGOPending_various_forms5: "nextGOPending T 0 = nextReqRespIs GO (reqresps1 T)"
  by simp

lemma nextGOPending_various_forms6: "nextGOPending T 1 = nextReqRespIs GO (reqresps2 T)"
  by simp

lemma nextGOPendingIs_various_forms1: "nextGOPendingIs X T 0 \<Longrightarrow> nextReqRespIs X (reqresps1 T)"
  by simp


lemma nextGOPendingIs_various_forms2: "nextReqRespIs X (reqresps1 T) \<Longrightarrow> nextGOPendingIs X T 0"
  by simp

lemma nextGOPendingIs_various_forms3: "nextGOPendingIs X T 1 \<Longrightarrow> nextReqRespIs X (reqresps2 T)"
  by simp

lemma nextGOPendingIs_various_forms4: "nextReqRespIs X (reqresps2 T) \<Longrightarrow> nextGOPendingIs X T 1"
  by simp

lemma nextGOPendingIs_various_forms5: "nextGOPendingIs X (T [ 0 +=reqresp Y mesi txid]) 0 =
 nextReqRespIs X (reqresps1 T @ [H2DResp txid Y mesi (clock T)])"
  by simp

lemma nextGOPendingIs_various_forms6: "nextGOPendingIs X (T [ 1 +=reqresp Y mesi txid]) 1 =
 nextReqRespIs X (reqresps2 T @ [H2DResp txid Y mesi (clock T)])"
  by simp



lemma nextHTDDataPending_various_forms1: "(nextHTDDataPending T 0) = (htddatas1 T \<noteq> [])"
  by simp

lemma nextHTDDataPending_various_forms2: "(nextHTDDataPending T 1) = (htddatas2 T \<noteq> [])"
  by simp


lemma nextReqIs_various_forms1: "startsWithProp X (reqs1 T) (case_Message (\<lambda>tid reqtype t. reqtype) (\<lambda>TransactionID SnpRespType nat. ReqMadeup)
        (\<lambda>TransactionID int nat. ReqMadeup) (\<lambda>TransactionID SnoopType nat. ReqMadeup)
        (\<lambda>TransactionID ReqRespType MESI_State nat. ReqMadeup) (\<lambda>TransactionID int nat. ReqMadeup)) = (nextReqIs X T 0)"
  by simp

lemma nextReqIs_various_forms2: "startsWithProp X (reqs2 T) (case_Message (\<lambda>tid reqtype t. reqtype) (\<lambda>TransactionID SnpRespType nat. ReqMadeup)
        (\<lambda>TransactionID int nat. ReqMadeup) (\<lambda>TransactionID SnoopType nat. ReqMadeup)
        (\<lambda>TransactionID ReqRespType MESI_State nat. ReqMadeup) (\<lambda>TransactionID int nat. ReqMadeup)) = (nextReqIs X T 1)"
  by simp

lemma nextSnpRespIs_various_forms1: "startsWithProp X (snpresps1 T)
         (\<lambda>resp. case resp of D2HResp tid reqresptype t \<Rightarrow> reqresptype | _ \<Rightarrow> SnpRespMadeup) = nextSnpRespIs X T 0"
  by simp

lemma nextSnpRespIs_various_forms2: "startsWithProp X (snpresps2 T)
         (\<lambda>resp. case resp of D2HResp tid reqresptype t \<Rightarrow> reqresptype | _ \<Rightarrow> SnpRespMadeup) = nextSnpRespIs X T 1"
  by simp

lemma nextReqIs_not_various_forms1: "reqs1 T = [] \<Longrightarrow> \<not> nextReqIs X T 0"
  by simp

lemma nextReqIs_not_various_forms2: "reqs2 T = [] \<Longrightarrow> \<not> nextReqIs X T 1"
  by simp

lemma nextGOPending_reqresps2_invariants1: "reqresps2 T = [] \<Longrightarrow> nextReqRespIs GO (reqresps2 T @ [H2DResp txid GO X t])"
  by simp

lemma nextGOPending_reqresps1_invariants1: "reqresps1 T = [] \<Longrightarrow> nextReqRespIs GO (reqresps1 T @ [H2DResp txid GO X t])"
  by simp

lemma nextReqIs_various_forms3: "(startsWithProp X (reqs1 T)
        (\<lambda>req. case req of D2HReq tid reqtype t \<Rightarrow> reqtype | _ \<Rightarrow> ReqMadeup)) = nextReqIs X T 0"
  by simp

lemma nextReqIs_various_forms4: "(startsWithProp X (reqs2 T)
        (\<lambda>req. case req of D2HReq tid reqtype t \<Rightarrow> reqtype | _ \<Rightarrow> ReqMadeup)) = nextReqIs X T 1"
  by simp

lemma minus_snpresps_various_forms1: "nextSnpRespIs X (T [ 0 -=snpresp  ]) 0 = 
startsWithProp X   (case (snpresps1 T) of [] \<Rightarrow> [] | 
(msg # tail) \<Rightarrow> tail) (\<lambda>resp. case resp of D2HResp tid reqresptype t \<Rightarrow> reqresptype | _ \<Rightarrow> SnpRespMadeup)"
  by simp

lemma minus_snpresps_various_forms2: "nextSnpRespIs X (T [ 1 -=snpresp  ]) 1 = 
startsWithProp X   (case (snpresps2 T) of [] \<Rightarrow> [] | 
(msg # tail) \<Rightarrow> tail) (\<lambda>resp. case resp of D2HResp tid reqresptype t \<Rightarrow> reqresptype | _ \<Rightarrow> SnpRespMadeup)"
  by simp

lemma nextEvict_various_forms1: "nextEvict T 0 = startsEvict (program1 T)"
  by simp
lemma nextEvict_various_forms2: "nextEvict T 1 = startsEvict (program2 T)"
  by simp

lemma CSTATE_disj1: assumes "CSTATE X T i  "
"U \<noteq> X"   shows "\<not> CSTATE U T i"
  apply(insert assms)  
  using CSTATE_inequality_invariant by blast

lemma CSTATE_disj2: assumes "CSTATE X T i \<or> CSTATE Y T i  "
"U \<noteq> X" "U \<noteq> Y"  shows "\<not> CSTATE U T i"
  apply(insert assms)  
  using CSTATE_inequality_invariant by blast

lemma CSTATE_disj3: assumes "CSTATE X T i \<or> CSTATE Y T i \<or> CSTATE Z T i  "
"U \<noteq> X" "U \<noteq> Y" "U \<noteq> Z" shows "\<not> CSTATE U T i"
  apply(insert assms)  
  using CSTATE_inequality_invariant by blast

lemma CSTATE_disj4: assumes "CSTATE X T i \<or> CSTATE Y T i \<or> CSTATE Z T i \<or> CSTATE W T i "
"U \<noteq> X" "U \<noteq> Y" "U \<noteq> Z" "U \<noteq> W" shows "\<not> CSTATE U T i"
  apply(insert assms)  
  using CSTATE_inequality_invariant by blast

lemma CSTATE_disj4': shows "\<lbrakk> CSTATE X T i \<or> CSTATE Y T i \<or> CSTATE Z T i \<or> CSTATE W T i;U \<noteq> X;
  U \<noteq> Y; U \<noteq> Z; U \<noteq> W \<rbrakk> \<Longrightarrow> \<not> CSTATE U T i"  
  using CSTATE_inequality_invariant by blast

lemma nextEvict_different_side_minus_op1: "nextEvict (T [ -=i 0]) 1 = nextEvict T 1"
  apply(case_tac "program1 T")
  by simp+


lemma nextEvict_different_side_minus_op2: "nextEvict (T [ -=i 1]) 0 = nextEvict T 0"
  apply(case_tac "program2 T")
  by simp+

lemma nextLoad_different_side_minus_op1: "nextLoad (T [ -=i 0]) 1 = nextLoad T 1"
  apply(case_tac "program1 T")
  by simp+


lemma nextLoad_different_side_minus_op2: "nextLoad (T [ -=i 1]) 0 = nextLoad T 0"
  apply(case_tac "program2 T")
  by simp+

lemma nextStore_different_side_minus_op1: "nextStore (T [ -=i 0]) 1 = nextStore T 1"
  apply(case_tac "program1 T")
  by simp+


lemma nextStore_different_side_minus_op2: "nextStore (T [ -=i 1]) 0 = nextStore T 0"
  apply(case_tac "program2 T")
  by simp+

lemma minus_op_invariant1: shows "CSTATE X (T [ -=i 0]) i = CSTATE X T i"
  apply(case_tac i)  
  apply (metis CSTATE_remove_op)  
  by (metis CSTATE_remove_op)

\<comment>\<open>needs flipped version for device 2\<close>
lemma HostShared_CleanEvictNoData_NotLast_preamble1: shows "reqresps1 T = [] \<Longrightarrow> nextReqRespStateIs Invalid (reqresps1 ( T [ 5 sHost= x] [ 0 +=reqresp GO Invalid txid] [ i -=req ]))"
  by simp

lemma nextGOInvalid_HostShared_CleanEvict_Last: "reqresps1 T = [] \<Longrightarrow> nextReqRespStateIs Invalid (reqresps1 ( T [ 5 sHost= x] [ 0 +=reqresp y Invalid txid] [ i -=req ]))"
  by simp

lemma reqresps_empty_noGOPendingIs1: "reqresps1 T = [] \<Longrightarrow> \<not> nextGOPendingIs X T 0"
  by simp

lemma reqresps_empty_noGOPendingIs2: "reqresps2 T = [] \<Longrightarrow> \<not> nextGOPendingIs X T 1"
  by simp


lemma reqresps_empty_noGOPending1: "reqresps1 T = [] \<Longrightarrow> \<not> nextGOPending T 0"
  by simp

lemma reqresps_empty_noGOPending2: "reqresps2 T = [] \<Longrightarrow> \<not> nextGOPending T 1"
  by simp


lemma C_msg_not_reqs_empty1: "reqs1 T = [] \<and> reqs2 T = [] \<Longrightarrow> C_msg_not X s T"
apply(cases X)
by simp+

lemma C_msg_not_remove_reqs1: "length (reqs1 T) \<le> 1 \<and> C_msg_not X s T \<Longrightarrow> C_msg_not X s (T [0 -=req ])"
apply(cases "reqs1 T")
by simp+

lemma C_msg_not_remove_reqs2: "length (reqs2 T) \<le> 1 \<and> C_msg_not X s T \<Longrightarrow> C_msg_not X s (T [1 -=req ])"
apply(cases "reqs2 T")
  by simp+

lemma reqs1_invariant_hstate_reqresps1: "reqs1 (T [ 5 sHost= x] [ 0 +=reqresp t y txid]) = reqs1 T"
  by simp

lemma nextSnoopIs_invariant: "X \<noteq> Y \<Longrightarrow> nextSnoopIs X T i \<Longrightarrow> \<not> nextSnoopIs Y T i"
  apply(case_tac i)
   apply(case_tac "snps1 T")
    apply simp
  apply simp
  apply(case_tac "snps2 T")
   apply simp
  apply simp 
  by (metis getSnoopType_def startsSnp.simps(2))

lemma nextSnoopIs_invariant_variant1: "X \<noteq> Y \<and> nextSnoopIs X T i \<Longrightarrow> \<not> nextSnoopIs Y T i"
  apply(case_tac i)
   apply(case_tac "snps1 T")
    apply simp
  apply simp
  apply(case_tac "snps2 T")
   apply simp
  apply simp 
  by (metis getSnoopType_def startsSnp.simps(2))

lemma nextSnpRespIs_invariant: "X \<noteq> Y \<Longrightarrow> nextSnpRespIs X T i \<Longrightarrow> \<not> nextSnpRespIs Y T i"
  apply(case_tac i)
   apply(case_tac "snpresps1 T")
    apply simp
   apply simp
  apply(case_tac "snpresps2 T")
   apply simp+
  done

lemma nextSnpRespIs_invariant_variant1: "X \<noteq> Y \<and> nextSnpRespIs X T i \<Longrightarrow> \<not> nextSnpRespIs Y T i"
  apply(case_tac i)
   apply(case_tac "snpresps1 T")
    apply simp
   apply simp
  apply(case_tac "snpresps2 T")
   apply simp+
  done

lemma nextGOPendingIs_invariant: "X \<noteq> Y \<Longrightarrow> nextGOPendingIs X T i \<Longrightarrow> \<not> nextGOPendingIs Y T i"
  apply(case_tac i)
   apply(case_tac "reqresps1 T")
    apply simp
   apply simp
  apply(case_tac "reqresps2 T")
   apply simp+
  done

lemma C_msg_not_invariant_used_by_many1: "C_msg_not X Y T \<and> length (reqs1 T) \<le> 1 \<Longrightarrow> 
  C_msg_not X Y ( T [ i +=snp t txid] [ 5 sHost= hmesi] [ 0 -=req ])"
  unfolding C_msg_not_def
  apply(cases i)
  apply(cases "reqs1 T")
   apply simp+
  apply(cases "reqs1 T")
  by simp+
  

lemma C_msg_not_invariant_used_by_many2: "C_msg_not X Y T \<and> length (reqs2 T) \<le> 1 \<Longrightarrow> 
  C_msg_not X Y ( T [ i +=snp t txid] [ 5 sHost= hmesi] [ 1 -=req ])"
  unfolding C_msg_not_def
  apply(cases i)
  apply(cases "reqs2 T")
   apply simp+
  apply(cases "reqs2 T")
  by simp+

lemma C_msg_P_same_invariant_1: shows "C_msg_P_same X nextGOPending nextStore T = C_msg_P_same X nextGOPending nextStore (  T [ i +=snp t txid]  [ 5 sHost= hmesi] [ j -=req ])"
  apply(cases i)
  by simp+

lemma C_msg_state_invariant_1_1: shows "C_msg_state X t T \<and> length (reqs1 T) \<le> 1 \<Longrightarrow> C_msg_state X t (T [ 5 sHost= hmesi] [ i +=reqresp gtype mesi txid] [ 0 -=req ])"
  unfolding C_msg_state_def
  apply(cases i)
   apply(cases "reqs1 T")
  apply simp+
     apply(cases "reqs1 T")
  by simp+


lemma C_msg_state_invariant_1_2: shows "C_msg_state X t T \<and> length (reqs2 T) \<le> 1 \<Longrightarrow> C_msg_state X t (T [ 5 sHost= hmesi] [ i +=reqresp gtype mesi txid] [ 1 -=req ])"
  unfolding C_msg_state_def
  apply(cases i)
   apply(cases "reqs2 T")
  apply simp+
     apply(cases "reqs2 T")
  by simp+

lemma nextStore_invariant_sendingSnoops: shows "nextStore (  T [ j +=snp snpt txid]  [ k sHost= MAD] [ s -=req ]) i = nextStore T i" 
  apply(cases i)
   apply(cases j)
    apply simp
   apply simp
   apply(cases j)
    apply simp
  apply simp
  done

lemma XYRspZ_equivalence_invariant1_1: "length (snpresps1 T) \<le> 1 \<Longrightarrow> snpresps1 ( T [ i +=reqresp gtype mesi txid] [ k sHost= hmesi] [ 0 -=snpresp ] ) = []"
  apply(cases i)
   apply(cases "snpresps1 T")
    apply simp
  apply simp
  apply(cases "snpresps1 T")
  by simp+

lemma XYRspZ_equivalence_invariant1_2: "length (snpresps2 T) \<le> 1 \<Longrightarrow> snpresps2 ( T [ i +=reqresp gtype mesi txid] [ k sHost= hmesi] [ 1 -=snpresp ] ) = []"
  apply(cases i)
   apply(cases "snpresps2 T")
    apply simp
  apply simp
  apply(cases "snpresps2 T")
  by simp+

lemma XYRspZ_equivalence_invariant2_1: "length (snpresps1 T) \<le> 1 \<Longrightarrow> \<not> nextSnpRespIs X ( T [ i +=reqresp gtype mesi txid] [ k sHost= hmesi] [ 0 -=snpresp ] ) 0"
  apply(cases i)
   apply(cases "snpresps1 T")
    apply simp
  apply simp
  apply(cases "snpresps1 T")
  by simp+

lemma XYRspZ_equivalence_invariant2_2: "length (snpresps2 T) \<le> 1 \<Longrightarrow> \<not> nextSnpRespIs X ( T [ i +=reqresp gtype mesi txid] [ k sHost= hmesi] [ 1 -=snpresp ] ) 1"
  apply(cases i)
   apply(cases "snpresps2 T")
    apply simp
  apply simp
  apply(cases "snpresps2 T")
  by simp+

lemma XBData_invariant1_1: "length (dthdatas1 T) \<le> 1 \<Longrightarrow> dthdatas1  ( T [ k sHost= hmesi] [ Dev1 -=d2hdHead ]) = []"
  apply(cases "(dthdatas1 T)")
  by simp+
lemma XBData_invariant1_2: "length (dthdatas2 T) \<le> 1 \<Longrightarrow> dthdatas2  ( T [ k sHost= hmesi] [ Dev2 -=d2hdHead ]) = []"
  apply(cases "(dthdatas2 T)")
  by simp+

lemma IXADGO_dthdatas1_invariant: "dthdatas1 T = dthdatas1 ( T \<lparr>buffer1 := Some m\<rparr> [ i s= X] [ j -=reqresp ])"
  by simp

lemma IXADGO_dthdatas2_invariant: "dthdatas2 T = dthdatas2 ( T \<lparr>buffer2 := Some m\<rparr> [ i s= X] [ j -=reqresp ])"
  by simp

lemma IXDData_C_msg_P_same_invariant1: "length (htddatas1 T) \<le> 1 \<and> C_msg_P_same X (nextSnoopIs Z) (\<lambda>T i. \<not> nextHTDDataPending T i) T \<Longrightarrow> 
  C_msg_P_same X (nextSnoopIs Z) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 0 s= Y] [ 0 :=dd msg] [ -=i 0] [ 0 -=devd ])"
  unfolding C_msg_P_same_def
  apply(cases "htddatas1 T")
  apply(cases "program1 T")
    apply simp
  apply simp
  apply(cases "program1 T")
  by simp+


lemma IXDData_C_msg_P_same_invariant2: "length (htddatas2 T) \<le> 1 \<and> C_msg_P_same X (nextSnoopIs Z) (\<lambda>T i. \<not> nextHTDDataPending T i) T \<Longrightarrow> 
  C_msg_P_same X (nextSnoopIs Z) (\<lambda>T i. \<not> nextHTDDataPending T i) ( T [ 1 s= Y] [ 1 :=dd msg] [ -=i 1] [ 1 -=devd ])"
  unfolding C_msg_P_same_def
  apply(cases "htddatas2 T")
  apply(cases "program2 T")
    apply simp
  apply simp
  apply(cases "program2 T")
  by simp+

lemma HTDDataPending_htddatas_invariant1: "(htddatas1 T = []) = (\<not> nextHTDDataPending T 0)"
  by simp

lemma HTDDataPending_htddatas_invariant2: "(htddatas2 T = []) = (\<not> nextHTDDataPending T 1)"
  by simp
lemma SARspSFwdM_invariant1: shows "snpresps1 T = [] = (\<forall>X. \<not> nextSnpRespIs X T 0)"
  apply(cases "snpresps1 T")
  apply simp+
  done

lemma SARspSFwdM_invariant2: shows "snpresps2 T = [] = (\<forall>X. \<not> nextSnpRespIs X T 1)"
  apply(cases "snpresps2 T")
  apply simp+
  done

lemma CSTATE_starting_transaction_otherside_invariant1: "CSTATE X ( T [ j +=rdreq Y] [ 0 s= Z]) 1 = CSTATE X T 1"
  apply(cases j)
   apply simp+
  done

lemma CSTATE_starting_transaction_otherside_invariant2: "CSTATE X ( T [ j +=rdreq Y] [ 1 s= Z]) 0 = CSTATE X T 0"
  apply(cases j)
   apply simp+
  done

lemma dthdatas1_starting_transaction_otherside_invariant1: "dthdatas1 ( T [ j +=rdreq Y] [ i s= Z])  = dthdatas1 T "
  apply(cases j)
   apply simp+
  done

lemma dthdatas2_starting_transaction_otherside_invariant2: "dthdatas2 ( T [ j +=rdreq Y] [ i s= Z]) = dthdatas2 T "
  apply(cases j)
   apply simp+
  done

lemma nextGOPending_xyad_htdd_invariant1: " nextGOPending ( T [ j s= mesi] [ k :=dd msg] [ m -=devd ]) i  = nextGOPending T i"
  apply(cases "htddatas1 T")
   apply(cases j)
    apply(cases k)
  apply simp+
    apply(cases k)
     apply simp+
   apply(cases j)
    apply(cases k)
     apply simp+
    apply(cases k)
  by simp+

lemma CSTATE_xyad_htdd_invariant1: " CSTATE X ( T [ 0 s= mesi] [ k :=dd msg] [ m -=devd ]) 1  = CSTATE X T 1"
  apply(cases k)
  by simp+

lemma CSTATE_xyad_htdd_invariant2: " CSTATE X ( T [ 1 s= mesi] [ k :=dd msg] [ m -=devd ]) 0  = CSTATE X T 0"
  apply(cases k)
  by simp+

lemma CSTATE_xyad_htdd_invariant3: " CSTATE mesi ( T [ 0 s= mesi] [ k :=dd msg] [ m -=devd ]) 0"
  apply(cases k)
  by simp+

lemma CSTATE_xyad_htdd_invariant4: " CSTATE mesi ( T [ 1 s= mesi] [ k :=dd msg] [ m -=devd ]) 1"
  apply(cases k)
  by simp+

lemma CSTATE_x_rdy_invariant1: "CSTATE X ( T [ i +=hostdata txid] [ 5 sHost= h] [ j +=reqresp g me txid] [ k -=req ]) n =
   CSTATE X T n"
  apply(case_tac n)
   apply(case_tac k)
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
   apply(case_tac k)
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
  by simp+


lemma nextStore_x_rdy_invariant1: "nextStore ( T [ i +=hostdata txid] [ 5 sHost= h] [ j +=reqresp g me txid] [ k -=req ]) n =
   nextStore T n"
  apply(case_tac n)
   apply(case_tac k)
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
   apply(case_tac k)
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
      apply simp+
    apply(case_tac i)
     apply(case_tac j)
      apply simp+
     apply(case_tac j)
  by simp+
lemma HSTATE_X_Evict_invariant1: "HSTATE X ( T [ i +=rdreq rq] [ i s= m])  = HSTATE X T"
  apply(cases i)
  by(simp)+

lemma snps1_X_Evict_invariant1: "snps1   ( T [ i +=rdreq re] [ i s= m]) = snps1 T"
  apply(cases i)
  by simp+
lemma snps2_X_Evict_invariant1: "snps2   ( T [ i +=rdreq re] [ i s= m]) = snps2 T"
  apply(cases i)
  by simp+
lemma CSTATE_X_rd_invariant1: "CSTATE X ( T [ j +=snp st txid]  [ 5 sHost= h] [ i -=req ]) 1 = CSTATE X T 1"
  apply(cases j)
  by simp+

lemma reqresps2_X_rd_invariant1: "reqresps2 ( T [ j +=snp st txid]  [ 5 sHost= h] [ i -=req ])  = reqresps2 T"
    apply(cases j)
  by simp+

lemma htddatas2_X_rd_invariant1: "htddatas2 ( T [ j +=snp st txid]  [ 5 sHost= h] [ i -=req ]) = htddatas2 T"
    apply(cases j)
  by simp+

lemma nextSnoopIs_X_rd_invariant1:"X \<noteq> st \<Longrightarrow> nextSnoopIs X ( T [ j +=snp st txid]  [ 5 sHost= h] [ i -=req ]) 1 = nextSnoopIs X T 1 "
  apply(cases j)
  apply(cases "snps1 T")
    apply simp
   apply simp
  apply(cases "snps2 T")
  by simp+

lemma HSTATE_X_rd_invariant1:"
    HSTATE h ( T [ j +=snp st txid]  [ 5 sHost= h] [ i -=req ]) "
  by simp

lemma xyad_go_invariant_CSTATE_sameside: "i \<le> 1 \<Longrightarrow> CSTATE x ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ j -=reqresp ]) i"
  unfolding CSTATE_def
  apply(cases i)
  by simp+

lemma xyad_go_invariant2: "nextHTDDataPending ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ j -=reqresp ]) k = nextHTDDataPending T k"
  apply(cases k)
  by simp+
  

lemma snpresps2_xyad_go_invariant: "snpresps2 ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ j -=reqresp ]) = snpresps2 T"
  by simp

lemma reqresps1_xyad_go_sameside_invariant: "length (reqresps1 T) \<le> 1 \<Longrightarrow>  reqresps1 ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ 0 -=reqresp ]) = []"
  apply(cases "(reqresps1 T)")
  by simp+

lemma reqresps2_xyad_go_sameside_invariant: "length (reqresps2 T) \<le> 1 \<Longrightarrow>  reqresps2 ( T\<lparr>buffer2 := om\<rparr> [ i s= x] [ 1 -=reqresp ]) = []"
  apply(cases "(reqresps2 T)")
  by simp+

lemma nextStore_XIAGO_WP1: "nextStore T 1 = nextStore ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ i -=reqresp ] [ devi +=d2hd dthd] [ -=i 0 ]) 1"
  apply(cases "program1 T")
   apply(cases i)
  apply(cases devi)
     apply simp
    apply simp
  apply(cases devi)
     apply simp
    apply simp
   apply(cases i)
  apply(cases devi)
     apply simp
    apply simp
  apply(cases devi)
  by simp+


lemma nextStore_XIAGO_WP2: "nextStore T 0 = nextStore ( T\<lparr>buffer1 := om\<rparr> [ i s= x] [ i -=reqresp ] [ devi +=d2hd dthd] [ -=i 1 ]) 0"
  apply(cases "program2 T")
   apply(cases i)
  apply(cases devi)
     apply simp
    apply simp
  apply(cases devi)
     apply simp
    apply simp
   apply(cases i)
  apply(cases devi)
     apply simp
    apply simp
  apply(cases devi)
  by simp+

lemma reqresps1_IIAGWP: "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = []"
  apply(cases "reqresps1 T")
   apply(cases "program1 T")
  apply simp+
   apply(cases "program1 T")
  by simp+

lemma nextGOPendingIs_IIAGWP: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
  apply(cases "reqresps1 T")
   apply(cases "program1 T")
  apply simp+
   apply(cases "program1 T")
  by simp+

lemma reqresps1_IIAGWP2: "length (reqresps2 T) \<le> 1 \<Longrightarrow> reqresps2 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = []"
  apply(cases "reqresps2 T")
   apply(cases "program2 T")
  apply simp+
   apply(cases "program2 T")
  by simp+

lemma nextGOPendingIs_IIAGWP2: "length (reqresps2 T) \<le> 1 \<Longrightarrow> \<not> nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 1"
  apply(cases "reqresps2 T")
   apply(cases "program2 T")
  apply simp+
   apply(cases "program2 T")
  by simp+

lemma nextGOPendingIs_XYADGO1: "length (reqresps1 T) \<le> 1 \<Longrightarrow> \<not> nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ i s= xyd] [ 0 -=reqresp ]) 0"
  using reqresps1_xyad_go_sameside_invariant reqresps_empty_noGOPendingIs1 by blast

lemma nextGOPendingIs_XYADGO2: "length (reqresps2 T) \<le> 1 \<Longrightarrow> \<not> nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ i s= xyd] [ 1 -=reqresp ]) 1"
  using reqresps2_xyad_go_sameside_invariant reqresps_empty_noGOPendingIs2 by blast

lemma nextGOPendingIs_XYADGO_agnostic1: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ i s= xyd] [ 0 -=reqresp ]) 1"
  by simp

lemma nextGOPendingIs_XYADGO_agnostic2: "nextGOPendingIs X T 0 = nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ i s= xyd] [ 1 -=reqresp ]) 0"
  by simp

lemma HSTATE_XYADGO1: "HSTATE X T = HSTATE X ( T\<lparr>buffer1 := om\<rparr> [ i s= xyd] [ 0 -=reqresp ])"
  by simp

lemma HSTATE_XYADGO2: "HSTATE X T = HSTATE X ( T\<lparr>buffer2 := om\<rparr> [ i s= xyd] [ 1 -=reqresp ])"
  by simp

lemma nextDTHDataFrom1_XYADGO1: "nextDTHDataFrom 0 T = nextDTHDataFrom 0 ( T\<lparr>buffer1 := om\<rparr> [ i s= xyd] [ 0 -=reqresp ])"
  by simp

lemma nextDTHDataFrom1_XYADGO2: "nextDTHDataFrom 0 T = nextDTHDataFrom 0 ( T\<lparr>buffer2 := om\<rparr> [ i s= xyd] [ 1 -=reqresp ])"
  by simp

lemma nextDTHDataFrom2_XYADGO1: "nextDTHDataFrom 1 T = nextDTHDataFrom 1 ( T\<lparr>buffer1 := om\<rparr> [ i s= xyd] [ 0 -=reqresp ])"
  by simp

lemma nextDTHDataFrom2_XYADGO2: "nextDTHDataFrom 1 T = nextDTHDataFrom 1 ( T\<lparr>buffer2 := om\<rparr> [ i s= xyd] [ 1 -=reqresp ])"
  by simp

lemma nextGOPendingIs_XYAGO_other1: "nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= Y] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingIs X T 1"
  by(cases "program1 T", simp+)
  
lemma nextGOPendingIs_XYAGO_other2: "nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= Y] [ 1 -=reqresp ] [ -=i 1]) 0 = nextGOPendingIs X T 0"
  by(cases "program2 T", simp+)

lemma reqresps1_XYAGO: "length (reqresps1 T) \<le> 1 \<Longrightarrow> reqresps1 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= Y] [ 0 -=reqresp ] [ -=i 0]) = []"
  apply(cases "reqresps1 T", cases "program1 T", simp+)
  by(cases "program1 T", simp+)

lemma reqresps2_XYAGO: "length (reqresps2 T) \<le> 1 \<Longrightarrow> reqresps2 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= Y] [ 1 -=reqresp ] [ -=i 1]) = []"
  apply(cases "reqresps2 T", cases "program2 T", simp+)
  by(cases "program2 T", simp+)


lemma HSTATE_XYAGO1: "HSTATE X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= Y] [ 0 -=reqresp ] [ -=i 0]) = HSTATE X T"
  by(cases "program1 T", simp+)

lemma HSTATE_XYAGO2: "HSTATE X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= Y] [ 1 -=reqresp ] [ -=i 1]) = HSTATE X T"
  by(cases "program2 T", simp+)

lemma nextDTHDataFrom1_XYAGO1: "nextDTHDataFrom 0 T = nextDTHDataFrom 0 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= Y] [ 0 -=reqresp ] [ -=i 0])"
  by(cases "program1 T", simp+)

lemma nextDTHDataFrom2_XYAGO1: "nextDTHDataFrom 1 T = nextDTHDataFrom 1 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= Y] [ 0 -=reqresp ] [ -=i 0])"
  by(cases "program1 T", simp+)

lemma nextDTHDataFrom1_XYAGO2: "nextDTHDataFrom 0 T = nextDTHDataFrom 0 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= Y] [ 1 -=reqresp ] [ -=i 1])"
  by(cases "program2 T", simp+)

lemma nextDTHDataFrom2_XYAGO2: "nextDTHDataFrom 1 T = nextDTHDataFrom 1 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= Y] [ 1 -=reqresp ] [ -=i 1])"
  by(cases "program2 T", simp+)

lemma HSTATE_XIAGOWP1: "HSTATE X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= x] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = HSTATE X T"
  by(cases "program1 T", simp+)

lemma HSTATE_XIAGOWP2: "HSTATE X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= x] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = HSTATE X T"
  by(cases "program2 T", simp+)

lemma nextGOPendingIs_XIAGOWP_otherside1: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= ms] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
  by(cases "program1 T", simp+)
lemma nextGOPendingIs_XIAGOWP_otherside2: "nextGOPendingIs X T 0 = nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= ms] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0"
  by(cases "program2 T", simp+)



lemma nextGOPendingIs_XIAGOWPD_otherside1: "nextGOPendingIs X T 1 = nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= ms] [ 0 -=reqresp ]  [ -=i 0]) 1"
  by(cases "program1 T", simp+)
lemma nextGOPendingIs_XIAGOWPD_otherside2: "nextGOPendingIs X T 0 = nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= ms] [ 1 -=reqresp ]  [ -=i 1]) 0"
  by(cases "program2 T", simp+)




lemma "HSTATE_rule_1":
  shows "HSTATE X T = HSTATE X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])"
  by (cases "program1 T", simp+)

lemma "HSTATE_rule_2":
  shows "HSTATE X T = HSTATE X ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])"
  by (cases "program1 T", simp+)

lemma "HSTATE_rule_3":
  shows "HSTATE X T = HSTATE X ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])"
  by (cases "program1 T", simp+)



lemma "HSTATE_rule_6":
  shows "HSTATE X T = HSTATE X ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])"
  by (cases "program1 T", simp+)

lemma "HSTATE_rule_1_flipped":
  shows "HSTATE X T = HSTATE X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 0])"
  by (cases "program1 T", simp+)

lemma "HSTATE_rule_2_flipped":
  shows "HSTATE X T = HSTATE X ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 0])"
  by (cases "program1 T", simp+)

lemma "HSTATE_rule_3_flipped":
  shows "HSTATE X T = HSTATE X ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ])"
  by (cases "program1 T", simp+)



lemma "HSTATE_rule_6_flipped":
  shows "HSTATE X T = HSTATE X ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 0] [ 1 -=devd ])"
  by (cases "program1 T", simp+)













lemma InvalidX_HSTATE1:
  shows "HSTATE X T = HSTATE X ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state])"
  by (cases "program1 T", simp+)







lemma "HSTATE_rule_14":
  shows "HSTATE X T = HSTATE X ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])"
  by (cases "program1 T", simp+)



lemma "HSTATE_rule_16":
  shows "HSTATE X T = HSTATE X (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd])"
  by (cases "program1 T", simp+)




lemma InvalidX_HSTATE2:
  shows "HSTATE X T = HSTATE X ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state])"
  by (cases "program1 T", simp+)





lemma "HSTATE_rule_14_flipped":
  shows "HSTATE X T = HSTATE X ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state])"
  by (cases "program1 T", simp+)



lemma "HSTATE_rule_16_flipped":
  shows "HSTATE X T = HSTATE X (T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd])"
  by (cases "program1 T", simp+)



\<comment>\<open>Mass-generated lemmas for CSTATE and rules: rules should not affect CSTATE on the other side\<close>
lemma "CSTATE_otherside_rule_1":
  shows "CSTATE X T 1 = CSTATE X ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_2":
  shows "CSTATE X T 1 = CSTATE X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_3":
  shows "CSTATE X T 1 = CSTATE X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_4":
  shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_5":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_6":
  shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_7":
  shows "CSTATE X T 1 = CSTATE X ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_8":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_9":
  shows "CSTATE X T 1 = CSTATE X ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_10":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_11":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox Modified txid] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_12":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_19":
  shows "CSTATE X T 1 = CSTATE X ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_20":
  shows "CSTATE X T 1 = CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_21":
  shows "CSTATE X T 1 = CSTATE X ( T [ 1 +=reqresp gox Modified txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_27":
  shows "CSTATE X T 1 = CSTATE X (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1"
  by (cases "program1 T", simp+)


lemma "CSTATE_otherside_rule_33":
  shows "CSTATE X T 1 = CSTATE X (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)




lemma "CSTATE_otherside_rule_40":
  shows "CSTATE X T 1 = CSTATE X ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1"
  by (cases "program1 T", simp+)








lemma "CSTATE_otherside_rule_54":
  shows "CSTATE X T 1 = CSTATE X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)




lemma "CSTATE_otherside_rule_1_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_2_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_3_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_4_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_5_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_6_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_8_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_9_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_10_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_11_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_19_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T\<lparr>buffer2 := om\<rparr> [ 1 +=snpresp rspx tid] [ 1 -=snp ] [ 1 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_20_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_21_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 +=reqresp gox Modified txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_27_flipped":
  shows "CSTATE X T 0 = CSTATE X (T \<lparr>buffer2 := om\<rparr> [ 1 +=snpresp rspx txid] [ 1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_33_flipped":
  shows "CSTATE X T 0 = CSTATE X (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_40_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_54_flipped":
  shows "CSTATE X T 0 = CSTATE X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 1 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_assign_rule_1":
  shows "CSTATE mesi_state ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
  by (cases "program1 T", simp+)
lemma "CSTATE_assign_rule_2":
  shows "CSTATE mesi_state ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 0"
  by (cases "program1 T", simp+)


lemma "CSTATE_assign_rule_4":
  shows "CSTATE mesi_state ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 0"
  by (cases "program1 T", simp+)


lemma "CSTATE_assign_rule_6":
  shows "CSTATE mesi_state ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
  by (cases "program1 T", simp+)


lemma "CSTATE_assign_rule_16":
  shows "CSTATE mesi_state (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "program1 T", simp+)

lemma "CSTATE_assign_rule_1_flipped":
  shows "CSTATE mesi_state ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "CSTATE_assign_rule_2_flipped":
  shows "CSTATE mesi_state ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 1"
  by (cases "program2 T", simp+)
lemma "CSTATE_assign_rule_4_flipped":
  shows "CSTATE mesi_state ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 1"
  by (cases "program2 T", simp+)

lemma "CSTATE_assign_rule_6_flipped":
  shows "CSTATE mesi_state ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1"
  by (cases "program2 T", simp+)

lemma "CSTATE_assign_rule_16_flipped":
  shows "CSTATE mesi_state (T \<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx txid] [ 0 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "program2 T", simp+)

lemma CSTATE_different1: "CSTATE X T 0 \<and> X \<noteq> Y \<Longrightarrow> \<not> CSTATE Y T 0"
  by simp

lemma CSTATE_different2: "CSTATE X T 1 \<and> X \<noteq> Y \<Longrightarrow> \<not> CSTATE Y T 1"
  by simp



































lemma "CSTATE_HostSide_rule_1_0":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_1_1":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_2_0":
  shows "CSTATE mesi_state ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_2_1":
  shows "CSTATE mesi_state ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_3_0":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_3_1":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = CSTATE mesi_state T 1"
  by simp



lemma "CSTATE_HostSide_rule_6_0":
  shows "CSTATE mesi_state ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_6_1":
  shows "CSTATE mesi_state ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_7_0":
  shows "CSTATE mesi_state ( T [ 1 +=reqresp gox Modified txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_7_1":
  shows "CSTATE mesi_state ( T [ 1 +=reqresp gox Modified txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1 = CSTATE mesi_state T 1"
  by simp


lemma "CSTATE_HostSide_rule_13_0":
  shows "CSTATE mesi_state (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp



lemma "CSTATE_HostSide_rule_16_0":
  shows "CSTATE mesi_state ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_16_1":
  shows "CSTATE mesi_state ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1 = CSTATE mesi_state T 1"
  by simp



lemma "CSTATE_HostSide_rule_28_0":
  shows "CSTATE mesi_state ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_28_1":
  shows "CSTATE mesi_state ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = CSTATE mesi_state T 1"
  by simp




lemma "CSTATE_HostSide_rule_1_flipped_1":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_1_flipped_0":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_2_flipped_1":
  shows "CSTATE mesi_state ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_2_flipped_0":
  shows "CSTATE mesi_state ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp

lemma "CSTATE_HostSide_rule_3_flipped_1":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_3_flipped_0":
  shows "CSTATE mesi_state ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp


lemma "CSTATE_HostSide_rule_6_flipped_1":
  shows "CSTATE mesi_state ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_6_flipped_0":
  shows "CSTATE mesi_state ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = CSTATE mesi_state T 0"
  by simp





lemma "CSTATE_HostSide_rule_13_flipped_0":
  shows "CSTATE mesi_state (  T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp



lemma "CSTATE_HostSide_rule_28_flipped_1":
  shows "CSTATE mesi_state ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = CSTATE mesi_state T 1"
  by simp

lemma "CSTATE_HostSide_rule_28_flipped_0":
  shows "CSTATE mesi_state ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = CSTATE mesi_state T 0"
  by simp

  lemma Invalid_not_eq_MIA: "Invalid \<noteq> MIA"
    by simp

\<comment>\<open> Auto-generated nextGOPending-related bits\<close>
lemma "nextGOPendingStateGeneral_rule_1_0":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_1_1":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_2_0":
  shows "nextGOPendingState mesi ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_2_1":
  shows "nextGOPendingState mesi ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_3_0":
  shows "nextGOPendingState mesi ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_3_1":
  shows "nextGOPendingState mesi ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_4_0":
  shows "nextGOPendingState mesi ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_4_1":
  shows "nextGOPendingState mesi ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_5_0":
  shows "nextGOPendingState mesi ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_5_1":
  shows "nextGOPendingState mesi ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)




lemma "nextGOPendingStateGeneral_rule_10_0":
  shows "nextGOPendingState mesi ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_10_1":
  shows "nextGOPendingState mesi ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_11_0":
  shows "nextGOPendingState mesi ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_11_1":
  shows "nextGOPendingState mesi ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingStateGeneral_rule_14_0":
  shows "nextGOPendingState mesi (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_14_1":
  shows "nextGOPendingState mesi (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingStateGeneral_rule_18_0":
  shows "nextGOPendingState mesi (T [ -=i 0]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_18_1":
  shows "nextGOPendingState mesi (T [ -=i 0]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_19_0":
  shows "nextGOPendingState mesi (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_19_1":
  shows "nextGOPendingState mesi (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingStateGeneral_rule_30_0":
  shows "nextGOPendingState mesi ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingStateGeneral_rule_30_1":
  shows "nextGOPendingState mesi ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)





lemma "nextGOPendingStateGeneral_rule_1_flipped_1":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_1_flipped_0":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_2_flipped_1":
  shows "nextGOPendingState mesi ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_2_flipped_0":
  shows "nextGOPendingState mesi ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_3_flipped_1":
  shows "nextGOPendingState mesi ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_3_flipped_0":
  shows "nextGOPendingState mesi ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_4_flipped_1":
  shows "nextGOPendingState mesi ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_4_flipped_0":
  shows "nextGOPendingState mesi ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_5_flipped_1":
  shows "nextGOPendingState mesi ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_5_flipped_0":
  shows "nextGOPendingState mesi ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)




lemma "nextGOPendingStateGeneral_rule_10_flipped_1":
  shows "nextGOPendingState mesi ( T\<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx tid] [ 0 -=snp ] [ 1 s= mesi_state]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_10_flipped_0":
  shows "nextGOPendingState mesi ( T\<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx tid] [ 0 -=snp ] [ 1 s= mesi_state]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_11_flipped_1":
  shows "nextGOPendingState mesi ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_11_flipped_0":
  shows "nextGOPendingState mesi ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPendingStateGeneral_rule_14_flipped_1":
  shows "nextGOPendingState mesi (T \<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx txid] [ 0 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_14_flipped_0":
  shows "nextGOPendingState mesi (T \<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx txid] [ 0 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPendingStateGeneral_rule_18_flipped_1":
  shows "nextGOPendingState mesi (T [ -=i 1]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_18_flipped_0":
  shows "nextGOPendingState mesi (T [ -=i 1]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_19_flipped_1":
  shows "nextGOPendingState mesi (  T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_19_flipped_0":
  shows "nextGOPendingState mesi (  T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPendingStateGeneral_rule_30_flipped_1":
  shows "nextGOPendingState mesi ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingStateGeneral_rule_30_flipped_0":
  shows "nextGOPendingState mesi ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)


\<comment>\<open>nextGOPending general lemmas\<close>
lemma "nextGOPending_General_rule_1_0":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_1_1":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_2_0":
  shows "nextGOPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_2_1":
  shows "nextGOPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_General_rule_4_0":
  shows "nextGOPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_4_1":
  shows "nextGOPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_5_0":
  shows "nextGOPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_5_1":
  shows "nextGOPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPending_General_rule_10_0":
  shows "nextGOPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_10_1":
  shows "nextGOPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_11_0":
  shows "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_11_1":
  shows "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)




lemma "nextGOPending_General_rule_14_0":
  shows "nextGOPending (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_14_1":
  shows "nextGOPending (T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPending_General_rule_19_0":
  shows "nextGOPending (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_19_1":
  shows "nextGOPending (  T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_General_rule_30_0":
  shows "nextGOPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_30_1":
  shows "nextGOPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_General_rule_1_flipped_1":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_1_flipped_0":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_2_flipped_1":
  shows "nextGOPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_2_flipped_0":
  shows "nextGOPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPending_General_rule_4_flipped_1":
  shows "nextGOPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_4_flipped_0":
  shows "nextGOPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_5_flipped_1":
  shows "nextGOPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_5_flipped_0":
  shows "nextGOPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPending_General_rule_10_flipped_1":
  shows "nextGOPending ( T\<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx tid] [ 0 -=snp ] [ 1 s= mesi_state]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_10_flipped_0":
  shows "nextGOPending ( T\<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx tid] [ 0 -=snp ] [ 1 s= mesi_state]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_11_flipped_1":
  shows "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_11_flipped_0":
  shows "nextGOPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPending_General_rule_14_flipped_1":
  shows "nextGOPending (T \<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx txid] [ 0 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_14_flipped_0":
  shows "nextGOPending (T \<lparr>buffer2 := om\<rparr> [ 0 +=snpresp rspx txid] [ 0 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)




lemma "nextGOPending_General_rule_18_flipped_1":
  shows "nextGOPending (T [ -=i 1]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_18_flipped_0":
  shows "nextGOPending (T [ -=i 1]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_19_flipped_1":
  shows "nextGOPending (  T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_19_flipped_0":
  shows "nextGOPending (  T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPending_General_rule_30_flipped_1":
  shows "nextGOPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_General_rule_30_flipped_0":
  shows "nextGOPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>useful for verifying two conjuncts C1, C2 are self contained under rule set Fpass \<union> Ffail\<close>
lemma composing_conjuncts1: "\<lbrakk> P T \<and> f \<in> Fpass \<and> C1 T \<longrightarrow> C1 (f T); P T \<and> f \<in> (Ffail \<union> Fpass) \<and> C2 T \<longrightarrow> C2 (f T); 
P T \<and> f \<in> Ffail \<and> C1 T \<and> C2 T \<longrightarrow> C1 (f T) \<and> C2 (f T) \<rbrakk> \<Longrightarrow> P T \<and> f \<in> (Ffail \<union> Fpass) \<and> C1 T \<and> C2 T \<longrightarrow> C1 (f T) \<and> C2 (f T)"
  by blast

\<comment>\<open>auto generated otherside nextGOPending equalities\<close>


lemma "nextGOPending_yes_reqresp_rule_3_1":
  shows "nextGOPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_4_1":
  shows "nextGOPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_6_1":
  shows "nextGOPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_8_1":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_10_1":
  shows "nextGOPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPending T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPending_yes_reqresp_rule_13_1":
  shows "nextGOPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0 = nextGOPending T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_3_flipped_0":
  shows "nextGOPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_4_flipped_0":
  shows "nextGOPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_6_flipped_0":
  shows "nextGOPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_8_flipped_0":
  shows "nextGOPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_10_flipped_0":
  shows "nextGOPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_11_flipped_0":
  shows "nextGOPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_12_flipped_0":
  shows "nextGOPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPending_yes_reqresp_rule_13_flipped_0":
  shows "nextGOPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)



lemma "nextGOPending_yes_reqresp_rule_15_flipped_0":
  shows "nextGOPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextGOPending T 0"
  by (cases "program2 T", simp+)





\<comment>\<open>possibly overlooked nextGOPending lemmas\<close>


lemma "nextGOPending_overlooked_reqresp_rule_11_flipped_1":
  shows "nextGOPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)


lemma "nextGOPending_overlooked_reqresp_rule_12_flipped_1":
  shows "nextGOPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPending_overlooked_reqresp_rule_15_flipped_1":
  shows "nextGOPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1 = nextGOPending T 1"
  by (cases "program2 T", simp+)


\<comment>\<open>nextGOPendingState overlooked lemmas \<close>


lemma "nextGOPending_overlooked_reqresp_rule_3_0":
  shows "nextGOPendingState mesi ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPending_overlooked_reqresp_rule_4_0":
  shows "nextGOPendingState mesi ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_overlooked_reqresp_rule_6_0":
  shows "nextGOPendingState mesi ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_overlooked_reqresp_rule_8_0":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPending_overlooked_reqresp_rule_10_0":
  shows "nextGOPendingState mesi ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPending_overlooked_reqresp_rule_13_0":
  shows "nextGOPendingState mesi ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program1 T", simp+)


lemma "nextGOPendingState_overlooked_reqresp_rule_3_flipped_1":
  shows "nextGOPendingState mesi ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_4_flipped_1":
  shows "nextGOPendingState mesi ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPendingState_overlooked_reqresp_rule_6_flipped_1":
  shows "nextGOPendingState mesi ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_8_flipped_1":
  shows "nextGOPendingState mesi ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_10_flipped_1":
  shows "nextGOPendingState mesi ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)



lemma "nextGOPendingState_overlooked_reqresp_rule_11_flipped_1":
  shows "nextGOPendingState mesi ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_11_flipped_0":
  shows "nextGOPendingState mesi ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_12_flipped_1":
  shows "nextGOPendingState mesi ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_12_flipped_0":
  shows "nextGOPendingState mesi ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_13_flipped_1":
  shows "nextGOPendingState mesi ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)



lemma "nextGOPendingState_overlooked_reqresp_rule_15_flipped_1":
  shows "nextGOPendingState mesi ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1 = nextGOPendingState mesi T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingState_overlooked_reqresp_rule_15_flipped_0":
  shows "nextGOPendingState mesi ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextGOPendingState mesi T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>nextGOPendingIs general invaraints\<close>
lemma "nextGOPendingIs_general_rule_1_0":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_1_1":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_2_0":
  shows "nextGOPendingIs X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_2_1":
  shows "nextGOPendingIs X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_3_0":
  shows "nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)




lemma "nextGOPendingIs_general_rule_5_0":
  shows "nextGOPendingIs X ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_5_1":
  shows "nextGOPendingIs X ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_6_0":
  shows "nextGOPendingIs X ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)



lemma "nextGOPendingIs_general_rule_7_0":
  shows "nextGOPendingIs X ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_7_1":
  shows "nextGOPendingIs X ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_8_0":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingIs_general_rule_9_0":
  shows "nextGOPendingIs X ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_9_1":
  shows "nextGOPendingIs X ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_10_0":
  shows "nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingIs_general_rule_11_0":
  shows "nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_11_1":
  shows "nextGOPendingIs X ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_12_0":
  shows "nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_12_1":
  shows "nextGOPendingIs X ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_13_0":
  shows "nextGOPendingIs X ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)



lemma "nextGOPendingIs_general_rule_15_0":
  shows "nextGOPendingIs X ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_15_1":
  shows "nextGOPendingIs X ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_16_0":
  shows "nextGOPendingIs X ( T [ -=i 0]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_16_1":
  shows "nextGOPendingIs X ( T [ -=i 0]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_17_0":
  shows "nextGOPendingIs X ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_17_1":
  shows "nextGOPendingIs X ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_18_0":
  shows "nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingIs_general_rule_18_1":
  shows "nextGOPendingIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program1 T", simp+)


lemma "nextGOPendingIs_general_rule_1_flipped_1":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_1_flipped_0":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_2_flipped_1":
  shows "nextGOPendingIs X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_2_flipped_0":
  shows "nextGOPendingIs X ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_3_flipped_1":
  shows "nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)




lemma "nextGOPendingIs_general_rule_5_flipped_1":
  shows "nextGOPendingIs X ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_5_flipped_0":
  shows "nextGOPendingIs X ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_6_flipped_1":
  shows "nextGOPendingIs X ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPendingIs_general_rule_7_flipped_1":
  shows "nextGOPendingIs X ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_7_flipped_0":
  shows "nextGOPendingIs X ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_8_flipped_1":
  shows "nextGOPendingIs X ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPendingIs_general_rule_9_flipped_1":
  shows "nextGOPendingIs X ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_9_flipped_0":
  shows "nextGOPendingIs X ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_10_flipped_1":
  shows "nextGOPendingIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)


lemma "nextGOPendingIs_general_rule_11_flipped_1":
  shows "nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_11_flipped_0":
  shows "nextGOPendingIs X ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_12_flipped_1":
  shows "nextGOPendingIs X ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_12_flipped_0":
  shows "nextGOPendingIs X ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_13_flipped_1":
  shows "nextGOPendingIs X ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)



lemma "nextGOPendingIs_general_rule_15_flipped_1":
  shows "nextGOPendingIs X ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_15_flipped_0":
  shows "nextGOPendingIs X ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_16_flipped_1":
  shows "nextGOPendingIs X ( T [ -=i 1]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_16_flipped_0":
  shows "nextGOPendingIs X ( T [ -=i 1]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_17_flipped_1":
  shows "nextGOPendingIs X ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_17_flipped_0":
  shows "nextGOPendingIs X ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_18_flipped_1":
  shows "nextGOPendingIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = nextGOPendingIs X T 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingIs_general_rule_18_flipped_0":
  shows "nextGOPendingIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = nextGOPendingIs X T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>nextReqIs general lemmas\<close>
lemma "nextReqIs_general_rule_1_0":
  shows "nextReqIs reqtype ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_2_0":
  shows "nextReqIs reqtype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_3_0":
  shows "nextReqIs reqtype ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_4_0":
  shows "nextReqIs reqtype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_5_0":
  shows "nextReqIs reqtype ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_6_0":
  shows "nextReqIs reqtype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_7_0":
  shows "nextReqIs reqtype ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_8_0":
  shows "nextReqIs reqtype ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_9_0":
  shows "nextReqIs reqtype ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_10_0":
  shows "nextReqIs reqtype ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)


lemma "nextReqIs_general_rule_12_0":
  shows "nextReqIs reqtype ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_13_0":
  shows "nextReqIs reqtype ( T [ -=i 0]) i = nextReqIs reqtype T i"
  by (cases "program1 T", simp+)

lemma "nextReqIs_general_rule_1_flipped_1":
  shows "nextReqIs reqtype ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_2_flipped_1":
  shows "nextReqIs reqtype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_3_flipped_1":
  shows "nextReqIs reqtype ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_4_flipped_1":
  shows "nextReqIs reqtype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_5_flipped_1":
  shows "nextReqIs reqtype ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_6_flipped_1":
  shows "nextReqIs reqtype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_7_flipped_1":
  shows "nextReqIs reqtype ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_8_flipped_1":
  shows "nextReqIs reqtype ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_9_flipped_1":
  shows "nextReqIs reqtype ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_10_flipped_1":
  shows "nextReqIs reqtype ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)



lemma "nextReqIs_general_rule_12_flipped_1":
  shows "nextReqIs reqtype ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

lemma "nextReqIs_general_rule_13_flipped_1":
  shows "nextReqIs reqtype ( T [ -=i 1]) i = nextReqIs reqtype T i"
  by (cases "program2 T", simp+)

\<comment>\<open>nextReqIs otherside lemmas \<close>
lemma "nextReqIs_otherside_rule_1_0":
  shows "nextReqIs reqtype ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextReqIs reqtype T 1"
  by (cases "program1 T", simp+)

lemma "nextReqIs_otherside_rule_2_0":
  shows "nextReqIs reqtype ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1 = nextReqIs reqtype T 1"
  by (cases "program1 T", simp+)

lemma "nextReqIs_otherside_rule_3_0":
  shows "nextReqIs reqtype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextReqIs reqtype T 1"
  by (cases "program1 T", simp+)

lemma "nextReqIs_otherside_rule_4_0":
  shows "nextReqIs reqtype ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 1 = nextReqIs reqtype T 1"
  by (cases "program1 T", simp+)

lemma "nextReqIs_otherside_rule_5_0":
  shows "nextReqIs reqtype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = nextReqIs reqtype T 1"
  by (cases "program1 T", simp+)



lemma "nextReqIs_otherside_rule_1_flipped_1":
  shows "nextReqIs reqtype ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextReqIs reqtype T 0"
  by (cases "program2 T", simp+)

lemma "nextReqIs_otherside_rule_2_flipped_1":
  shows "nextReqIs reqtype ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0 = nextReqIs reqtype T 0"
  by (cases "program2 T", simp+)

lemma "nextReqIs_otherside_rule_3_flipped_1":
  shows "nextReqIs reqtype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextReqIs reqtype T 0"
  by (cases "program2 T", simp+)

lemma "nextReqIs_otherside_rule_4_flipped_1":
  shows "nextReqIs reqtype ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 0 = nextReqIs reqtype T 0"
  by (cases "program2 T", simp+)

lemma "nextReqIs_otherside_rule_5_flipped_1":
  shows "nextReqIs reqtype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = nextReqIs reqtype T 0"
  by (cases "program2 T", simp+)

\<comment>\<open> nextHTDDataPending general lemmas\<close>
lemma "nextHTDDataPending_general_rule_1_0":
  shows "nextHTDDataPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_2_0":
  shows "nextHTDDataPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_3_0":
  shows "nextHTDDataPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_4_0":
  shows "nextHTDDataPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_6_0":
  shows "nextHTDDataPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_7_0":
  shows "nextHTDDataPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_8_0":
  shows "nextHTDDataPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_9_0":
  shows "nextHTDDataPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)


lemma "nextHTDDataPending_general_rule_11_0":
  shows "nextHTDDataPending ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_12_0":
  shows "nextHTDDataPending ( T [ -=i 0]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_13_0":
  shows "nextHTDDataPending ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = nextHTDDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_general_rule_1_flipped_1":
  shows "nextHTDDataPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_2_flipped_1":
  shows "nextHTDDataPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_3_flipped_1":
  shows "nextHTDDataPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_4_flipped_1":
  shows "nextHTDDataPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_5_flipped_1":
  shows "nextHTDDataPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_6_flipped_1":
  shows "nextHTDDataPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_7_flipped_1":
  shows "nextHTDDataPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_8_flipped_1":
  shows "nextHTDDataPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_9_flipped_1":
  shows "nextHTDDataPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_11_flipped_1":
  shows "nextHTDDataPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_12_flipped_1":
  shows "nextHTDDataPending ( T [ -=i 1]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_general_rule_13_flipped_1":
  shows "nextHTDDataPending ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = nextHTDDataPending T i"
  by (cases "program2 T", simp+)

\<comment>\<open> nextHTDDataPending otherside lemmas\<close>
lemma "nextHTDDataPending_otherside_rule_1_0":
  shows "nextHTDDataPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 = nextHTDDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_2_0":
  shows "nextHTDDataPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextHTDDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_3_0":
  shows "nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1 = nextHTDDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_4_0":
  shows "nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0 = nextHTDDataPending T 0"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_5_0":
  shows "nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 1 = nextHTDDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_6_0":
  shows "nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ]) 1 = nextHTDDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_otherside_rule_1_flipped_1":
  shows "nextHTDDataPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0 = nextHTDDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_otherside_rule_2_flipped_1":
  shows "nextHTDDataPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextHTDDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_otherside_rule_3_flipped_1":
  shows "nextHTDDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0 = nextHTDDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_otherside_rule_4_flipped_1":
  shows "nextHTDDataPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1 = nextHTDDataPending T 1"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_otherside_rule_5_flipped_1":
  shows "nextHTDDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 0 = nextHTDDataPending T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>minus req nextReqIs \<close>
lemma "minus_req_nextReqIs_False_rule_1_0":
  shows "length (reqs1 T) <= 1 --> nextReqIs X ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0 = False"
  by (cases "reqs1 T", simp+)

lemma "minus_req_nextReqIs_False_rule_2_0":
  shows "length (reqs1 T) <= 1 --> nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0 = False"
  by (cases "reqs1 T", simp+)

lemma "minus_req_nextReqIs_False_rule_3_0":
  shows "length (reqs1 T) <= 1 --> nextReqIs X ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = False"
  by (cases "reqs1 T", simp+)

lemma "minus_req_nextReqIs_False_rule_4_0":
  shows "length (reqs1 T) <= 1 --> nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = False"
  by (cases "reqs1 T", simp+)



lemma "minus_req_nextReqIs_False_rule_1_flipped_1":
  shows "length (reqs2 T) <= 1 --> nextReqIs X ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1 = False"
  by (cases "reqs2 T", simp+)

lemma "minus_req_nextReqIs_False_rule_2_flipped_1":
  shows "length (reqs2 T) <= 1 --> nextReqIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1 = False"
  by (cases "reqs2 T", simp+)

lemma "minus_req_nextReqIs_False_rule_3_flipped_1":
  shows "length (reqs2 T) <= 1 --> nextReqIs X ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = False"
  by (cases "reqs2 T", simp+)

lemma "minus_req_nextReqIs_False_rule_4_flipped_1":
  shows "length (reqs2 T) <= 1 --> nextReqIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = False"
  by (cases "reqs2 T", simp+)




\<comment>\<open>minus req nextReqIs false but with swmr+ instead of length (reqsi) \<le> 1 as precondition\<close>

lemma "minus_req_nextReqIs_False_swmrp_rule_1_0":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0 = False"
  apply (unfold SWMR_state_machine_def, elim conjE)
  by (metis minus_req_nextReqIs_False_rule_1_0)

lemma "minus_req_nextReqIs_False_swmrp_rule_2_0":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0 = False"
  apply (unfold SWMR_state_machine_def, elim conjE)
  by (metis minus_req_nextReqIs_False_rule_2_0)

lemma "minus_req_nextReqIs_False_swmrp_rule_3_0":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = False"
  apply (unfold SWMR_state_machine_def, elim conjE)
  by (metis minus_req_nextReqIs_False_rule_3_0)

lemma "minus_req_nextReqIs_False_swmrp_rule_4_0":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = False"
  apply (unfold SWMR_state_machine_def, elim conjE)
  by (metis minus_req_nextReqIs_False_rule_4_0)



lemma "minus_req_nextReqIs_False_swmrp_rule_1_flipped_1":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1 = False"
    apply (unfold SWMR_state_machine_def, elim conjE)
    by (metis minus_req_nextReqIs_False_rule_1_flipped_1)

lemma "minus_req_nextReqIs_False_swmrp_rule_2_flipped_1":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1 = False"
    apply (unfold SWMR_state_machine_def, elim conjE)
    by (metis minus_req_nextReqIs_False_rule_2_flipped_1)

lemma "minus_req_nextReqIs_False_swmrp_rule_3_flipped_1":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = False"
    apply (unfold SWMR_state_machine_def, elim conjE)
    by (metis minus_req_nextReqIs_False_rule_3_flipped_1)

lemma "minus_req_nextReqIs_False_swmrp_rule_4_flipped_1":
  shows "SWMR_state_machine T \<Longrightarrow> nextReqIs X ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = False"
    apply (unfold SWMR_state_machine_def, elim conjE)
    by (metis minus_req_nextReqIs_False_rule_4_flipped_1)

\<comment>\<open>+h2dd +hostdata \<longrightarrow> nextHTDDataPending True\<close>
lemma "nextHTDDataPending_true_rule_1_0":
  shows "nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_true_rule_2_0":
  shows "nextHTDDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "nextHTDDataPending_true_rule_3_0":
  shows "nextHTDDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)



lemma "nextHTDDataPending_true_rule_1_flipped_1":
  shows "nextHTDDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_true_rule_2_flipped_1":
  shows "nextHTDDataPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program2 T", simp+)

lemma "nextHTDDataPending_true_rule_3_flipped_1":
  shows "nextHTDDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)













\<comment>\<open>GOPlus nextGOPending \<close>
lemma "nextGOPendingPlus_true_rule_1_0":
  shows "reqresps1 T = [] \<Longrightarrow> nextGOPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp GO   mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingPlus_true_rule_2_0":
  shows "reqresps1 T = [] \<Longrightarrow> nextGOPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp GO   mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextGOPendingPlus_true_rule_3_0":
  shows "reqresps2 T = [] \<Longrightarrow> nextGOPending ( T [ 1 +=reqresp GO   mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1"
  by (cases "program1 T", simp+)

lemma "nextGOPendingPlus_true_rule_1_flipped_1":
  shows "reqresps2 T = [] \<Longrightarrow> nextGOPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp GO   mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingPlus_true_rule_2_flipped_1":
  shows "reqresps2 T = [] \<Longrightarrow> nextGOPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp GO   mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextGOPendingPlus_true_rule_3_flipped_1":
  shows "reqresps1 T = [] \<Longrightarrow> nextGOPending ( T [ 0 +=reqresp GO   mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 0"
  by (cases "program2 T", simp+)




\<comment>\<open>nextSnpRespIs general lemmas \<close>
lemma "nextSnpRespIs_general_rule_1_0":
  shows "nextSnpRespIs snpresptype ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_2_0":
  shows "nextSnpRespIs snpresptype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_3_0":
  shows "nextSnpRespIs snpresptype ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_4_0":
  shows "nextSnpRespIs snpresptype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_5_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_6_0":
  shows "nextSnpRespIs snpresptype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_7_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_8_0":
  shows "nextSnpRespIs snpresptype ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_9_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_10_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_11_0":
  shows "nextSnpRespIs snpresptype ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)



lemma "nextSnpRespIs_general_rule_13_0":
  shows "nextSnpRespIs snpresptype ( T [ -=i 0]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_14_0":
  shows "nextSnpRespIs snpresptype ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_15_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_16_0":
  shows "nextSnpRespIs snpresptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnpRespIs_general_rule_1_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_2_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_3_flipped_1":
  shows "nextSnpRespIs snpresptype ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_4_flipped_1":
  shows "nextSnpRespIs snpresptype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_5_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_6_flipped_1":
  shows "nextSnpRespIs snpresptype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_7_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_8_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_9_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_10_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_11_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)


lemma "nextSnpRespIs_general_rule_13_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ -=i 1]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_14_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnpRespIs_general_rule_15_flipped_1":
  shows "nextSnpRespIs snpresptype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = nextSnpRespIs snpresptype T i"
  by (cases "program2 T", simp+)


(*nextSnoopIs general invariants*)
lemma "nextSnoopIs_general_rule_1_0":
  shows "nextSnoopIs snptype ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_2_0":
  shows "nextSnoopIs snptype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_3_0":
  shows "nextSnoopIs snptype ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_4_0":
  shows "nextSnoopIs snptype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_5_0":
  shows "nextSnoopIs snptype ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_6_0":
  shows "nextSnoopIs snptype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_7_0":
  shows "nextSnoopIs snptype ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_8_0":
  shows "nextSnoopIs snptype ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_9_0":
  shows "nextSnoopIs snptype ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_10_0":
  shows "nextSnoopIs snptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_11_0":
  shows "nextSnoopIs snptype ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_12_0":
  shows "nextSnoopIs snptype ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_13_0":
  shows "nextSnoopIs snptype ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_14_0":
  shows "nextSnoopIs snptype ( T [ -=i 0]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_15_0":
  shows "nextSnoopIs snptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ]) i = nextSnoopIs snptype T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_general_rule_1_flipped_1":
  shows "nextSnoopIs snptype ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_2_flipped_1":
  shows "nextSnoopIs snptype ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_3_flipped_1":
  shows "nextSnoopIs snptype ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_4_flipped_1":
  shows "nextSnoopIs snptype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_5_flipped_1":
  shows "nextSnoopIs snptype ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_6_flipped_1":
  shows "nextSnoopIs snptype ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_7_flipped_1":
  shows "nextSnoopIs snptype ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_8_flipped_1":
  shows "nextSnoopIs snptype ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_9_flipped_1":
  shows "nextSnoopIs snptype ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_10_flipped_1":
  shows "nextSnoopIs snptype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_11_flipped_1":
  shows "nextSnoopIs snptype ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_general_rule_12_flipped_1":
  shows "nextSnoopIs snptype ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)



lemma "nextSnoopIs_general_rule_14_flipped_1":
  shows "nextSnoopIs snptype ( T [ -=i 1]) i = nextSnoopIs snptype T i"
  by (cases "program2 T", simp+)

(*otherside*)
lemma "nextSnoopIs_otherside_rule_1_0":
  shows "nextSnoopIs snptype ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = nextSnoopIs snptype T 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_otherside_rule_2_0":
  shows "nextSnoopIs snptype ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextSnoopIs snptype T 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_otherside_rule_3_0":
  shows "nextSnoopIs snptype ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = nextSnoopIs snptype T 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_otherside_rule_4_0":
  shows "nextSnoopIs snptype ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = nextSnoopIs snptype T 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopIs_otherside_rule_1_flipped_1":
  shows "nextSnoopIs snptype ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = nextSnoopIs snptype T 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_otherside_rule_2_flipped_1":
  shows "nextSnoopIs snptype ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextSnoopIs snptype T 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_otherside_rule_3_flipped_1":
  shows "nextSnoopIs snptype ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = nextSnoopIs snptype T 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopIs_otherside_rule_4_flipped_1":
  shows "nextSnoopIs snptype ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = nextSnoopIs snptype T 1"
  by (cases "program2 T", simp+)


(*nextSnoopPending general lemmas*)
lemma "nextSnoopPending_general_rule_1_0":
  shows "nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_2_0":
  shows "nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_3_0":
  shows "nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_4_0":
  shows "nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_5_0":
  shows "nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_6_0":
  shows "nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_7_0":
  shows "nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_8_0":
  shows "nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_9_0":
  shows "nextSnoopPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_10_0":
  shows "nextSnoopPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_11_0":
  shows "nextSnoopPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_general_rule_12_0":
  shows "nextSnoopPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)


lemma "nextSnoopPending_general_rule_14_0":
  shows "nextSnoopPending ( T [ -=i 0]) i = nextSnoopPending T i"
  by (cases "program1 T", simp+)



lemma "nextSnoopPending_general_rule_1_flipped_1":
  shows "nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_2_flipped_1":
  shows "nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_3_flipped_1":
  shows "nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_4_flipped_1":
  shows "nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_5_flipped_1":
  shows "nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_6_flipped_1":
  shows "nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_7_flipped_1":
  shows "nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_8_flipped_1":
  shows "nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_9_flipped_1":
  shows "nextSnoopPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_10_flipped_1":
  shows "nextSnoopPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_11_flipped_1":
  shows "nextSnoopPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_general_rule_12_flipped_1":
  shows "nextSnoopPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)



lemma "nextSnoopPending_general_rule_14_flipped_1":
  shows "nextSnoopPending ( T [ -=i 1]) i = nextSnoopPending T i"
  by (cases "program2 T", simp+)

(*otherside *)
lemma "nextSnoopPending_otherside_rule_1_0":
  shows "nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = nextSnoopPending T 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_otherside_rule_2_0":
  shows "nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextSnoopPending T 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_otherside_rule_3_0":
  shows "nextSnoopPending ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0 = nextSnoopPending T 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_otherside_rule_4_0":
  shows "nextSnoopPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0 = nextSnoopPending T 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_otherside_rule_1_flipped_1":
  shows "nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = nextSnoopPending T 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_otherside_rule_2_flipped_1":
  shows "nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextSnoopPending T 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_otherside_rule_3_flipped_1":
  shows "nextSnoopPending ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1 = nextSnoopPending T 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_otherside_rule_4_flipped_1":
  shows "nextSnoopPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1 = nextSnoopPending T 1"
  by (cases "program2 T", simp+)
\<comment>\<open>snpsi = [] implies not nextSnoopPending\<close>
lemma "nextSnoopPending_empty_not_rule_1_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_1_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_2_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_2_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_3_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_3_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_4_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_4_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_5_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_5_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_6_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_6_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_7_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_7_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_8_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_8_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_9_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_9_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_10_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_10_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_11_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_11_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_12_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_12_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_13_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_13_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_14_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_rule_14_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ -=i 0]) 1"
  by (cases "program1 T", simp+)


lemma "nextSnoopPending_empty_not_rule_1_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_1_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_2_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_2_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_3_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_3_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_4_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_4_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_5_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_5_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_6_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_6_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_7_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_7_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_8_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_8_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_9_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_9_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_10_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_10_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_11_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_11_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_12_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_12_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 0"
  by (cases "program2 T", simp+)



lemma "nextSnoopPending_empty_not_rule_14_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_rule_14_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ -=i 1]) 0"
  by (cases "program2 T", simp+)

(*other side*)

lemma "nextSnoopPending_empty_not_other_rule_1_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_1_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_2_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_2_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_3_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_3_1":
  shows "snps2 T = [] \<Longrightarrow> length (snps2 ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ])) \<le> 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_4_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_4_1":
  shows "snps2 T = [] \<Longrightarrow> length (snps2 ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ])) \<le> 1"
  by (cases "program1 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_1_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_1_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_2_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_2_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_3_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_3_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> length (snps1 ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ])) \<le> 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_4_flipped_1":
  shows "snps2 T = [] \<Longrightarrow> \<not> nextSnoopPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "nextSnoopPending_empty_not_other_rule_4_flipped_0":
  shows "snps1 T = [] \<Longrightarrow> length (snps1 ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ])) <= 1"
  by (cases "program2 T", simp+)

\<comment>\<open>htddatas1 general lemmas\<close>
lemma "htddatas1_general_rule_1_0":
  shows "htddatas1 ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_2_0":
  shows "htddatas1 ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_3_0":
  shows "htddatas1 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_4_0":
  shows "htddatas1 ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_5_0":
  shows "htddatas1 ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_6_0":
  shows "htddatas1 ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_7_0":
  shows "htddatas1 ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_8_0":
  shows "htddatas1 ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_9_0":
  shows "htddatas1 ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_10_0":
  shows "htddatas1 ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_11_0":
  shows "htddatas1 ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_12_0":
  shows "htddatas1 ( T [ -=i 0]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_13_0":
  shows "htddatas1 ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) = htddatas1 T"
  by (cases "program1 T", simp+)

lemma "htddatas1_general_rule_1_flipped_1":
  shows "htddatas1 ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_2_flipped_1":
  shows "htddatas1 ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_3_flipped_1":
  shows "htddatas1 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_4_flipped_1":
  shows "htddatas1 ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_5_flipped_1":
  shows "htddatas1 ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_6_flipped_1":
  shows "htddatas1 ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_7_flipped_1":
  shows "htddatas1 ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_8_flipped_1":
  shows "htddatas1 ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_9_flipped_1":
  shows "htddatas1 ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = htddatas1 T"
  by (cases "program2 T", simp+)


lemma "htddatas1_general_rule_11_flipped_1":
  shows "htddatas1 ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_12_flipped_1":
  shows "htddatas1 ( T [ -=i 1]) = htddatas1 T"
  by (cases "program2 T", simp+)

lemma "htddatas1_general_rule_13_flipped_1":
  shows "htddatas1 ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) = htddatas1 T"
  by (cases "program2 T", simp+)

(*ewmpty if minus*)
lemma "htddatas1_empty_if_minus_rule_1_0":
  shows "length (htddatas1 T) <= 1 \<Longrightarrow> htddatas1 ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) = []"
  by (cases "htddatas1 T", simp+)

lemma "htddatas1_empty_if_minus_rule_2_0":
  shows "length (htddatas1 T) <= 1 \<Longrightarrow> htddatas1 ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) = []"
  apply (cases "htddatas1 T", cases "program1 T", simp+)
  by(cases "program1 T", simp+)

lemma "htddatas2_empty_if_minus_rule_1_flipped_1":
  shows "length (htddatas2 T) <= 1 \<Longrightarrow> htddatas2 ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = []"
  by (cases "htddatas2 T", simp+)

lemma "htddatas2_empty_if_minus_rule_2_flipped_1":
  shows "length (htddatas2 T) <= 1 \<Longrightarrow> htddatas2 ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = []"
  apply (cases "htddatas2 T", cases "program2 T", simp+)
  by(cases "program2 T", simp+)

\<comment>\<open>nextDTHDataFrom general lemmas \<close>
lemma "nextDTHDataFrom_general_rule_1_0":
  shows "nextDTHDataFrom i ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_2_0":
  shows "nextDTHDataFrom i ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_3_0":
  shows "nextDTHDataFrom i ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_4_0":
  shows "nextDTHDataFrom i ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_5_0":
  shows "nextDTHDataFrom i ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_6_0":
  shows "nextDTHDataFrom i ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_7_0":
  shows "nextDTHDataFrom i ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_8_0":
  shows "nextDTHDataFrom i ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_9_0":
  shows "nextDTHDataFrom i ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_10_0":
  shows "nextDTHDataFrom i ( T [ -=i 0])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_11_0":
  shows "nextDTHDataFrom i ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_12_0":
  shows "nextDTHDataFrom i ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_13_0":
  shows "nextDTHDataFrom i ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ])  = nextDTHDataFrom i T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_general_rule_1_flipped_1":
  shows "nextDTHDataFrom i ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_2_flipped_1":
  shows "nextDTHDataFrom i ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_3_flipped_1":
  shows "nextDTHDataFrom i ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_4_flipped_1":
  shows "nextDTHDataFrom i ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_5_flipped_1":
  shows "nextDTHDataFrom i ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_6_flipped_1":
  shows "nextDTHDataFrom i ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_7_flipped_1":
  shows "nextDTHDataFrom i ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_8_flipped_1":
  shows "nextDTHDataFrom i ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_9_flipped_1":
  shows "nextDTHDataFrom i ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_10_flipped_1":
  shows "nextDTHDataFrom i ( T [ -=i 1]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_11_flipped_1":
  shows "nextDTHDataFrom i ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_general_rule_12_flipped_1":
  shows "nextDTHDataFrom i ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) = nextDTHDataFrom i T"
  by (cases "program2 T", simp+)

\<comment>\<open>nextDTHDataFrom otherside lemmas\<close>

lemma "nextDTHDataFrom_otherside_rule_1_0":
  shows "nextDTHDataFrom 1 ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = nextDTHDataFrom 1 T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_2_0":
  shows "nextDTHDataFrom 1 ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = nextDTHDataFrom 1 T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_3_0":
  shows "nextDTHDataFrom 1 ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  = nextDTHDataFrom 1 T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_4_0":
  shows "nextDTHDataFrom 1 ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = nextDTHDataFrom 1 T "
  by (cases "program1 T", simp+)


lemma "nextDTHDataFrom_otherside_rule_6_0":
  shows "nextDTHDataFrom 1 ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd])  = nextDTHDataFrom 1 T "
  by (cases "program1 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_1_flipped_1":
  shows "nextDTHDataFrom 0 ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = nextDTHDataFrom 0 T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_2_flipped_1":
  shows "nextDTHDataFrom 0 ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = nextDTHDataFrom 0 T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_3_flipped_1":
  shows "nextDTHDataFrom 0 ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = nextDTHDataFrom 0 T"
  by (cases "program2 T", simp+)

lemma "nextDTHDataFrom_otherside_rule_4_flipped_1":
  shows "nextDTHDataFrom 0 ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = nextDTHDataFrom 0 T"
  by (cases "program2 T", simp+)



lemma "nextDTHDataFrom_otherside_rule_6_flipped_1":
  shows "nextDTHDataFrom 0 ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) = nextDTHDataFrom 0 T"
  by (cases "program2 T", simp+)

\<comment>\<open>nextStore otherside \<close>
lemma "nextStore_otherside_rule_1_0":
  shows "nextStore  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextStore  T 1"
  by (cases "program1 T", simp+)

lemma "nextStore_otherside_rule_2_0":
  shows "nextStore  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1 = nextStore  T 1"
  by (cases "program1 T", simp+)

lemma "nextStore_otherside_rule_3_0":
  shows "nextStore  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextStore  T 1"
  by (cases "program1 T", simp+)



lemma "nextStore_otherside_rule_1_flipped_1":
  shows "nextStore  ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = nextStore  T 0"
  by (cases "program2 T", simp+)

lemma "nextStore_otherside_rule_2_flipped_1":
  shows "nextStore  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0 = nextStore  T 0"
  by (cases "program2 T", simp+)

lemma "nextStore_otherside_rule_3_flipped_1":
  shows "nextStore  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextStore  T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>CSTATE other side \<close>
lemma "CSTATE_otherside_rule_1_0":
  shows "CSTATE mesi  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_2_0":
  shows "CSTATE mesi  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_4_0":
  shows "CSTATE mesi  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_5_0":
  shows "CSTATE mesi  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_7_0":
  shows "CSTATE mesi  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)



lemma "CSTATE_otherside_rule_9_0":
  shows "CSTATE mesi  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = CSTATE mesi  T 1"
  by (cases "program1 T", simp+)

lemma "CSTATE_otherside_rule_1_flipped_1":
  shows "CSTATE mesi  ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_2_flipped_1":
  shows "CSTATE mesi  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)



lemma "CSTATE_otherside_rule_4_flipped_1":
  shows "CSTATE mesi  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_5_flipped_1":
  shows "CSTATE mesi  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_6_flipped_1":
  shows "CSTATE mesi  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)

lemma "CSTATE_otherside_rule_7_flipped_1":
  shows "CSTATE mesi  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)



lemma "CSTATE_otherside_rule_9_flipped_1":
  shows "CSTATE mesi  ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = CSTATE mesi  T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>CSTATE general \<close>

lemma "CSTATE_general_rule_1_0":
  shows "CSTATE mesi  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)

lemma "CSTATE_general_rule_2_0":
  shows "CSTATE mesi  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)

lemma "CSTATE_general_rule_3_0":
  shows "CSTATE mesi  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)


lemma "CSTATE_general_rule_5_0":
  shows "CSTATE mesi  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)

lemma "CSTATE_general_rule_6_0":
  shows "CSTATE mesi  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)


lemma "CSTATE_general_rule_8_0":
  shows "CSTATE mesi  ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)

lemma "CSTATE_general_rule_9_0":
  shows "CSTATE mesi  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = CSTATE mesi  T i"
  by (cases "program1 T", simp+)



lemma "CSTATE_general_rule_1_flipped_1":
  shows "CSTATE mesi  ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_2_flipped_1":
  shows "CSTATE mesi  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_3_flipped_1":
  shows "CSTATE mesi  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)


lemma "CSTATE_general_rule_5_flipped_1":
  shows "CSTATE mesi  ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_6_flipped_1":
  shows "CSTATE mesi  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_7_flipped_1":
  shows "CSTATE mesi  ( T [ -=i 1]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_8_flipped_1":
  shows "CSTATE mesi  ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)

lemma "CSTATE_general_rule_9_flipped_1":
  shows "CSTATE mesi  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = CSTATE mesi  T i"
  by (cases "program2 T", simp+)


\<comment>\<open>HSTATE general \<close>




lemma "HSTATE_general_rule_3_0":
  shows "HSTATE hmesi  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)

lemma "HSTATE_general_rule_4_0":
  shows "HSTATE hmesi  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)

lemma "HSTATE_general_rule_5_0":
  shows "HSTATE hmesi  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)


lemma "HSTATE_general_rule_7_0":
  shows "HSTATE hmesi  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)



lemma "HSTATE_general_rule_9_0":
  shows "HSTATE hmesi  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)

lemma "HSTATE_general_rule_10_0":
  shows "HSTATE hmesi  ( T [ -=i 0])  = HSTATE hmesi  T "
  by (cases "program1 T", simp+)



lemma "HSTATE_general_rule_3_flipped_1":
  shows "HSTATE hmesi  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)

lemma "HSTATE_general_rule_4_flipped_1":
  shows "HSTATE hmesi  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)

lemma "HSTATE_general_rule_5_flipped_1":
  shows "HSTATE hmesi  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)



lemma "HSTATE_general_rule_7_flipped_1":
  shows "HSTATE hmesi  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)



lemma "HSTATE_general_rule_9_flipped_1":
  shows "HSTATE hmesi  ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)

lemma "HSTATE_general_rule_10_flipped_1":
  shows "HSTATE hmesi  ( T [ -=i 1]) = HSTATE hmesi  T"
  by (cases "program2 T", simp+)

\<comment>\<open>snps1 general \<close>
lemma "snps1_general_rule_1_0":
  shows "snps1  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_2_0":
  shows "snps1  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_3_0":
  shows "snps1  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_4_0":
  shows "snps1  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_5_0":
  shows "snps1  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_6_0":
  shows "snps1  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_7_0":
  shows "snps1  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_8_0":
  shows "snps1  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = snps1  T "
  by (cases "program1 T", simp+)


lemma "snps1_general_rule_10_0":
  shows "snps1  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_11_0":
  shows "snps1  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps1  T "
  by (cases "program1 T", simp+)

lemma "snps1_general_rule_12_0":
  shows "snps1  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ])  = snps1  T "
  by (cases "program1 T", simp+)



lemma "snps1_general_rule_14_0":
  shows "snps1  ( T [ -=i 0])  = snps1  T "
  by (cases "program1 T", simp+)



lemma "snps1_general_rule_1_flipped_1":
  shows "snps1  ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_2_flipped_1":
  shows "snps1  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_3_flipped_1":
  shows "snps1  ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_4_flipped_1":
  shows "snps1  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_5_flipped_1":
  shows "snps1  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_6_flipped_1":
  shows "snps1  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_7_flipped_1":
  shows "snps1  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_8_flipped_1":
  shows "snps1  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = snps1  T"
  by (cases "program2 T", simp+)



lemma "snps1_general_rule_10_flipped_1":
  shows "snps1  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_11_flipped_1":
  shows "snps1  ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps1  T"
  by (cases "program2 T", simp+)

lemma "snps1_general_rule_12_flipped_1":
  shows "snps1  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = snps1  T"
  by (cases "program2 T", simp+)



lemma "snps1_general_rule_14_flipped_1":
  shows "snps1  ( T [ -=i 1]) = snps1  T"
  by (cases "program2 T", simp+)


lemma "snps2_general_rule_1_0":
  shows "snps2  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_2_0":
  shows "snps2  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_3_0":
  shows "snps2  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_4_0":
  shows "snps2  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_5_0":
  shows "snps2  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_6_0":
  shows "snps2  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_7_0":
  shows "snps2  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_8_0":
  shows "snps2  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = snps2  T "
  by (cases "program1 T", simp+)


lemma "snps2_general_rule_10_0":
  shows "snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_11_0":
  shows "snps2  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_12_0":
  shows "snps2  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_13_0":
  shows "snps2  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_14_0":
  shows "snps2  ( T [ -=i 0])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_15_0":
  shows "snps2  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ])  = snps2  T "
  by (cases "program1 T", simp+)

lemma "snps2_general_rule_1_flipped_1":
  shows "snps2  ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_2_flipped_1":
  shows "snps2  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_3_flipped_1":
  shows "snps2  ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_4_flipped_1":
  shows "snps2  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_5_flipped_1":
  shows "snps2  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_6_flipped_1":
  shows "snps2  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_7_flipped_1":
  shows "snps2  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_8_flipped_1":
  shows "snps2  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_9_flipped_1":
  shows "snps2  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_10_flipped_1":
  shows "snps2  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_11_flipped_1":
  shows "snps2  ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) = snps2  T"
  by (cases "program2 T", simp+)

lemma "snps2_general_rule_12_flipped_1":
  shows "snps2  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = snps2  T"
  by (cases "program2 T", simp+)



lemma "snps2_general_rule_14_flipped_1":
  shows "snps2  ( T [ -=i 1]) = snps2  T"
  by (cases "program2 T", simp+)

\<comment>\<open>snps minus empty \<close>
lemma "snps1_minus_empty_rule_1_0":
  shows "length (snps1 T) <= 1 --> snps1  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])  = []"
  by (cases "snps1 T", simp+)

lemma "snps1_minus_empty_rule_2_0":
  shows "length (snps1 T) <= 1 --> snps1  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd])  = []"
  by (cases "snps1 T", simp+)

lemma "snps2_minus_empty_rule_1_flipped_1":
  shows "length (snps2 T) <= 1 --> snps2 ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = []"
  by (cases "snps2 T", simp+)

lemma "snps2_minus_empty_rule_2_flipped_1":
  shows "length (snps2 T) <= 1 --> snps2 ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) = []"
  by (cases "snps2 T", simp+)

\<comment>\<open>snps minus not nextSnoopIs \<close>
lemma "snps1_minus_not_nextSnoopIs_rule_1_0":
  shows "length (snps1 T) <= 1 --> \<not> nextSnoopIs snpt  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0"
  by (cases "snps1 T", simp+)

lemma "snps1_minus_not_nextSnoopIs_rule_2_0":
  shows "length (snps1 T) <= 1 --> \<not> nextSnoopIs snpt  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "snps1 T", simp+)

lemma "snps2_minus_not_nextSnoopIs_rule_1_flipped_1":
  shows "length (snps2 T) <= 1 --> \<not> nextSnoopIs snpt ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1"
  by (cases "snps2 T", simp+)

lemma "snps2_minus_not_nextSnoopIs_rule_2_flipped_1":
  shows "length (snps2 T) <= 1 --> \<not> nextSnoopIs snpt ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "snps2 T", simp+)


\<comment>\<open>snps empty not nextSnoopPending\<close>
lemma "snps1_empty_not_nextSnoopIs_rule_1_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_2_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_3_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_4_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_5_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_6_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_7_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_8_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_9_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_10_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_11_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_12_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_13_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_14_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_15_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_16_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ -=i 0]) 0"
  by (cases "program1 T", simp+)

lemma "snps1_empty_not_nextSnoopIs_rule_17_0":
  shows "snps1 T = [] --> \<not> nextSnoopIs snpt  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ]) 0"
  by (cases "program1 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_1_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_2_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_3_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_4_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_5_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_6_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_7_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_8_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_9_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_10_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_11_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_12_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_13_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) 1"
  by (cases "program2 T", simp+)



lemma "snps2_empty_not_nextSnoopIs_rule_15_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "program2 T", simp+)

lemma "snps2_empty_not_nextSnoopIs_rule_16_flipped_1":
  shows " (snps2 T) = [] --> \<not> nextSnoopIs snpt ( T [ -=i 1]) 1"
  by (cases "program2 T", simp+)


\<comment>\<open>dthdatas1 general \<close>
lemma "dthdatas1_general_rule_1_0":
  shows "dthdatas1  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_2_0":
  shows "dthdatas1  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_3_0":
  shows "dthdatas1  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_4_0":
  shows "dthdatas1  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_5_0":
  shows "dthdatas1  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_6_0":
  shows "dthdatas1  ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_7_0":
  shows "dthdatas1  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_8_0":
  shows "dthdatas1  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_9_0":
  shows "dthdatas1  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_10_0":
  shows "dthdatas1  ( T [ -=i 0])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_11_0":
  shows "dthdatas1  ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ])  = dthdatas1  T "
  by (cases "program1 T", simp+)

lemma "dthdatas1_general_rule_12_0":
  shows "dthdatas1  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ])  = dthdatas1  T "
  by (cases "program1 T", simp+)



lemma "dthdatas1_general_rule_1_flipped_1":
  shows "dthdatas1  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_2_flipped_1":
  shows "dthdatas1  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_3_flipped_1":
  shows "dthdatas1  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_4_flipped_1":
  shows "dthdatas1  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_5_flipped_1":
  shows "dthdatas1  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_6_flipped_1":
  shows "dthdatas1  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_7_flipped_1":
  shows "dthdatas1  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_8_flipped_1":
  shows "dthdatas1  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_9_flipped_1":
  shows "dthdatas1  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_10_flipped_1":
  shows "dthdatas1  ( T [ -=i 1]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_11_flipped_1":
  shows "dthdatas1  ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

lemma "dthdatas1_general_rule_12_flipped_1":
  shows "dthdatas1  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) = dthdatas1  T"
  by (cases "program2 T", simp+)

\<comment>\<open>CXL_SPG_used general\<close>
lemma "CXL_SPG_used_general_rule_1_0":
  shows "CXL_SPG_used ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_2_0":
  shows "CXL_SPG_used ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_3_0":
  shows "CXL_SPG_used ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_4_0":
  shows "CXL_SPG_used ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_5_0":
  shows "CXL_SPG_used ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_6_0":
  shows "CXL_SPG_used ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_7_0":
  shows "CXL_SPG_used ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_8_0":
  shows "CXL_SPG_used ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_9_0":
  shows "CXL_SPG_used ( T [ -=i 0]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_10_0":
  shows "CXL_SPG_used ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_11_0":
  shows "CXL_SPG_used ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = CXL_SPG_used T i"
  by (cases "program1 T", simp+)

lemma "CXL_SPG_used_general_rule_1_flipped_1":
  shows "CXL_SPG_used ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_2_flipped_1":
  shows "CXL_SPG_used ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_3_flipped_1":
  shows "CXL_SPG_used ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_4_flipped_1":
  shows "CXL_SPG_used ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_5_flipped_1":
  shows "CXL_SPG_used ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_6_flipped_1":
  shows "CXL_SPG_used ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_7_flipped_1":
  shows "CXL_SPG_used ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_8_flipped_1":
  shows "CXL_SPG_used ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_9_flipped_1":
  shows "CXL_SPG_used ( T [ -=i 1]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_10_flipped_1":
  shows "CXL_SPG_used ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)

lemma "CXL_SPG_used_general_rule_11_flipped_1":
  shows "CXL_SPG_used ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = CXL_SPG_used T i"
  by (cases "program2 T", simp+)
\<comment>\<open>nextLoad general\<close>
lemma "nextLoad_general_rule_1_0":
  shows "nextLoad  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_2_0":
  shows "nextLoad  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_3_0":
  shows "nextLoad  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_4_0":
  shows "nextLoad  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_5_0":
  shows "nextLoad  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_6_0":
  shows "nextLoad  ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_7_0":
  shows "nextLoad  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_8_0":
  shows "nextLoad  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_9_0":
  shows "nextLoad  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_10_0":
  shows "nextLoad  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_11_0":
  shows "nextLoad  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_12_0":
  shows "nextLoad  ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)

lemma "nextLoad_general_rule_13_0":
  shows "nextLoad  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = nextLoad  T i"
  by (cases "program1 T", simp+)


lemma "nextLoad_general_rule_1_flipped_1":
  shows "nextLoad  ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_2_flipped_1":
  shows "nextLoad  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_3_flipped_1":
  shows "nextLoad  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_4_flipped_1":
  shows "nextLoad  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_5_flipped_1":
  shows "nextLoad  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_6_flipped_1":
  shows "nextLoad  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_7_flipped_1":
  shows "nextLoad  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_8_flipped_1":
  shows "nextLoad  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_9_flipped_1":
  shows "nextLoad  ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_10_flipped_1":
  shows "nextLoad  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_11_flipped_1":
  shows "nextLoad  ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_12_flipped_1":
  shows "nextLoad  ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

lemma "nextLoad_general_rule_13_flipped_1":
  shows "nextLoad  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = nextLoad  T i"
  by (cases "program2 T", simp+)

\<comment>\<open>nextStore general\<close>
lemma "nextStore_general_rule_1_0":
  shows "nextStore  ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_2_0":
  shows "nextStore  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_3_0":
  shows "nextStore  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_4_0":
  shows "nextStore  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_5_0":
  shows "nextStore  ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_6_0":
  shows "nextStore  ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_7_0":
  shows "nextStore  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_8_0":
  shows "nextStore  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_9_0":
  shows "nextStore  ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_10_0":
  shows "nextStore  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_11_0":
  shows "nextStore  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_12_0":
  shows "nextStore  ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_13_0":
  shows "nextStore  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_14_0":
  shows "nextStore  ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi txid] [ 0 -=req ]) i = nextStore  T i"
  by (cases "program1 T", simp+)

lemma "nextStore_general_rule_1_flipped_1":
  shows "nextStore  ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_2_flipped_1":
  shows "nextStore  ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_3_flipped_1":
  shows "nextStore  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_4_flipped_1":
  shows "nextStore  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_5_flipped_1":
  shows "nextStore  ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_6_flipped_1":
  shows "nextStore  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_7_flipped_1":
  shows "nextStore  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_8_flipped_1":
  shows "nextStore  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_9_flipped_1":
  shows "nextStore  ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_10_flipped_1":
  shows "nextStore  ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_11_flipped_1":
  shows "nextStore  ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_12_flipped_1":
  shows "nextStore  ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

lemma "nextStore_general_rule_13_flipped_1":
  shows "nextStore  ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = nextStore  T i"
  by (cases "program2 T", simp+)

\<comment>\<open>lastSharer non-Invalid state changes equality\<close>
lemma "lastSharer_non_Invalid_rule_1_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_2_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_3_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_4_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_5_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_6_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_7_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state])  = lastSharer  T "
  by (cases "program1 T", simp+)



lemma "lastSharer_non_Invalid_rule_9_0":
  shows "CSTATE X T 0 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd])  = lastSharer  T "
  by (cases "program1 T", simp+)

lemma "lastSharer_non_Invalid_rule_1_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_2_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_3_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_4_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_5_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_6_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) = lastSharer  T"
  by (cases "program2 T", simp+)

lemma "lastSharer_non_Invalid_rule_7_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) = lastSharer  T"
  by (cases "program2 T", simp+)


lemma "lastSharer_non_Invalid_rule_9_flipped_1":
  shows "CSTATE X T 1 \<and> X \<noteq> Invalid \<and> mesi_state \<noteq> Invalid --> lastSharer  ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) = lastSharer  T"
  by (cases "program2 T", simp+)



\<comment>\<open>reqs1 empty no Pending\<close>
lemma "reqs1_empty_not_nextReqIs_general_invariant":
  shows "reqs1 T = [] --> \<not> nextReqIs reqt T 0"
  by (cases "program1 T", simp+)

lemma "reqs2_empty_not_nextReqIs_general_invariant":
  shows " (reqs2 T) = [] --> \<not> nextReqIs reqt T 1"
  by (cases "program2 T", simp+)

\<comment>\<open>snpresps1 minus empty \<close>
lemma "snpresps1_minus_empty_rule_1_0":
  shows "length (snpresps1 T) <= 1 --> snpresps1  ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ])  = []"
  by (cases "snpresps1 T", simp+)

lemma "snpresps2_minus_empty_rule_1_flipped_1":
  shows "length (snpresps2 T) <= 1 --> snpresps2 ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) = []"
  by (cases "snpresps2 T", simp+)










\<comment>\<open>helper for all giant lemmas\<close>
lemma general_helper: "P \<Longrightarrow> (Q = Q') \<Longrightarrow> T1 = T2 \<Longrightarrow>
    (
        P \<and> Q \<Longrightarrow>
        f T2) \<Longrightarrow>
    Lall
     (if Q'
      then [T1]
      else [])
     f "
  by (metis Lall.simps(1) Lall.simps(2) insert_Nil)



\<comment>\<open>nextDTHDataPending general\<close>
lemma "nextDTHDataPending_general_rule_1_0":
  shows "nextDTHDataPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ -=i 0]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_2_0":
  shows "nextDTHDataPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_3_0":
  shows "nextDTHDataPending ( T [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_4_0":
  shows "nextDTHDataPending ( T [ 0 +=rdreq rdx] [ 0 s= mesi_state]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_5_0":
  shows "nextDTHDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=reqresp gox mesi_state txid] [ 0 -=req ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_6_0":
  shows "nextDTHDataPending ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_7_0":
  shows "nextDTHDataPending ( T [ 1 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 0 -=snpresp  ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_8_0":
  shows "nextDTHDataPending ( T [ -=i 0]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_9_0":
  shows "nextDTHDataPending ( T [ 1 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 0 -=req ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_general_rule_10_0":
  shows "nextDTHDataPending ( T [ 0 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=snp snpx txid]  [ 0 -=req ]) i = nextDTHDataPending T i"
  by (cases "program1 T", simp+)



lemma "nextDTHDataPending_general_rule_1_flipped_1":
  shows "nextDTHDataPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ -=i 1]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_2_flipped_1":
  shows "nextDTHDataPending ( T \<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_3_flipped_1":
  shows "nextDTHDataPending ( T [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_4_flipped_1":
  shows "nextDTHDataPending ( T [ 1 +=rdreq rdx] [ 1 s= mesi_state]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_5_flipped_1":
  shows "nextDTHDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 1 +=reqresp gox mesi_state txid] [ 1 -=req ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_6_flipped_1":
  shows "nextDTHDataPending ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_7_flipped_1":
  shows "nextDTHDataPending ( T [ 0 +=reqresp gox mesi_state txid] [ 5 sHost= hmesi_state] [ 1 -=snpresp  ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_8_flipped_1":
  shows "nextDTHDataPending ( T [ -=i 1]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_9_flipped_1":
  shows "nextDTHDataPending ( T [ 0 +=snp snpx txid]  [ 5 sHost= hmesi_state] [ 1 -=req ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_general_rule_10_flipped_1":
  shows "nextDTHDataPending ( T [ 1 +=hostdata  txid] [ 5 sHost= hmesi_state] [ 0 +=snp snpx txid]  [ 1 -=req ]) i = nextDTHDataPending T i"
  by (cases "program2 T", simp+)

\<comment>\<open>DTHDataPending otherside \<close>

lemma "nextDTHDataPending_other_rule_1_0":
  shows "nextDTHDataPending ( T [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_2_0":
  shows "nextDTHDataPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_3_0":
  shows "nextDTHDataPending ( T\<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd] [ -=i 0]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_4_0":
  shows "nextDTHDataPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ]  [ 0 -=devd ]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_5_0":
  shows "nextDTHDataPending ( T [ 0 s= mesi_state] [ 0 :=dd msg ] [ -=i 0] [ 0 -=devd ]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_6_0":
  shows "nextDTHDataPending ( T [ Dev2 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev1 -=d2hdHead ]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_7_0":
  shows "nextDTHDataPending ( T \<lparr>buffer1 := om\<rparr> [ 0 s= mesi_state] [ 0 -=reqresp ] [ Dev1 +=d2hd dthd][ -=i 0]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_8_0":
  shows "nextDTHDataPending ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 1 = nextDTHDataPending T 1"
  by (cases "program1 T", simp+)

lemma "nextDTHDataPending_other_rule_1_flipped_1":
  shows "nextDTHDataPending ( T [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_other_rule_2_flipped_1":
  shows "nextDTHDataPending ( T [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_other_rule_3_flipped_1":
  shows "nextDTHDataPending ( T\<lparr>buffer2 := om\<rparr> [ 1 s= mesi_state] [ 1 -=reqresp ] [ Dev2 +=d2hd dthd] [ -=i 1]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_other_rule_4_flipped_1":
  shows "nextDTHDataPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ]  [ 1 -=devd ]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_other_rule_5_flipped_1":
  shows "nextDTHDataPending ( T [ 1 s= mesi_state] [ 1 :=dd msg ] [ -=i 1] [ 1 -=devd ]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

lemma "nextDTHDataPending_other_rule_6_flipped_1":
  shows "nextDTHDataPending ( T [ Dev1 +=h2dd hmsg] [ =hv v] [ 5 sHost= hmesi_state] [ Dev2 -=d2hdHead ]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)



lemma "nextDTHDataPending_other_rule_8_flipped_1":
  shows "nextDTHDataPending ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 0 = nextDTHDataPending T 0"
  by (cases "program2 T", simp+)

\<comment>\<open>snpresps1/2 empty plus eq/neq\<close>
lemma "snpresps1_empty_plus_neq_a_rule_1_0":
  shows " (snpresps1 T) = [] --> nextSnpRespIs rspx  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0"
  by (cases "snpresps1 T", simp+)

lemma "snpresps1_empty_plus_neq_a_rule_2_0":
  shows " (snpresps1 T) = [] --> nextSnpRespIs rspx  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "snpresps1 T", simp+)

lemma "snpresps2_empty_plus_neq_a_rule_1_flipped_1":
  shows " (snpresps2 T) = [] --> nextSnpRespIs rspx ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1"
  by (cases "snpresps2 T", simp+)

lemma "snpresps2_empty_plus_neq_a_rule_2_flipped_1":
  shows " (snpresps2 T) = [] --> nextSnpRespIs rspx ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "snpresps2 T", simp+)



lemma "snpresps1_empty_plus_neq_b_rule_1_0":
  shows "rspx1 \<noteq> rspx \<and> (snpresps1 T) = [] --> \<not> nextSnpRespIs rspx1  ( T\<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx tid] [0 -=snp ] [ 0 s= mesi_state]) 0"
  by (cases "snpresps1 T", simp+)

lemma "snpresps1_empty_plus_neq_b_rule_2_0":
  shows "rspx1 \<noteq> rspx \<and> (snpresps1 T) = [] --> \<not> nextSnpRespIs rspx1  ( T \<lparr>buffer1 := om\<rparr> [0 +=snpresp rspx txid] [0 -=snp ] [ 0 s= mesi_state] [ Dev1 +=d2hd dthd]) 0"
  by (cases "snpresps1 T", simp+)

lemma "snpresps2_empty_plus_neq_b_rule_1_flipped_1":
  shows "rspx1 \<noteq> rspx \<and> (snpresps2 T) = [] --> \<not> nextSnpRespIs rspx1 ( T\<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx tid] [1 -=snp ] [ 1 s= mesi_state]) 1"
  by (cases "snpresps2 T", simp+)

lemma "snpresps2_empty_plus_neq_b_rule_2_flipped_1":
  shows "rspx1 \<noteq> rspx \<and> (snpresps2 T) = [] --> \<not> nextSnpRespIs rspx1 ( T \<lparr>buffer2 := om\<rparr> [1 +=snpresp rspx txid] [1 -=snp ] [ 1 s= mesi_state] [ Dev2 +=d2hd dthd]) 1"
  by (cases "snpresps2 T", simp+)































end
