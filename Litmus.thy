theory Litmus imports BuggyRules
begin
\<comment>\<open>Scenario verifications, We have allTransitions, which are core transitions we also include for formal proofs.
For Snoop-pushes-GO or GO-not-before-snoop-returns, we need another set of rules we call "liberal" so these restrictions
do become the last safeguard before a coherence violation.

\<close>

definition SWMR_p :: "Type1State \<Rightarrow> bool" where [simp]: 
  "SWMR_p T = ( (CSTATE Modified T 0 \<longrightarrow>  \<not> CSTATE Shared T 1) \<and>  
              (CSTATE Modified T 1 \<longrightarrow>  \<not> CSTATE Shared T 0) \<and> 
              (CSTATE Modified T 0 \<longrightarrow> \<not>CSTATE Modified T 1) \<and>
              (CSTATE Modified T 1 \<longrightarrow> \<not>CSTATE Modified T 0) )"

value "SWMR_p  \<lparr>hostcache = \<lparr>HostEntry.content = Some 0, block_state = ModifiedM\<rparr>,
      devcache1 = \<lparr>CLEntry.content = Some 0, block_state = Modified\<rparr>,
      devcache2 = \<lparr>CLEntry.content = Some 0, block_state = Modified\<rparr>, reqs1 = [], reqs2 = [], snpresps1 = [], snpresps2 = [],
      dthdatas1 = [], dthdatas2 = [], snps1 = [], snps2 = [], reqresps1 = [], reqresps2 = [], htddatas1 = [], htddatas2 = [],
      program1 = [], program2 = [], counter = 4, registers11 = 0, registers12 = 0, registers21 = 0, registers22 = 0,
      clock = 21, buffer1 = Some (H2DResp (Utid 2) GO Modified 16), buffer2 = Some (H2DResp (Utid 3) GO Modified 17)\<rparr>"
 fun list_prop_exists :: "'a list \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "list_prop_exists [] p  = False"
| "list_prop_exists (a # as) p = (if p a then True else  list_prop_exists as p)"
definition "true_MESI_violation T = (\<not> SWMR_p T)"






definition "InvalidSnpDataLiberal' T i = (if ( CSTATE Invalid T i \<and> nextSnoopIs SnpData T i \<and> CXL_SPG_used T i) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI Invalid i T] else [] )"
definition "InvalidSnpDataLiberal T i = map update_clock (InvalidSnpDataLiberal' T i)"
  
definition "InvalidSnpInvLiberal' T i = (if ( CSTATE Invalid T i \<and> nextSnoopIs SnpInv T i \<and> CXL_SPG_used T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI Invalid i T] else [] )"
definition "InvalidSnpInvLiberal T i = map update_clock (InvalidSnpInvLiberal' T i)"

definition "IMADSnpDataLiberal' T i = (if ( CSTATE IMAD T i \<and> nextSnoopIs SnpData T i  \<and> CXL_SPG_used T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI IMAD i T] else [] )"
definition "IMADSnpDataLiberal T i = map update_clock (IMADSnpDataLiberal' T i)"


definition "IMADSnpInvLiberal' T i = (if ( CSTATE IMAD T i \<and> nextSnoopIs SnpInv T i  \<and> CXL_SPG_used T i) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI IMAD i T] else [] )"
definition "IMADSnpInvLiberal T i = map update_clock (IMADSnpInvLiberal' T i)"

definition "ISADSnpDataLiberal' T i = (if ( CSTATE ISAD T i \<and> nextSnoopIs SnpData T i  \<and> CXL_SPG_used T i) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI ISAD i T] else [] )"
definition "ISADSnpDataLiberal T i = map update_clock (ISADSnpDataLiberal' T i)"

definition "ISADSnpInvLiberal' T i = (if ( CSTATE ISAD T i \<and> nextSnoopIs SnpInv T i  \<and> CXL_SPG_used T i) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI ISAD i T] else [] )"
definition "ISADSnpInvLiberal T i = map update_clock (ISADSnpInvLiberal' T i)"


definition "HostSADRspIHitILiberal' T i = (if ( HSTATE SAD T  \<and> nextSnpRespIs RspIHitI T i \<and> GTS T i ) then 
  [clearBuffer (sendGOFromSnpRespForwardData  (nextSnoopRespID T i) i Shared GO SharedM T) ] else [] )"
definition "HostSADRspIHitILiberal T i = map update_clock (HostSADRspIHitILiberal' T i)"
definition noMultiSnoops :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where "noMultiSnoops T i = (if i = 0 then snps1 T = [] else snps2 T = [])"

\<comment>\<open>This rule also violates Data-GO atomicity and no multiple-snoops rule\<close>
definition "HostMARdOwnLiberal' T i = (if ( HSTATE MA T  \<and> nextReqIs RdOwn T i \<and> noMultiSnoops T i ) then 
  [clearBuffer (sendSnoop SnpInv i MA T) ] else [] )"
definition "HostMARdOwnLiberal T i = map update_clock (HostMARdOwnLiberal' T i)"

\<comment>\<open>end of SPG-vioating rules\<close>

\<comment>\<open>For GTS violation rules\<close>


\<comment>\<open>Rule allows the final phase of getting from a GTS violation to MESI violation
20240126\<close>
definition "HostModifiedRspIHitILiberal' T i = (if HSTATE ModifiedM T \<and> nextSnpRespIs RspIHitI T i \<and> GTS T i
  then [ clearBuffer (sendGOFromSnpRespForwardData  (nextSnoopRespID T i) i Modified GO ModifiedM T) ] else [])" 

definition "HostSADRspIFwdMLiberal' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [ clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 


definition "HostSADRspSFwdMLiberal' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T i \<and> GTS T i
  then [clearBuffer ( sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 
definition "HostMADRspIFwdMLiberal' T i = (if HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO MD T)  ] else [])"

definition "HostMARspIFwdMLiberal' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"
\<comment>\<open>TODO: need to add SAD --> SA where data is processed first
\<close>

definition "HostSARspIFwdMLiberal' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"
definition "HostSARspSFwdMLiberal' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspSFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"


\<comment>\<open>Sent in case a dirtyevict was serialised before (interrupted by) a RdOwn\<close>
definition "HostMADDirtyEvictLiberal' T i = (if HSTATE MAD T \<and> nextReqIs DirtyEvict  T i \<and> GTS T ((i+1) mod 2)
  then  [ clearBuffer (sendEvictResp GO_WritePull i MAD (nextReqID T i) T )]  else [])"

\<comment>\<open>Might happen if snoop arrives after device started DEvict, but that DEvict reached Host after the snoop's data  arrived\<close>
definition "HostMADirtyEvictLiberal' T i = (if HSTATE MA T \<and> nextReqIs DirtyEvict  T i  \<and> GTS T ((i+1) mod 2) 
  then  [ clearBuffer (sendEvictResp GO_WritePull i MA (nextReqID T i) T) ]  else [])"

\<comment>\<open>Might happen if snoop arrives after device started DEvict, but that DEvict reached Host after the snoop's  response arrived \<close>
definition "HostMDDirtyEvictLiberal' T i = (if HSTATE MD T \<and> nextReqIs DirtyEvict  T i  \<and> GTS T ((i+1) mod 2)
  then  [ clearBuffer (sendEvictResp GO_WritePull i MD (nextReqID T i) T) ]  else [])"

\<comment>\<open>Rule allows GTS violation if the other device has an unreturned snoop
20240126\<close>
definition "HostMARspIHitSELiberal' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIHitSE T i \<and> GTS T ((i+1) mod 2)
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"


definition "HostSADRspIFwdMLiberal T i = map update_clock (HostSADRspIFwdMLiberal' T i)"
definition "HostSADRspSFwdMLiberal T i = map update_clock (HostSADRspSFwdMLiberal' T i)"
definition "HostMADRspIFwdMLiberal T i = map update_clock (HostMADRspIFwdMLiberal' T i)"
definition "HostMARspIFwdMLiberal T i = map update_clock (HostMARspIFwdMLiberal' T i)"
definition "HostSARspIFwdMLiberal T i = map update_clock (HostSARspIFwdMLiberal' T i)"
definition "HostSARspSFwdMLiberal T i = map update_clock (HostSARspSFwdMLiberal' T i)"
definition "HostMADDirtyEvictLiberal T i = map update_clock (HostMADDirtyEvictLiberal' T i)"
definition "HostMADirtyEvictLiberal T i = map update_clock (HostMADirtyEvictLiberal' T i)"
definition "HostMDDirtyEvictLiberal T i = map update_clock (HostMDDirtyEvictLiberal' T i)"
definition "HostModifiedRspIHitILiberal T i = map update_clock (HostModifiedRspIHitILiberal' T i)"
definition "HostMARspIHitSELiberal T i = map update_clock (HostMARspIHitSELiberal' T i)"

\<comment>\<open>end of GTS-vioating rules\<close>


definition LiberalTransitions_SPG :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "LiberalTransitions_SPG = [
InvalidSnpDataLiberal,                  
InvalidSnpInvLiberal,                    
IMADSnpDataLiberal,                     
IMADSnpInvLiberal,                     
ISADSnpInvLiberal,
ISADSnpDataLiberal,
HostSADRspIHitILiberal,
HostMARdOwnLiberal                
]
  "


definition LiberalTransitions_GTS :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "LiberalTransitions_GTS = [
HostSADRspIFwdMLiberal,                  
HostSADRspSFwdMLiberal,
HostMADRspIFwdMLiberal,
HostMARspIFwdMLiberal,
HostSARspIFwdMLiberal,
HostSARspSFwdMLiberal,
HostMADDirtyEvictLiberal,
HostMADirtyEvictLiberal,
HostMDDirtyEvictLiberal,
HostModifiedRspIHitILiberal,
HostMARspIHitSELiberal      
]"


definition "LiberalTransitions = LiberalTransitions_SPG @ LiberalTransitions_GTS "
                                                                            

definition "LiberalGood = allTransitions @ LiberalTransitions"

definition "reallyBad = allTransitions @ badTransitions"

definition onestep_liberal :: "Type1State \<Rightarrow> Type1State list"
where
   "onestep_liberal T = (concat (map (\<lambda>f. (f T 0 @ f T 1)) LiberalGood))"

definition "chain_of_liberal_good_states Tlist  Plist =   (mfold (\<lambda>Tl P.  (filter P (concat (map onestep_liberal Tl))) ) Tlist Plist) "


definition "allTrue = (\<lambda>T. True)"

definition snoop_pushes_GO_config :: "Type1State"
  where 
  "snoop_pushes_GO_config = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = \<lparr>CLEntry.content = None, CLEntry.block_state = Invalid\<rparr>, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Write  1],
    program2                     = [Read  2],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None


  \<rparr>"




definition SPG_vio1 :: "Type1State \<Rightarrow> bool" where  "SPG_vio1 T = messageAtLast (\<lambda>m. getSpecificTypeReq m = RdShared) (reqs2 T)"

definition "SPG_vio2 T = 
  (messageAtLast (\<lambda>m. getSpecificTypeReq m = RdShared) (reqs2 T) \<and> 
    messageAtLast (\<lambda>m. getSpecificTypeReq m = RdOwn) (reqs1 T))"

definition "SPG_vio3 T =   
  (messageAtLast (\<lambda>m. getSpecificTypeReq m = RdShared) (reqs2 T) \<and> 
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps1 T) \<and>
    block_state (hostcache T) = ModifiedM)"


definition "SPG_vio4 T = 
  ( (buffer1 T) = None \<and>
    messageAtLast (\<lambda>m. getSpecificTypeSnoop m = SnpData) (snps1 T) \<and> 
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps1 T) \<and>
    block_state (hostcache T) = SAD)"


definition "SPG_vio5 T = 
  ( bufferType SnpData (buffer1 T)  \<and> 
    messageAtLast (\<lambda>m. getSpecificTypeSnpResp m = RspIHitI) (snpresps1 T) \<and>
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps1 T) \<and>
    block_state (hostcache T) = SAD \<and>
    CLEntry.block_state (devcache1 T) = IMAD)"

definition "SPG_vio6 T = 
  ( (buffer2 T) = None  \<and> 
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps1 T) \<and>
    \<comment>\<open>messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps2 T) \<and>\<close>
    CLEntry.block_state (devcache1 T) = IMAD)"

definition "SPG_vio7 T = 
  (  
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps2 T) \<and>
    CLEntry.block_state (devcache1 T) = IMD)"

definition "SPG_vio8 T = 
  (  
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps2 T) \<and>
    CLEntry.block_state (devcache1 T) = Modified \<and>
    CLEntry.block_state (devcache2 T) = ISAD )"

definition "SPG_vio9 T = 
  (  
    
    CLEntry.block_state (devcache1 T) = Modified \<and>
    CLEntry.block_state (devcache2 T) = ISD)"

definition "SPG_vio10 T = 
  (  
    
    CLEntry.block_state (devcache1 T) = Modified \<and>
    CLEntry.block_state (devcache2 T) = Shared)"



definition "SPG_violation_sequence =  [SPG_vio1, SPG_vio2, SPG_vio3, SPG_vio4, SPG_vio5, SPG_vio6, SPG_vio7, SPG_vio8, SPG_vio9, SPG_vio10]"

definition "spg_chain = chain_of_states [snoop_pushes_GO_config] SPG_violation_sequence"
definition "spg_chain_liberal = chain_of_liberal_good_states [snoop_pushes_GO_config] SPG_violation_sequence"
definition "spg_chain_bad = chain_of_bad_states [snoop_pushes_GO_config] SPG_violation_sequence"
\<comment>\<open>definition "Config10_satisifies_mesi_violation = (chain_reachable_option_with_final (Some snoop_pushes_GO_config) 
  [SPG_vio1, SPG_vio2, SPG_vio3, SPG_vio4, SPG_vio5, SPG_vio6, SPG_vio7, SPG_vio8, SPG_vio9, SPG_vio10] true_MESI_violation)"
\<close>
value " spg_chain"
value "spg_chain_liberal"
value "spg_chain_bad"


value "list_prop_exists (concat spg_chain) (\<lambda>T. \<not> SWMR_state_machine T)"
value "list_prop_exists (concat spg_chain_liberal) (\<lambda>T. \<not> SWMR_state_machine T)"
value "list_prop_exists (concat spg_chain_bad) (\<lambda>T. \<not> SWMR_state_machine T)"

definition "tree_violations (Tss) = list_prop_exists (concat Tss) true_MESI_violation"



fun unprunedN :: "nat \<Rightarrow> (Type1State \<Rightarrow> bool) list" where
  "unprunedN 0 = []"
| "unprunedN (Suc n) = allTrue # unprunedN n"
 (*a write and a read successfully complete *)
definition "write_and_read = chain_of_states [snoop_pushes_GO_config] (unprunedN 11)"

value "write_and_read"
value "tree_violations write_and_read"

definition mevicts :: "Type1State"
  where 
  "mevicts = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = SharedM\<rparr>,
    Type1State.devcache1         = \<lparr>CLEntry.content = Some 0, CLEntry.block_state = Shared\<rparr>,
    Type1State.devcache2         = \<lparr>CLEntry.content = Some 0, CLEntry.block_state = Shared\<rparr>, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Evict, Evict, Evict, Evict],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*multiple evicts *)
definition "mevicts_tree = chain_of_states [mevicts] (unprunedN 11)"

value "mevicts_tree"



definition mreads :: "Type1State"
  where 
  "mreads = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Read 1, Read 1, Read 1, Read 1],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*multiple evicts *)
definition "mreads_tree = chain_of_states [mreads] (unprunedN 11)"

value "mreads_tree"


definition mwrites :: "Type1State"
  where 
  "mwrites = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Write 3, Write 3, Write 3, Write 3],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*multiple evicts *)
definition "mwrites_tree = chain_of_states [mwrites] (unprunedN 11)"

value "mwrites_tree"


definition alternating :: "Type1State"
  where 
  "alternating = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Read 1, Write 3, Evict, Write 3],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*multiple evicts *)
definition "alternating_tree = chain_of_states [alternating] (unprunedN 18)"

value "alternating_tree"

definition two_sides_alternating :: "Type1State"
  where 
  "two_sides_alternating = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = InvalidM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Read 1,  Write 3],
    program2                     = [Write 3, Read 1],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*multiple evicts *)
definition "two_sides_alternating_tree = chain_of_states [two_sides_alternating] (unprunedN 3)"

value "two_sides_alternating_tree"

definition GTSConfig :: "Type1State"
  where 
  "GTSConfig = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = SharedM\<rparr>,
    Type1State.devcache1         = empty_entry,
    Type1State.devcache2         = \<lparr>CLEntry.content = Some 0, CLEntry.block_state = Shared\<rparr>, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Write  1],
    program2                     = [Write  2],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"


(*cheesy written predicates, need debugging
definition GTS_legal1 :: "Type1State \<Rightarrow> bool" where  
  "GTS_legal1 T = messageAtLast (\<lambda>m. getSpecificTypeReq m = RdOwn) (reqs2 T)"



definition "GTS_legal2 T = 
  (( messageAtLast (\<lambda>m. getSpecificTypeSnoop m = SnpInv) (snps1 T))
    )"

\<comment>\<open> RdOwn from D2 is serviced first, therefore RdOwn from D1 remains
A data has been sent to D2, a SnpInv sent to D1\<close>
definition "GTS_legal3 T =   
  ( messageAtLast (\<lambda>m. getSpecificTypeReq m = RdOwn) (reqs1 T))"


\<comment>\<open>  D1 processed SnpInv, downgraded from SMAD to IMAD, sent RspIHitSE \<close>
definition "GTS_legal4 T = 
  ( bufferType SnpInv (buffer1 T)  \<comment>\<open> \<and>
    messageAtLast (\<lambda>m. getSpecificTypeSnpResp m = RspIHitSE) (snpresps1 T) \<and> 
    CLEntry.block_state (devcache1 T) = IMAD \<and>
    block_state (hostcache T) = MA\<close>)"

\<comment>\<open> Host sees RspIHitSE from D1, sent GO-M to D2 \<close>
definition "GTS_legal5 T = 
  (  
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps2 T) \<and>
    block_state (hostcache T) = MA \<and>
    CLEntry.block_state (devcache1 T) = IMAD)"


\<comment>\<open>  GO-M to D2 consumed \<close>
definition "GTS_legal5_0 T = 
  ( 
    block_state (hostcache T) = ModifiedM \<and>
    CLEntry.block_state (devcache2 T) = IMA)"

\<comment>\<open>  GO-M to D2 consumed \<close>
definition "GTS_legal5_1 T = 
  ( 
    block_state (hostcache T) = ModifiedM \<and>
    CLEntry.block_state (devcache2 T) = Modified)"

definition "GTS_legal6 T = 
  (
    messageAtLast (\<lambda>m. getSpecificTypeSnoop m = SnpInv) (snps2 T) \<and> 
    CLEntry.block_state (devcache1 T) = IMAD)"


\<comment>\<open>  D2 responds to Host's SnpInv with RspIFwdM, downgrading to Invalid, data is also sent (not explicitly mandated here) \<close>
definition "GTS_legal7 T = 
  ( messageAtLast (\<lambda>m. getSpecificTypeSnpResp m = RspIFwdM) (snpresps2 T) \<and> 
    CLEntry.block_state (devcache2 T) = Invalid)"



\<comment>\<open>  GO-M sent to D1\<close>
definition "GTS_legal8 T = 
  (  
    messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps1 T) \<and>
    CLEntry.block_state (devcache1 T) = IMAD )"


\<comment>\<open>   Data forwarded to D1\<close>
definition "GTS_legal8_1 T = 
  (  
    
    block_state (hostcache T) = ModifiedM  )"


definition "GTS_legal9 T = 
  (  
    
    CLEntry.block_state (devcache1 T) = IMD \<and>
    CLEntry.block_state (devcache2 T) = Invalid)"

definition "GTS_legal10 T = 
  (  
    
    CLEntry.block_state (devcache1 T) = Modified \<and>
    CLEntry.block_state (devcache2 T) = Invalid)"

definition "GTS_violation_sequence =  [GTS_legal1, GTS_legal2, GTS_legal3, GTS_legal4, GTS_legal5, GTS_legal6, GTS_legal7, GTS_legal8, GTS_legal9, GTS_legal10]"


definition "GTS_chain = chain_of_states [GTSConfig]  GTS_violation_sequence "
definition "GTS_liberal_chain = chain_of_liberal_good_states [GTSConfig]  GTS_violation_sequence "
definition "GTS_bad_chain = chain_of_bad_states [GTSConfig]  GTS_violation_sequence "
value GTS_chain
value GTS_liberal_chain
value GTS_bad_chain
*)

definition "GTS_all_states = chain_of_states [GTSConfig] (unprunedN 14)"

value "GTS_all_states"

\<comment>\<open>
value "  GTS_chain"
definition "Sixth_state = \<lparr>hostcache = \<lparr>HostEntry.content = Some 0, block_state = MAD\<rparr>, devcache1 = \<lparr>CLEntry.content = Some 0, block_state = IMAD\<rparr>,
     devcache2 = \<lparr>CLEntry.content = Some 2, block_state = Modified\<rparr>, reqs1 = [], reqs2 = [], snpresps1 = [], snpresps2 = [],
     dthdatas1 = [], dthdatas2 = [], snps1 = [], snps2 = [H2DReq (Utid 3) SnpInv Dev2 16], reqresps1 = [], reqresps2 = [],
     htddatas1 = [], htddatas2 = [], program1 = [Write Dev1 1], program2 = [], counter = 4, registers11 = 0, registers12 = 0,
     registers21 = 0, registers22 = 0, clock = 17, buffer1 = None, buffer2 = None\<rparr>"

definition "seventh_state = onestep Sixth_state"

value "seventh_state"\<close>




definition GTS_vio1 :: "Type1State \<Rightarrow> bool" where  
  "GTS_vio1 T = messageAtLast (\<lambda>m. getSpecificTypeReq m = RdOwn) (reqs1 T)"



definition "GTS_vio2 T = 
  (
    messageAtLast (\<lambda>m. getSpecificTypeSnoop m = SnpInv) (snps2 T))"

\<comment>\<open> RdOwn from D2 is serviced first, therefore RdOwn from D1 remains
A data has been sent to D2, a SnpInv sent to D1\<close>
definition "GTS_vio3 T =   
  (reqs2 T \<noteq> [] )"


\<comment>\<open>  D1 processed SnpInv, downgraded from SMAD to IMAD, sent RspIHitSE \<close>
definition "GTS_vio4 T = 
  ( snps1 T \<noteq> [] )"

\<comment>\<open> violation happens: the Host has sent a tailgating GO to D1, which it has just sent a snoop without getting a response \<close>
definition "GTS_vio5 T = 
  ( \<comment>\<open>(buffer1 T) = None \<and> \<close>
    snpresps1 T \<noteq> [])"


\<comment>\<open>  GO-M to D1 consumed \<close>
definition "GTS_vio6 T = 
  ( snpresps1 T \<noteq> [] )"

\<comment>\<open>  Data to D1 consumed \<close>
definition "GTS_vio7 T = 
  ( 
    snpresps2 T \<noteq> [])"

\<comment>\<open>  GO-M to D2 sent \<close>
definition "GTS_vio8 T = 
  (reqresps1 T \<noteq> [])"


\<comment>\<open> Data to D2 consumed \<close>
definition "GTS_vio9 T = 
  ( reqresps2 T \<noteq> [])"



\<comment>\<open>  GO-M D2 consumed\<close>
definition "GTS_vio10 T = 
  (  
    block_state (hostcache T) = ModifiedM \<and>
        messageAtLast (\<lambda>m. getSpecificTypeReqResp m = GO) (reqresps2 T) \<and>
    CLEntry.block_state (devcache2 T) = IMAD )"


definition "GTS_vio11 T = 
  (  
    block_state (hostcache T) = ModifiedM \<and>
    CLEntry.block_state (devcache2 T) = IMD )"

definition "GTS_vio12 T = 
  ( CLEntry.block_state (devcache1 T) = Modified \<and>
    block_state (hostcache T) = ModifiedM \<and>
    CLEntry.block_state (devcache2 T) = Modified )"



definition "GTS_violation_sequence2 = 
  [GTS_vio1, GTS_vio2, GTS_vio3, GTS_vio4, GTS_vio5, GTS_vio6, GTS_vio7, GTS_vio8,  allTrue, allTrue, allTrue, allTrue, allTrue]"


definition "GTS_good_chain = chain_of_states [GTSConfig]  GTS_violation_sequence2 "
definition "GTS_bad_chain = chain_of_states_mixed [GTSConfig]  GTS_violation_sequence2 "
definition "GTS_liberal_chain = chain_of_liberal_good_states [GTSConfig]  GTS_violation_sequence2 "

value "GTS_good_chain"
value " GTS_bad_chain"
value " GTS_liberal_chain"


  value "list_prop_exists (concat GTS_good_chain) true_MESI_violation"
  value "list_prop_exists (concat GTS_liberal_chain) true_MESI_violation"
  value "list_prop_exists (concat GTS_bad_chain) true_MESI_violation"

(*the stronger property also holds for good rules, as indicated by our proof,
not too surprising but interesting: liberal rules don't violate swmr++ either
*)
  value "list_prop_exists (concat GTS_good_chain) (\<lambda>T. \<not> SWMR_state_machine T)"
  value "list_prop_exists (concat GTS_liberal_chain) (\<lambda>T. \<not> SWMR_state_machine T)"
  value "list_prop_exists (concat GTS_bad_chain) (\<lambda>T. \<not> SWMR_state_machine T)"
\<comment>\<open>This tries to reach a mesi violation with only good transitions, which fails
value " GTS_chain_violation"
  value "list_prop_exists GTS_chain_violation true_MESI_violation"
  value "list_prop_exists spg_chain true_MESI_violation"\<close>



\<comment>\<open>This tries to reach a mesi violation with  good and bad transitions, which succeeds
value "list_prop_exists GTS_bad_chain true_MESI_violation"
  value "list_prop_exists spg_chain_bad true_MESI_violation"\<close>


\<comment>\<open>problem: one might ask: this particular sequence of predicates can not get you into an error, but what about some other routes?

problem2: how do you enumerate all possible next states within 10 steps of your GTSconfig? How do you know 10 steps is sufficient?



\<close>






  value "1::nat"
\<comment>\<open>2024TODO: agument ModifiedRspIHitI rule such that it also sends data to the requestor
get an unordered network for the model (not the proof yet)\<close>

  value "take  1 GTS_chain_violation"

definition "GTS_vio_first3 = [GTS_vio1\<comment>\<open>, GTS_vio2, GTS_vio3\<close>]"

value "chain_of_states_mixed [GTSConfig]  GTS_vio_first3 "


definition "spg_chain_bad_list = chain_of_states_mixed [snoop_pushes_GO_config] SPG_violation_sequence"



definition"evict_test = \<lparr> 
    Type1State.hostcache         = \<lparr>HostEntry.content = Some 0, block_state = ModifiedM\<rparr>,
    Type1State.devcache1         = \<lparr>CLEntry.content = Some 1, CLEntry.block_state = Modified\<rparr>,
    Type1State.devcache2         = empty_entry, 
    Type1State.reqs1             = [],
    Type1State.reqs2             = [],
    Type1State.snpresps1         = [],
    Type1State.snpresps2         = [],
    Type1State.dthdatas1         = [],
    Type1State.dthdatas2         = [],
    Type1State.snps1           = [],
    Type1State.snps2           = [],
    Type1State.reqresps1         = [],
    Type1State.reqresps2         = [],
    Type1State.htddatas1         = [],
    Type1State.htddatas2         = [],
    program1                     = [Evict ],
    program2                     = [],
    counter                      = 2,
    registers11                  = 0,
    registers12                  = 0,
    registers21                  = 0,
    registers22                  = 0,
    clock                        = 9,
    buffer1                      = None,
    buffer2                      = None

  \<rparr>"



definition "evict_sequence = [allTrue, allTrue, allTrue, allTrue]"

definition "evict_states_sequence = chain_of_states [evict_test] evict_sequence"


value "evict_states_sequence"













end