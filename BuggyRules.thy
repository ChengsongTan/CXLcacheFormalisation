theory BuggyRules imports CoherenceProperties begin

\<comment>\<open>Implementing store forwarding entails modelling a non-blocking (per loc) protocol would requires modelling "pending instr PC" and "current PC",
which we implement later.
definition storeForwarding :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State" where [simp]:
  "storeForwarding T i = (let regNum = (getRegNum T i ) in let v = getin (if i = 0 then T \<lparr> r11 := 0 \<rparr> else T \<lparr>r11 := 1 \<rparr>))"

\<close>

definition saneSIACGO :: "Type1State \<Rightarrow> nat \<Rightarrow> bool" where [simp]: "saneSIACGO T i = (if i = 0 then \<not> HSTATE SAD T \<and> \<not> HSTATE MD T \<and> \<not> HSTATE MA T \<and> (CSTATE IIA T 1 \<longrightarrow> \<not> HSTATE SharedM T) else
\<not> HSTATE SAD T \<and> \<not> HSTATE MD T \<and> \<not> HSTATE MA T \<and> (CSTATE IIA T 0 \<longrightarrow> \<not> HSTATE SharedM T))"


definition InvalidLoad' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "InvalidLoad' T i = (if (CSTATE Invalid T i \<and> nextLoad T i) then [clearBuffer (sendReq RdShared ISAD i T)] else [])"

definition InvalidStore' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "InvalidStore' T i = (if (CSTATE Invalid T i \<and> nextStore T i) then [clearBuffer (sendReq RdOwn IMAD i T)] else [])"
definition SharedStore' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "SharedStore' T i = (if (CSTATE Shared T i \<and> nextStore T i) then [clearBuffer (sendReq RdOwn SMAD i T)] else [])"
definition SharedEvict' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "SharedEvict' T i = (if (CSTATE Shared T i \<and> nextEvict T i) then [clearBuffer (sendReq CleanEvictNoData SIAC i T)] else [])"
definition SharedEvictData' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "SharedEvictData' T i = (if (CSTATE Shared T i \<and> nextEvict T i) then [clearBuffer (sendReq CleanEvict SIA i T)] else [])"

definition ModifiedEvict' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "ModifiedEvict' T i = (if (CSTATE Modified T i \<and> nextEvict T i) then [clearBuffer (sendReq DirtyEvict MIA i T)] else [])"
\<comment>\<open>5 "Instruction starting" transitions are grouped together\<close> 

definition SharedLoad' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "SharedLoad' T i = (if (CSTATE Shared T i \<and> nextLoad T i) then [ clearBuffer (T[  -=i i  ]) ] else [])"
\<comment>\<open>TODO: store forwarding
definition "SMADLoad' T i = (if CSTATE SMAD T i \<and> nextLoad T i then [clearBuffer (storeForwarding T i)] else [])"
definition "SMALoad' T i = (if CSTATE SMA T i \<and> nextLoad T i then [clearBuffer (storeForwarding T i)] else [])"\<close>
definition "ModifiedStore' T i = (if  CSTATE Modified T i \<and> nextStore T i then [clearBuffer T [ -=i i]] else [])"
definition "ModifiedLoad' T i = (if CSTATE Modified T i \<and> nextLoad T i then [clearBuffer T [ -=i i]] else [])"

\<comment>\<open>5 device can perform instruction without requesting/upgrading  ownership
definition device_perform_op :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State" 
  ("_ [ -=i _]" [100] 101) where [simp]:
  "T [ -=i devNum] = (if devNum = 0 then 
          let v = read_from_cache (CLEntry.content ((devcache1 T) )) in
            (case ((program1 T) ) of [] \<Rightarrow> T 
                                      | Read  regNum # tlI \<Rightarrow> ( if regNum = 0 then T \<lparr>registers11 := v \<rparr> else T \<lparr>registers12 := v \<rparr> \<lparr> program1 := tlI \<rparr> )                                                                      
                                      | Write  v' # tlI \<Rightarrow> (T \<lparr>devcache1 := ( (devcache1 T)  \<lparr>CLEntry.content := Some v'\<rparr>)\<rparr> \<lparr> program1 := tlI \<rparr>)
                                      | Evict  # tlI \<Rightarrow> (T \<lparr>devcache1 := ((devcache1 T)  \<lparr>CLEntry.block_state := Invalid \<rparr>) \<rparr> \<lparr> program1 := tlI \<rparr>)
                     ) else
           let v = read_from_cache (CLEntry.content ((devcache2 T) )) in
            (case ((program2 T) ) of [] \<Rightarrow> T 
                                      | Read   regNum # tlI \<Rightarrow>  ( if regNum = 0 then T \<lparr>registers21 := v \<rparr> else T \<lparr>registers22 := v \<rparr> \<lparr> program2 := tlI \<rparr>) 
                                      | Write   v' # tlI \<Rightarrow> (T \<lparr>devcache2 := ( (devcache2 T)  \<lparr>CLEntry.content := Some v'\<rparr>)\<rparr> \<lparr> program2 := tlI \<rparr> )
                                      | Evict   # tlI \<Rightarrow> (T \<lparr>devcache2 := ((devcache2 T)  \<lparr>CLEntry.block_state := Invalid \<rparr> )\<rparr> \<lparr> program2 := tlI \<rparr>)
                     )
)"

definition device_perform_rd :: "Type1State \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> Type1State" 
  ("_ [_ :=r _]" [100] 101) where [simp]:
  "T [devNum :=r regNum] = (if devNum = 0 then 
          let v = read_from_cache (CLEntry.content ((devcache1 T) )) in
            (case ((program1 T) ) of [] \<Rightarrow> T 
                                      | I # tlI \<Rightarrow> ( if regNum = 0 then T \<lparr>registers11 := v \<rparr> \<lparr> program1 := tlI \<rparr> else T \<lparr>registers12 := v \<rparr> \<lparr> program1 := tlI \<rparr> )
                     ) else
           let v = read_from_cache (CLEntry.content ((devcache2 T) )) in
            (case ((program2 T) ) of [] \<Rightarrow> T 
                                      | I # tlI \<Rightarrow>  ( if regNum = 0 then T \<lparr>registers21 := v \<rparr> \<lparr> program2 := tlI \<rparr> else T \<lparr>registers22 := v \<rparr> \<lparr> program2 := tlI \<rparr>) 
                     )
)"

\<close>










definition SharedSnpInv' :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list" where [simp]: "SharedSnpInv' T i = (if (CXL_SPG_used T i \<and> CSTATE Shared T i \<and> nextSnoopIs SnpInv T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitSE Invalid i T] else [] )"







definition "ISDSnpInv' T i = (if (CXL_SPG_used T i \<and> CSTATE ISD T i \<and> nextSnoopIs SnpInv T i) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitSE ISDI i T] else [])"
\<comment>\<open>Proof notes: these scenarios are perfectly valid, and must be considered, same applies to the rest of the rules\<close> 

definition "SMADSnpInv' T i = (if CXL_SPG_used T i \<and> CSTATE SMAD T i \<and> nextSnoopIs SnpInv T i then
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitSE IMAD i T] else [])"


definition "MIASnpDataInvalid' T i = (if CXL_SPG_used T i \<and> CSTATE MIA T i \<and> nextSnoopIs SnpData T i then [sendSnpRespAndData RspIFwdM IIA i T] else [])"

definition "MIASnpDataShared' T i = (if CXL_SPG_used T i \<and> CSTATE MIA T i \<and> nextSnoopIs SnpData T i then [sendSnpRespAndData RspSFwdM SIA i T] else [])"


definition "SIASnpInv' T i = (if CXL_SPG_used T i \<and> CSTATE SIA T i \<and> nextSnoopIs SnpInv T i \<and> \<not> nextReqIs DirtyEvict T i
  then [sendSnpResp (getSnoopOrMakeup (getSnoops i T))  RspIHitSE IIA i T] else [])"
definition  "MIASnpInv' T i = (if CXL_SPG_used T i \<and> CSTATE MIA T i \<and> nextSnoopIs SnpInv T i then [sendSnpRespAndData RspIFwdM IIA i T] else [])"


\<comment>\<open>Note: 3 more overlooked rules.
Note+: Data and Response are modelled as sent together for simplicity: the host can non-deterministically choose to process data/response first.\<close>
definition "ModifiedSnpInv' T i = (if (CXL_SPG_used T i \<and> CSTATE Modified T i \<and> nextSnoopIs SnpInv T i ) then 
  [sendSnpRespAndData RspIFwdM Invalid i T] else [] )"

definition "ModifiedSnpDataShared' T i = (if (CXL_SPG_used T i \<and> CSTATE Modified T i \<and> nextSnoopIs SnpData T i ) then 
  [sendSnpRespAndData RspSFwdM Shared i T] else [] )"

definition "ModifiedSnpDataInvalid' T i = (if (CXL_SPG_used T i \<and> CSTATE Modified T i \<and> nextSnoopIs SnpData T i ) then 
  [sendSnpRespAndData RspIFwdM Invalid i T] else [] )"

\<comment>\<open>15 "Device responding to snoop" transitions are grouped together\<close>






definition "ISDData' T i = ( if CSTATE ISD T i \<and> nextHTDDataPending T i then 
  [clearBuffer (copyInDataPerformInstr (getHTDDataOrMakeup T i) i Shared T)] else [])"
definition "ISDIData' T i = (if CSTATE ISDI T  i \<and> nextHTDDataPending T i then [clearBuffer (copyInDataPerformInstr (getHTDDataOrMakeup T i) i Invalid T)] else [])"
\<comment>\<open>!1 3.2.5.2.2 last sentence of paragraph:
Note that the response (GO) message can be received before, after, or between the data messages.

TODO: Would it be possible for Host to be in MD state (meaning sending Data and sending GO are done in a separate time, and is non-atomic\<close>
definition "IMADData' T i = (if CSTATE IMAD T i \<and> nextHTDDataPending T i then [clearBuffer (copyInData (getHTDDataOrMakeup T i) i IMA T)] else [])"
definition "SMADData' T i = (if CSTATE SMAD T i \<and> nextHTDDataPending T i then [clearBuffer (copyInData (getHTDDataOrMakeup T i) i SMA T)]  else [])"
definition "ISADData' T i = (if CSTATE ISAD T i \<and> nextHTDDataPending T i then [clearBuffer (copyInData (getHTDDataOrMakeup T i) i ISA T)] else [])"
\<comment>\<open>!4 3.2.5.2.2 last sentence of paragraph:
Note that the response (GO) message can be received before, after, or between the data messages.\<close>
definition "IMDData' T i = (if  CSTATE IMD T i \<and> nextHTDDataPending T i then [clearBuffer (copyInDataPerformInstr (getHTDDataOrMakeup T i) i Modified T)] else [])"
definition "SMDData' T i = (if  CSTATE SMD T i \<and> nextHTDDataPending T i then [clearBuffer (copyInDataPerformInstr (getHTDDataOrMakeup T i) i Modified T)] else [])"

\<comment>\<open>6 Device taking Data and upgrading state\<close>

\<comment>\<open>!2 3.2.5.2.2 last sentence of paragraph:
Note that the response (GO) message can be received before, after, or between the data messages.\<close>
definition "IMADGO' T i = (if CSTATE IMAD T i \<and> nextGOPending T i then [consumeGO i IMD T] else [])"
definition "ISADGO' T i = (if CSTATE ISAD T i \<and> nextGOPending T i then [consumeGO i ISD T] else [])"
definition "SMADGO' T i = (if CSTATE SMAD T i \<and> nextGOPending T i then [consumeGO i SMD T] else [])"
definition "SMAGO' T i = (if CSTATE SMA T i \<and> nextGOPending T i then [consumeGOPerform i Modified T] else [])"
\<comment>\<open>!3 3.2.5.2.2 last sentence of paragraph:
Note that the response (GO) message can be received before, after, or between the data messages.\<close>
definition "IMAGO' T i = (if CSTATE IMA T i \<and> nextGOPending T i then [ consumeGOPerform i Modified T] else [])"
definition "ISAGO' T i = (if CSTATE ISA T i \<and> nextGOPending T i then [ consumeGOPerform i Shared T] else [])"
\<comment>\<open>device consumes host resp, upgrades to state, and perform instruction\<close>

definition "SIAGO_WritePullDrop' T i = (if CSTATE SIA T i \<and> nextGOPendingIs GO_WritePullDrop T i then
  [consumeGODiscard  i Invalid T] else [])"

definition "SIAGO_WritePull' T i = (if CSTATE SIA T i \<and> nextGOPendingIs GO_WritePull T i then
  [consumeGOSendData  i Invalid T] else [])"

definition "SIACGO' T i = (if CSTATE SIAC T i \<and> nextGOPendingIs GO T i \<and> nextGOPendingState Invalid T i \<and> GTS T ((i + 1) mod 2) \<and> saneSIACGO T i then
  [consumeGODiscard  i Invalid T] else [])"

\<comment>\<open>consume GO WritePull. This state corresponds to a device being invalidated while evicting its copy.
This late-running GO_WritePull should no longer require data to be sent again, but to be as faithful as possible to CXL,
we choose to implement as dictated by the table 3-18 D2H Request (Targeting Non Device-attached Memory) Supported H2D Responses (Sheet 1 of 2) 
on page 99.
\<close>
definition "IIAGO_WritePull' T i = (if CSTATE IIA T i \<and> nextGOPendingIs GO_WritePull T i then
  [consumeGOSendData  i Invalid T] else [])"
definition "IIAGO_WritePullDrop' T i = (if CSTATE IIA T i \<and> nextGOPendingIs GO_WritePullDrop T i then
  [consumeGODiscard  i Invalid T] else [])"
\<comment>\<open>consume GO, go to state Invalid, send D2HData for eviction\<close>
definition  "MIAGO_WritePull' T i = (if CSTATE MIA T i \<and> nextGOPendingIs GO_WritePull T i then
  [consumeGOSendDataPerformEvict i Invalid T ] else [])"

\<comment>\<open>12+1 = 13 Device got GO, upgrading/downgrading, if successfully upgraded/downgraded to a stable state, perform the pending instruction\<close>



\<comment>\<open>10 12 6 12 = 40 in total for device\<close>







\<comment>\<open>shortcut transaction, sendHostDataGO consumes the request directly, and responds with GO and Data, updating host state\<close>
\<comment>\<open>proof notes: removed the "clearBuffer" function typically used in a transition not involving the buffer: it is not used in SWMR proofs.\<close>
definition "HostInvalidRdShared' T i = (if HSTATE InvalidM T \<and> nextReqIs RdShared T i \<and> GTS T ((i + 1) mod 2) then 
  [ (sendHostDataGO (nextReqID T i) i SharedM Shared GO T)] else [])"
definition "HostInvalidRdOwn' T i = (if HSTATE InvalidM T \<and> nextReqIs RdOwn T i \<and> GTS T ((i + 1) mod 2) then 
  [ (sendHostDataGO (nextReqID T i) i ModifiedM Modified GO T)] else [])"
definition "HostSharedRdShared' T i = (if HSTATE SharedM T \<and> nextReqIs RdShared T i \<and> GTS T ((i + 1) mod 2) then 
[ (sendHostDataGO (nextReqID T i) i SharedM Shared GO T)] else [])" \<comment> \<open>if necessary snoop sharers, GO+Data if possible\<close>
\<comment>\<open>change to MA state, send copy of Data to requestor, send SnpInv to all sharers, consume req\<close>
\<comment>\<open>3 host can immediately grant permission to requestor, without snooping another device\<close>

(*Not really a strengthening--NOT cstate iia t 1 just means the other side cannot be Invalid, then this rule should be Last instead of NotLast*)
definition "HostShared_CleanEvict_NotLastData' T i = (if HSTATE SharedM T \<and> nextReqIs CleanEvict T i \<and> \<not>(lastSharer T) \<and> GTS T ((i + 1) mod 2) \<and> \<not> CSTATE IIA T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO_WritePull i SB (nextReqID T i) T)] else [])"
(*~ cstate iia t 1 just checks other side is a sharer, so it's indeed NotLast*)
definition "HostShared_CleanEvict_NotLastDrop' T i = (if HSTATE SharedM T \<and> nextReqIs CleanEvict T i \<and> \<not>(lastSharer T) \<and> GTS T ((i + 1) mod 2) \<and> \<not> CSTATE IIA T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO_WritePullDrop i SharedM (nextReqID T i) T)] else [])"
definition "HostShared_CleanEvict_Last' T i = (if HSTATE SharedM T \<and> nextReqIs CleanEvict T i \<and> (lastSharer T) \<and>  GTS T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO_WritePull i IB (nextReqID T i) T) ] else [])"
  \<comment>\<open>CXL says you must send GO-I in receiving CleanEvictNoData.\<close>
definition "HostShared_CleanEvictNoData_NotLast' T i = (if HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T i \<and> \<not>(lastSharer T) \<and>  GTS T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO i SharedM (nextReqID T i) T)] else [])"
definition "HostShared_CleanEvictNoData_Last' T i = (if HSTATE SharedM T \<and> nextReqIs CleanEvictNoData T i \<and> (lastSharer T) \<and>  GTS T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO i InvalidM (nextReqID T i) T)] else [])"

 \<comment>\<open> This is a very subtle transition, normally should not occur, DirtyEvict was greatly delayed and the data is no longer needed,
however to be faithful to CXL we still choose to send GO_WritePull instead of dropping the data
We have to take care of when the DirtyEvict does not come from the current owner, for which it stays in M(M) state, and also 
drops the Data (as Bogus = 1)
Also possible ModifiedInvalidEvict, as the old owner being invalidated means some other device has go ownership.
Current owner downgraded first, then previous owner trying to downgrade.\<close>
definition "HostShared_DirtyEvict' T i = (if HSTATE SharedM T \<and> nextReqIs DirtyEvict T i  \<and>  GTS T ((i + 1) mod 2) \<and> CSTATE IIA T i
  then [clearBuffer(sendEvictResp GO_WritePull i SB (nextReqID T i) T )] else [])"
definition "HostModifiedDirtyEvict' T i = (if HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T i  \<and> GTS T ((i + 1) mod 2) \<and> CSTATE MIA T i \<and> \<not> (CSTATE SIA T 1 \<and> nextGOPendingIs GO_WritePullDrop T 1)
  then [clearBuffer (sendEvictResp GO_WritePull i ID (nextReqID T i) T)] else [])"   
definition "HostModifiedDirtyEvictPrevious' T i = (if HSTATE ModifiedM T \<and> nextReqIs DirtyEvict T i  \<and> GTS T ((i + 1) mod 2) \<and> CSTATE IIA T i \<and> CSTATE Modified T ((i + 1) mod 2)
  then [clearBuffer (sendEvictResp GO_WritePull i MB (nextReqID T i) T)] else [])"   
\<comment>\<open>This happens when new owner evicted first, making old owner's DE even more stale. still send GWP to previous owner. added 20240313. 
TODO: verify stale data always discarded. TODO: what if previous owner is starved? i.e. the new owner now keeps getting ownership and relinquishing it. 
This DE can happen at any transient state then.TODO: CleanEvict could suffer from this same delay, causing CE+any HSTATE.\<close>
definition "HostInvalidDirtyEvict' T i = (if HSTATE InvalidM T \<and> nextReqIs DirtyEvict T i  \<and> GTS T ((i + 1) mod 2) \<and> CSTATE IIA T i
  then [clearBuffer (sendEvictResp GO_WritePull i IB (nextReqID T i) T)] else [])" 

\<comment>\<open>previous owner's DE is serialised, for which Host sends a GWP. new rule 20240313. TODO: add to set of rules
20240401 make proof simpler by disallowing this rule, less concurrency
definition "HostIDDirtyEvict' T i = (if HSTATE ID T \<and> nextReqIs DirtyEvict T i  \<and> GTS T ((i + 1) mod 2) \<and> CSTATE IIA T i
  then [clearBuffer (sendEvictResp GO_WritePull i ID (nextReqID T i) T)] else [])" 
\<close>



\<comment>\<open>6 An eviction request, send response, depending on whether is last one set the global view to all Invalid or still some shared\<close>





\<comment>\<open>consume req, upgrade host state, send snoop\<close>
definition "HostModifiedRdShared' T i = (if HSTATE ModifiedM T \<and> nextReqIs RdShared T i then [clearBuffer (sendSnoop SnpData i SAD T)] else [])"
definition "HostModifiedRdOwn' T i = (if HSTATE ModifiedM T \<and> nextReqIs RdOwn T i  then [clearBuffer (sendSnoop SnpInv i MAD T)] else [])" 

\<comment>\<open>2024.10 note: (CSTATE Shared T ((i + 1) mod 2) \<or> CSTATE SMAD T ((i + 1) mod 2)) should be used in the last conjunct if we want an even more concurrent system\<close>
definition "HostSharedRdOwn' T i = (if HSTATE SharedM T \<and> nextReqIs RdOwn T i \<and> CSTATE Shared T ((i + 1) mod 2) then
  [clearBuffer (invalidateSharers (nextReqID T i) i T) ] else [])" \<comment>\<open>Only send data in the case the other side is a valid copy holder. TODO: add the rule where the other side is SMAD\<close>
\<comment>\<open>3 When host got a rdreq that would require a snoop: sharers should be invalidated for RdOwn, and owners be downgraded/invalidated  for RdS/O\<close>
(*2024.10 note: last conjunct should be replaced by a more general predicate such as almostInvalid T ((i+1)mod2) to allow even more concurrency *)
definition "HostSharedRdOwnSelf' T i = (if HSTATE SharedM T \<and> nextReqIs RdOwn T i \<and> (CSTATE Invalid T ((i + 1) mod 2)) then
  [clearBuffer (noInvalidateSharers (nextReqID T i) i T) ] else [])"


\<comment>\<open>send data to requestor, consume data and copy in to host cache, upgrade to state SharedM\<close>
definition "HostSDData' T i = (if HSTATE SD T \<and>    nextDTHDataFrom i T
  then [clearBuffer (copyInAndForwardData i SharedM T) ] else [])"                
definition "HostSADData' T i = (if HSTATE SAD T \<and>    nextDTHDataFrom i T        
  then [clearBuffer (copyInAndForwardData i SA T) ] else [])" 
definition "HostMDData' T i = (if HSTATE MD T \<and> nextDTHDataFrom i T 
  then [clearBuffer (copyInAndForwardData i ModifiedM T)  ] else [])"
(* \<not> nextReqIs DirtyEvict T ((i + 1) mod 2) was an old strengthening, about fairness and latency guarantees. We 
replaced this with "looking at device caches state to ensure sanity"*)
definition "HostIDData' T i = (if HSTATE ID T \<and> nextDTHDataFrom i T \<and> CSTATE Invalid T i \<and>  (CSTATE IIA T ((i+1)mod 2) \<or> CSTATE Invalid T ((i+1)mod 2) \<or> CSTATE SIA T ((i+1)mod 2))
  then [clearBuffer (copyInDataHost i InvalidM T)  ] else [])"

(*cstate invalid t i refers to the data provider already downgrading to invalid, because SB only used for DE and CE, which both ends up in Invalid*)
definition "HostSBData' T i = (if HSTATE SB T \<and> nextDTHDataFrom i T \<and> CSTATE Invalid T i
  then [clearBuffer (discardDataHost i SharedM T)  ] else [])"


definition "HostMADData' T i = (if HSTATE MAD T \<and> nextDTHDataFrom i T then [copyInAndForwardData i MA T ] else [])"
\<comment>\<open>The Host sees a Data from an Invalid device, which means it had previously downgraded from IIA.
This corresponds to CXL's Bogus Data, dropped by Host.\<close>

(*similar to SB, no strengthenings really *)
definition "HostMBData' T i = (if HSTATE MB T \<and> nextDTHDataFrom i T \<and> CSTATE Invalid T i
then [clearBuffer (discardDataHost i ModifiedM T) ] else [])"
(*similar to SB, no strengthenings really *)
definition "HostIBDataPrevious' T i = (if HSTATE IB T \<and> nextDTHDataFrom i T \<and> CSTATE Invalid T i \<and> CSTATE Invalid T ((i + 1) mod 2)
then [clearBuffer (discardDataHost i InvalidM T)] else [])"
\<comment>\<open>6+1 copy in the D2HData, and forward the data to initial requestor unless it is an eviction\<close>


\<comment>\<open>send GO, consume snoop resp, granting Shared state to requestor, host upgrades to SD state\<close>
definition "HostSADRspIFwdM' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [ clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 


definition "HostSADRspSFwdM' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T i \<and> GTS T i
  then [clearBuffer ( sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 
definition "HostMADRspIFwdM' T i = (if HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO MD T)  ] else [])"

definition "HostMARspIFwdM' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"
\<comment>\<open>TODO: need to add SAD --> SA where data is processed first
\<close>
(*htddats1 T = [] is really an SPG+no snoop sent between Data-GO (Data-GO atomicity) restriction, which is part of spec (3.2.5.2 paragraph 3) 
future work: some simpler phrasing of these restrictions: e.g. double-GO not allowed*)
definition "HostMARspIHitSE' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIHitSE T i \<and> GTS T i \<and> htddatas1 T  = []
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"




definition "HostSARspIFwdM' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspIFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"
definition "HostSARspSFwdM' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspSFwdM T i \<and> GTS T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"








\<comment>\<open>in total 10+5+3+6+3=27 host transitions+2 = 29 \<close>




\<comment>\<open>MARdOwn not modelled/not possible\<close>
\<comment>\<open> export_code guard_transition in Scala
definition guard_transition :: "(nat * nat * nat) \<Rightarrow> Type1State \<Rightarrow> bool"
  where
"guard_transition tuple T = (let (row, col, devNum) = tuple in
                          if devNum < OFFSET then  
                           
                          
)) "

definition do_transition_phase1 :: "(nat * nat * nat) \<Rightarrow> Type1State \<Rightarrow> Type1State" 
  where
"do_transition_phase1 tuple T = (let (row, col,  devNum) = tuple in
                          if devNum < OFFSET then \<comment>\<open>clearBuffer is applied to all non-snoop/GO transactions\<close>
                            (   
 \<comment>\<open>purposefully written transition to trigger SPG violation\<close>
                          else  \<comment> \<open>devNum - 5 is the requestor\<close>
                             
                             \<comment>\<open>Impossible: if row = MEM_MA_ROW \<and> col = RSPIFWDM_COL then sendGOFromSnpResp  (nextSnoopRespID T (devNum - 5)) devNum Modified GO MD T else \<close>                                                       
T                             
)               
) 

definition do_transition :: "(nat * nat * nat) \<Rightarrow> Type1State \<Rightarrow> Type1State" where
  "do_transition n T =  (do_transition_phase1 n T)"

"\<close>





definition update_clock :: "Type1State \<Rightarrow> Type1State" ( "_ ++cl " [100] 101) where
  " T++cl = T \<lparr> clock := (clock T ) + 1 \<rparr>"




definition "InvalidLoad T i = map update_clock (InvalidLoad' T i )"
definition "SharedLoad T i = (map update_clock (SharedLoad' T i))"
definition "InvalidStore T i = map update_clock (InvalidStore' T i)"
definition "SharedStore T i = map update_clock (SharedStore' T i)"
definition "SharedEvict T i = map update_clock (SharedEvict' T i)"
definition "SharedEvictData T i = map update_clock (SharedEvictData' T i)"
definition "ModifiedEvict T i = map update_clock (ModifiedEvict' T i)"
\<comment>\<open>
definition "InvalidSnpData T i = map update_clock (InvalidSnpData' T i)"
definition "SharedSnpData T i = map update_clock (SharedSnpData' T i)"\<close>
definition "SharedSnpInv T i = map update_clock (SharedSnpInv' T i)"
\<comment>\<open>definition "InvalidSnpInv T i = map update_clock (InvalidSnpInv' T i)"\<close>
definition "ISDSnpInv T i = map update_clock (ISDSnpInv' T i)"
definition "ISDData T i = map update_clock (ISDData' T i)"
definition "ISDIData T i = map update_clock (ISDIData' T i)"
definition "IMADData T i = map update_clock (IMADData' T i)"
definition "SMADData T i = map update_clock (SMADData' T i)"
definition "IMADGO T i = map update_clock (IMADGO' T i)"
definition "ISADGO T i = map update_clock (ISADGO' T i)"
definition "ISADData T i = map update_clock (ISADData' T i)"
\<comment>\<open>
definition "ISADSnpData T i = map update_clock (ISADSnpData' T i)"
definition "ISADSnpInv T i = map update_clock (ISADSnpInv' T i)"
\<close>
definition "SMADGO T i = map update_clock (SMADGO' T i)"
definition "SMAGO T i = map update_clock (SMAGO' T i)"
\<comment>\<open>Store forwarding implementation complicated
definition "SMADLoad T i = map update_clock (SMADLoad' T i)"
definition "SMALoad T i = map update_clock (SMALoad' T i)"\<close>

definition "SMADSnpInv T i = map update_clock (SMADSnpInv' T i)"
\<comment>\<open>
definition "IMADSnpInv T i = map update_clock (IMADSnpInv' T i)"
\<close>
definition "IMAGO T i = map update_clock (IMAGO' T i)"
definition "ISAGO T i = map update_clock (ISAGO' T i)"
definition "ModifiedStore T i = map update_clock (ModifiedStore' T i)"
definition "ModifiedLoad T i = map update_clock (ModifiedLoad' T i)"




definition "SIAGO_WritePullDrop T i = map update_clock (SIAGO_WritePullDrop' T i)"
definition "SIAGO_WritePull T i = map update_clock (SIAGO_WritePull' T i)"
\<comment>\<open>
definition "SIAGO_I T i = map update_clock (SIAGO_I' T i)"\<close>
definition "IIAGO_WritePullDrop T i = map update_clock (IIAGO_WritePullDrop' T i)"
definition "IIAGO_WritePull T i = map update_clock (IIAGO_WritePull' T i)"
definition "IMDData T i = map update_clock (IMDData' T i)"
definition "SMDData T i = map update_clock (SMDData' T i)"
definition "MIASnpDataInvalid T i = map update_clock (MIASnpDataInvalid' T i)"
definition "MIASnpDataShared T i = map update_clock (MIASnpDataShared' T i)"
definition "MIASnpInv T i = map update_clock (MIASnpInv' T i)"
definition "MIAGO_WritePull T i = map update_clock (MIAGO_WritePull' T i)"
definition "SIASnpInv T i = map update_clock (SIASnpInv' T i)"
definition "ModifiedSnpInv T i = map update_clock (ModifiedSnpInv' T i)"
definition "ModifiedSnpDataShared T i = map update_clock (ModifiedSnpDataShared' T i)"
definition "ModifiedSnpDataInvalid T i = map update_clock (ModifiedSnpDataInvalid' T i)"



definition "HostInvalidRdShared T i = map update_clock (HostInvalidRdShared' T i)"
definition "HostInvalidRdOwn T i = map update_clock (HostInvalidRdOwn' T i)"
definition "HostSharedRdShared T i = map update_clock (HostSharedRdShared' T i)"
definition "HostShared_CleanEvict_NotLastDrop T i = map update_clock (HostShared_CleanEvict_NotLastDrop' T i)"
definition "HostShared_CleanEvict_NotLastData T i = map update_clock (HostShared_CleanEvict_NotLastData' T i)"
definition "HostShared_CleanEvict_Last T i = map update_clock (HostShared_CleanEvict_Last' T i)"
definition "HostShared_CleanEvictNoData_NotLast T i = map update_clock (HostShared_CleanEvictNoData_NotLast' T i)"
definition "HostShared_CleanEvictNoData_Last T i = map update_clock (HostShared_CleanEvictNoData_Last' T i)"
definition "HostShared_DirtyEvict T i = map update_clock (HostShared_DirtyEvict' T i)"
definition "HostModifiedDirtyEvict T i = map update_clock (HostModifiedDirtyEvict' T i)"
definition "HostModifiedDirtyEvictPrevious T i = map update_clock (HostModifiedDirtyEvictPrevious' T i)"
definition "HostModifiedRdShared T i = map update_clock (HostModifiedRdShared' T i)"
definition "HostModifiedRdOwn T i = map update_clock (HostModifiedRdOwn' T i)"
definition "HostSharedRdOwn T i = map update_clock (HostSharedRdOwn' T i)"
definition "HostSharedRdOwnSelf T i = map update_clock (HostSharedRdOwnSelf' T i)"
definition "HostSDData T i = map update_clock (HostSDData' T i)"
definition "HostSADData T i = map update_clock (HostSADData' T i)"
definition "HostMDData T i = map update_clock (HostMDData' T i)"
definition "HostIDData T i = map update_clock (HostIDData' T i)"
definition "HostMADData T i = map update_clock (HostMADData' T i)"
definition "HostIBDataPrevious T i = map update_clock (HostIBDataPrevious' T i)"
definition "HostMBData T i = map update_clock (HostMBData' T i)"
definition "HostSBData T i = map update_clock (HostSBData' T i)"
definition "HostInvalidDirtyEvict T i = map update_clock (HostInvalidDirtyEvict' T i)"
definition "SIACGO T i = map update_clock (SIACGO' T i)"


definition "HostSADRspIFwdM T i = map update_clock (HostSADRspIFwdM' T i)"
definition "HostSADRspSFwdM T i = map update_clock (HostSADRspSFwdM' T i)"
definition "HostMADRspIFwdM T i = map update_clock (HostMADRspIFwdM' T i)"
definition "HostMARspIHitSE T i = map update_clock (HostMARspIHitSE' T i)"
definition "HostMARspIFwdM T i = map update_clock (HostMARspIFwdM' T i)"
definition "HostSARspIFwdM T i = map update_clock (HostSARspIFwdM' T i)"
definition "HostSARspSFwdM T i = map update_clock (HostSARspSFwdM' T i)"






\<comment>\<open>remove the message that has just been enqueued\<close>
definition removeLastMessage :: "Type1State \<Rightarrow> nat \<Rightarrow> Message \<Rightarrow> Type1State" ( "_ --msg _ _" [101, 1] 100)
  where
  " removeLastMessage T i m = (if i = 0 then (case m of 
      H2DResp txid gotype state_granted time \<Rightarrow> T \<lparr> reqresps1 := butlast (reqresps1 T) \<rparr>
    | H2DReq txid snooptype time_ \<Rightarrow> T \<lparr> snps1 := butlast (snps1 T) \<rparr>
    | H2DData txid v time_ \<Rightarrow> T \<lparr> htddatas1 := butlast (htddatas1 T) \<rparr>
    | D2HResp txid snpresptype  time \<Rightarrow> T \<lparr> snpresps1 := butlast (snpresps1 T) \<rparr>
    | D2HReq txid reqtype time_ \<Rightarrow> T \<lparr> reqs1 := butlast (reqs1 T) \<rparr>
    | D2HData txid v time_ \<Rightarrow> T \<lparr> dthdatas1 := butlast (dthdatas1 T) \<rparr>
 )
  else  (case m of 
      H2DResp txid gotype state_granted time \<Rightarrow> T \<lparr> reqresps2 := butlast (reqresps2 T) \<rparr>
    | H2DReq txid snooptype time_ \<Rightarrow> T \<lparr> snps2 := butlast (snps2 T) \<rparr>
    | H2DData txid v time_ \<Rightarrow> T \<lparr> htddatas2 := butlast (htddatas2 T) \<rparr>
    | D2HResp txid snpresptype  time \<Rightarrow> T \<lparr> snpresps2 := butlast (snpresps2 T) \<rparr>
    | D2HReq txid reqtype time_ \<Rightarrow> T \<lparr> reqs2 := butlast (reqs2 T) \<rparr>
    | D2HData txid v time_ \<Rightarrow> T \<lparr> dthdatas2 := butlast (dthdatas2 T) \<rparr>
 )
)
"

\<comment>\<open>prepend the message that has just been dequeued\<close>
definition prependRecentMessage :: "Type1State \<Rightarrow> nat \<Rightarrow> Message \<Rightarrow> Type1State" ("_ ++msg _ _" [101, 1] 100) where
  "prependRecentMessage T i m = (if i = 0 then (case m of 
      H2DResp txid gotype state_granted time \<Rightarrow> T \<lparr> reqresps1 := m # (reqresps1 T) \<rparr>
    | H2DReq txid snooptype time_ \<Rightarrow> T \<lparr> snps1 := m # (snps1 T) \<rparr>
    | H2DData txid v time_ \<Rightarrow> T \<lparr> htddatas1 := m # (htddatas1 T) \<rparr>
    | D2HResp txid snpresptype  time \<Rightarrow> T \<lparr> snpresps1 := m # (snpresps1 T) \<rparr>
    | D2HReq txid reqtype time_ \<Rightarrow> T \<lparr> reqs1 := m # (reqs1 T) \<rparr>
    | D2HData txid v time_ \<Rightarrow> T \<lparr> dthdatas1 := m # (dthdatas1 T) \<rparr>
 )
  else  (case m of 
      H2DResp txid gotype state_granted time \<Rightarrow> T \<lparr> reqresps2 := m # (reqresps2 T) \<rparr>
    | H2DReq txid snooptype time_ \<Rightarrow> T \<lparr> snps2 := m # (snps2 T) \<rparr>
    | H2DData txid v time_ \<Rightarrow> T \<lparr> htddatas2 := m # (htddatas2 T) \<rparr>
    | D2HResp txid snpresptype  time \<Rightarrow> T \<lparr> snpresps2 := m # (snpresps2 T) \<rparr>
    | D2HReq txid reqtype time_ \<Rightarrow> T \<lparr> reqs2 := m # (reqs2 T) \<rparr>
    | D2HData txid v time_ \<Rightarrow> T \<lparr> dthdatas2 := m # (dthdatas2 T) \<rparr>
 )
)
"


definition "HostShared_CleanEvict_NotLast_Inverse T i = (if (block_state (hostcache T)) = InvalidM then (let gomsg = (last (reqresps1 T)) in 
  (case gomsg of H2DResp txid gotype state_granted time 
      \<Rightarrow> let reqmsg = (D2HReq txid CleanEvict (time - 1)) in [((T --msg i gomsg) ++msg i reqmsg) [5  sHost= SharedM] ]
 | _  \<Rightarrow> [])


  ) else []

)
"

(*

With events we can implement "Snoop pushes GO" violation: consider two events been issued from Dev1 and Dev2 at roughtly the same time:


        eventToIssue    reqs
Dev1:    [RdOwn]        [], I
Dev2:   [RdShared]      [], I

        eventToIssue    reqs
Dev1:    []           [RdOwn], IMAD
Dev2:   [RdShared]      [],   I

        eventToIssue    reqs
Dev1:    []           [RdOwn], IMAD, I
Dev2:    []           [RdShared], ISAD, I

        eventToIssue    reqs
Dev1:   eventToIssue = [], reqs = [],         devclmap: IMAD, hostcache's block_state: M,   snoops = [], reqresps = [GO-M]  (No one valid, so M is directly granted for dev1)
Dev2:   eventToIssue = [], reqs = [RdShared], devclmap: ISAD, hostcache's block_state: M, snoops = [], reqresps = [] 

        eventToIssue    reqs
Dev1:   eventToIssue = [], reqs = [],         devclmap: IMAD, hostcache's block_state: SAD,   snoops = [SnpData], reqresps = [GO-M]  (Now Dev2's RdShared is processed)
Dev2:   eventToIssue = [], reqs = [], devclmap: ISAD,         hostcache's block_state: SAD, snoops = [], reqresps = [] 

At this point both SnpData and GO-M can be propagated to Dev1. Now the issuedEvents list for Dev1 is updated so we get

        eventToIssue    reqs
Dev1:   eventToIssue = [], reqs = [],         devclmap: IMAD, hostcache's block_state: SAD,   snoops = [], reqresps = [GO-M], receivedSnoops = [SnpData]
Dev2:   eventToIssue = [], reqs = [], devclmap: ISAD,         hostcache's block_state: SAD, snoops = [], reqresps = [] 




ERROR: IMAD sees SnpData!

*)
type_synonym prettyPrintedConfig =  "(Message list * Message list * MESI_State * Message list * MESI_State * Message list * Message list * Message list * Message option) * 
(Message list * Message list * Message list * MESI_State * Message list * Message list * Message list * Message option)" 


\<comment>\<open>A dirty quick function to achieve the above\<close>
(*definition prettyPrintingType1 :: "Type1State \<Rightarrow> prettyPrintedConfig" where
  "prettyPrintingType1 T = (   
  (((htddatas T) Dev1) \<comment>\<open>eventToIssue\<close>, (dthdatas T) Dev1, block_state (hostcache T), (reqs T) Dev1, block_state ((devclmap T) Dev1), (reqresps T) Dev1, (snoops T) Dev1, (snpresps T) Dev1, (buffer T) Dev1),
  ((htddatas T) Dev2) \<comment>\<open>eventToIssue\<close>, (dthdatas T) Dev2, (reqs T) Dev2, block_state ((devclmap T) Dev2), (reqresps T) Dev2, (snoops T) Dev2, (snpresps T) Dev2, (buffer T) Dev2
 )"*)


(*
has been checked: all MEM related cells don't have the problem of mismatched senders, requestors, and recipients
which party sent which, and which message should be sent to which, 
which message should be deleted from which have all been clearly distinguished
*)

fun list_product :: "'a list \<Rightarrow> 'a list \<Rightarrow> ('a * 'a) list" where
  "list_product (a # as) bs = map (\<lambda>b. (a, b)) bs @ list_product as bs"
| "list_product [] bs = []"





value " table_cube"

\<comment>\<open>legacy table cube, not used for generating possible transition list anymore
definition protocol_table_cube :: "(nat * nat * nat) list"
  where
  "protocol_table_cube = (List.concat (List.map (\<lambda>(i, j). [(i, j, 0), (i, j, 1)] ) [(1, 1), (1, 2), (2, 5), (4, 7), (5, 8), (4, 8), (15, 2), (15, 3), (IMAD_ROW, DATA_COL)]  )) @
                         (List.concat (List.map (\<lambda>(i, j). [(i, j, OFFSET + 0), (i, j, OFFSET + 1)]) [(1, 1), (2, 1), (3, 1), (1, 2)] ) )"
\<close>          


\<comment>\<open> For SPG violation\<close>
definition "InvalidSnpDataBad' T i = (if ( CSTATE Invalid T i \<and> nextSnoopIs SnpData T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI Invalid i T] else [] )"
definition "InvalidSnpDataBad T i = map update_clock (InvalidSnpDataBad' T i)"
  
definition "InvalidSnpInvBad' T i = (if ( CSTATE Invalid T i \<and> nextSnoopIs SnpInv T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI Invalid i T] else [] )"
definition "InvalidSnpInvBad T i = map update_clock (InvalidSnpInvBad' T i)"

definition "IMADSnpDataBad' T i = (if ( CSTATE IMAD T i \<and> nextSnoopIs SnpData T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI IMAD i T] else [] )"
definition "IMADSnpDataBad T i = map update_clock (IMADSnpDataBad' T i)"


definition "IMADSnpInvBad' T i = (if ( CSTATE IMAD T i \<and> nextSnoopIs SnpInv T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI IMAD i T] else [] )"
definition "IMADSnpInvBad T i = map update_clock (IMADSnpInvBad' T i)"

definition "ISADSnpDataBad' T i = (if ( CSTATE ISAD T i \<and> nextSnoopIs SnpData T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI ISAD i T] else [] )"
definition "ISADSnpDataBad T i = map update_clock (ISADSnpDataBad' T i)"

definition "ISADSnpInvBad' T i = (if ( CSTATE ISAD T i \<and> nextSnoopIs SnpInv T i ) then 
  [sendSnpResp (getSnoopOrMakeup (getSnoops i T)) RspIHitI ISAD i T] else [] )"
definition "ISADSnpInvBad T i = map update_clock (ISADSnpInvBad' T i)"


definition "HostSADRspIHitIBad' T i = (if ( HSTATE SAD T  \<and> nextSnpRespIs RspIHitI T i  ) then 
  [clearBuffer (sendGOFromSnpRespForwardData  (nextSnoopRespID T i) i Shared GO SharedM T) ] else [] )"
definition "HostSADRspIHitIBad T i = map update_clock (HostSADRspIHitIBad' T i)"

\<comment>\<open>This rule also violates Data-GO atomicity and no multiple-snoops rule\<close>
definition "HostMARdOwnBad' T i = (if ( HSTATE MA T  \<and> nextReqIs RdOwn T i ) then 
  [clearBuffer (sendSnoop SnpInv i MA T) ] else [] )"
definition "HostMARdOwnBad T i = map update_clock (HostMARdOwnBad' T i)"

\<comment>\<open>end of SPG-vioating rules\<close>

\<comment>\<open>For GTS violation rules\<close>


\<comment>\<open>Rule allows the final phase of getting from a GTS violation to MESI violation
20240126\<close>
definition "HostModifiedRspIHitIBad' T i = (if HSTATE ModifiedM T \<and> nextSnpRespIs RspIHitI T i 
  then [ clearBuffer (sendGOFromSnpRespForwardData  (nextSnoopRespID T i) i Modified GO ModifiedM T) ] else [])" 

definition "HostSADRspIFwdMBad' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspIFwdM T i 
  then [ clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 


definition "HostSADRspSFwdMBad' T i = (if HSTATE SAD T \<and> nextSnpRespIs RspSFwdM T i 
  then [clearBuffer ( sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SD T) ] else [])" 
definition "HostMADRspIFwdMBad' T i = (if HSTATE MAD T \<and> nextSnpRespIs RspIFwdM T i 
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO MD T)  ] else [])"

definition "HostMARspIFwdMBad' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIFwdM T i 
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"
\<comment>\<open>TODO: need to add SAD --> SA where data is processed first
\<close>

definition "HostSARspIFwdMBad' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspIFwdM T i 
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"
definition "HostSARspSFwdMBad' T i = (if  HSTATE SA T \<and> nextSnpRespIs RspSFwdM T i 
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Shared GO SharedM T)] else [])"


\<comment>\<open>Sent in case a dirtyevict was serialised before (interrupted by) a RdOwn\<close>
definition "HostMADDirtyEvictBad' T i = (if HSTATE MAD T \<and> nextReqIs DirtyEvict  T i 
  then  [ clearBuffer (sendEvictResp GO_WritePull i MAD (nextReqID T i) T )]  else [])"

\<comment>\<open>Might happen if snoop arrives after device started DEvict, but that DEvict reached Host after the snoop's data  arrived\<close>
definition "HostMADirtyEvictBad' T i = (if HSTATE MA T \<and> nextReqIs DirtyEvict  T i 
  then  [ clearBuffer (sendEvictResp GO_WritePull i MA (nextReqID T i) T) ]  else [])"

\<comment>\<open>Might happen if snoop arrives after device started DEvict, but that DEvict reached Host after the snoop's  response arrived \<close>
definition "HostMDDirtyEvictBad' T i = (if HSTATE MD T \<and> nextReqIs DirtyEvict  T i 
  then  [ clearBuffer (sendEvictResp GO_WritePull i MD (nextReqID T i) T) ]  else [])"

\<comment>\<open>Rule allows GTS violation if the other device has an unreturned snoop
20240126\<close>
definition "HostMARspIHitSEBad' T i = (if HSTATE MA T \<and> nextSnpRespIs RspIHitSE T i
  then [clearBuffer (sendGOFromSnpResp  (nextSnoopRespID T i) i Modified GO ModifiedM T)  ] else [])"


definition "HostSADRspIFwdMBad T i = map update_clock (HostSADRspIFwdMBad' T i)"
definition "HostSADRspSFwdMBad T i = map update_clock (HostSADRspSFwdMBad' T i)"
definition "HostMADRspIFwdMBad T i = map update_clock (HostMADRspIFwdMBad' T i)"
definition "HostMARspIFwdMBad T i = map update_clock (HostMARspIFwdMBad' T i)"
definition "HostSARspIFwdMBad T i = map update_clock (HostSARspIFwdMBad' T i)"
definition "HostSARspSFwdMBad T i = map update_clock (HostSARspSFwdMBad' T i)"
definition "HostMADDirtyEvictBad T i = map update_clock (HostMADDirtyEvictBad' T i)"
definition "HostMADirtyEvictBad T i = map update_clock (HostMADirtyEvictBad' T i)"
definition "HostMDDirtyEvictBad T i = map update_clock (HostMDDirtyEvictBad' T i)"
definition "HostModifiedRspIHitIBad T i = map update_clock (HostModifiedRspIHitIBad' T i)"
definition "HostMARspIHitSEBad T i = map update_clock (HostMARspIHitSEBad' T i)"

\<comment>\<open>end of GTS-vioating rules\<close>


definition badTransitions_SPG :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "badTransitions_SPG = [
InvalidSnpDataBad,                  
InvalidSnpInvBad,                    
IMADSnpDataBad,                     
IMADSnpInvBad,                     
ISADSnpInvBad,
ISADSnpDataBad,
HostSADRspIHitIBad,
HostMARdOwnBad                
]
  "


definition badTransitions_GTS :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "badTransitions_GTS = [
HostSADRspIFwdMBad,                  
HostSADRspSFwdMBad,
HostMADRspIFwdMBad,
HostMARspIFwdMBad,
HostSARspIFwdMBad,
HostSARspSFwdMBad,
HostMADDirtyEvictBad,
HostMADirtyEvictBad,
HostMDDirtyEvictBad,
HostModifiedRspIHitIBad,
HostMARspIHitSEBad      
]"


definition "badTransitions = badTransitions_SPG @ badTransitions_GTS "


\<comment>\<open> Rules removed either because they are not possible or to simplify verification (as they are not essential)
InvalidSnpData,
SharedSnpData,

InvalidSnpInv,
ISADSnpData,
ISADSnpInv,
IMADSnpInv,
\<close>
\<comment>\<open>IIAGO_WritePullDrop should be discarded as G_WPD is not allowed in CXL\<close>



definition allTransitions' :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "allTransitions' = [
InvalidLoad',
SharedLoad',
InvalidStore',
SharedStore',
SharedEvict',
SharedEvictData',
ModifiedEvict',
SharedSnpInv',
ISDSnpInv',
ISDData',
ISDIData',
IMADData',
SMADData',
IMADGO',
ISADGO',
ISADData',
SMADGO',
SMAGO',
SMADSnpInv',
SMDData',
IMAGO',
ISAGO',
ModifiedStore',
ModifiedLoad',
SIAGO_WritePull',
SIAGO_WritePullDrop',
IIAGO_WritePullDrop',
IIAGO_WritePull',
IMDData',
MIASnpDataInvalid',
MIASnpDataShared',
MIASnpInv',
MIAGO_WritePull',
SIASnpInv',
ModifiedSnpInv',
ModifiedSnpDataShared',
ModifiedSnpDataInvalid',
HostInvalidRdShared',
HostInvalidRdOwn',
HostSharedRdShared',
HostShared_CleanEvict_NotLastDrop',
HostShared_CleanEvict_NotLastData',
HostShared_CleanEvict_Last',
HostShared_CleanEvictNoData_NotLast',
HostShared_CleanEvictNoData_Last',
HostShared_DirtyEvict',
HostModifiedDirtyEvict',
HostModifiedRdShared',
HostModifiedRdOwn',
HostSharedRdOwn',
HostSharedRdOwnSelf',
HostSDData',
HostSADData',
HostMDData',
HostIDData',
HostMADData',
HostSADRspIFwdM',
HostSADRspSFwdM',
HostMADRspIFwdM',
HostMARspIFwdM',
HostSARspIFwdM',
HostSARspSFwdM',
HostIBDataPrevious',
HostSBData',
HostMBData',
HostInvalidDirtyEvict',
HostMARspIHitSE',
SIACGO'
]"


definition allTransitions :: "(Type1State \<Rightarrow> nat \<Rightarrow> Type1State list) list" where 
  "allTransitions = [
InvalidLoad,
SharedLoad,
InvalidStore,
SharedStore,
SharedEvict,
SharedEvictData,
ModifiedEvict,
SharedSnpInv,
ISDSnpInv,
ISDData,
ISDIData,
IMADData,
SMADData,
IMADGO,
ISADGO,
ISADData,
SMADGO,
SMAGO,
SMADSnpInv,
SMDData,
IMAGO,
ISAGO,
ModifiedStore,
ModifiedLoad,
SIAGO_WritePull,
SIAGO_WritePullDrop,
IIAGO_WritePullDrop,
IIAGO_WritePull,
IMDData,
MIASnpDataInvalid,
MIASnpDataShared,
MIASnpInv,
MIAGO_WritePull,
SIASnpInv,
ModifiedSnpInv,
ModifiedSnpDataShared,
ModifiedSnpDataInvalid,
HostInvalidRdShared,
HostInvalidRdOwn,
HostSharedRdShared,
HostShared_CleanEvict_NotLastDrop,
HostShared_CleanEvict_NotLastData,
HostShared_CleanEvict_Last,
HostShared_CleanEvictNoData_NotLast,
HostShared_CleanEvictNoData_Last,
HostShared_DirtyEvict,
HostModifiedDirtyEvict,
HostModifiedRdShared,
HostModifiedRdOwn,
HostSharedRdOwn,
HostSharedRdOwnSelf,
HostSDData,
HostSADData,
HostMDData,
HostIDData,
HostMADData,
HostSADRspIFwdM,
HostSADRspSFwdM,
HostMADRspIFwdM,
HostMARspIFwdM,
HostSARspIFwdM,
HostSARspSFwdM,
HostIBDataPrevious,
HostSBData,
HostMBData,

HostInvalidDirtyEvict,
HostMARspIHitSE,
SIACGO
]"


definition onestep :: "Type1State \<Rightarrow> Type1State list"
where
   "onestep T = (concat (map (\<lambda>f. f T 0 @ f T 1) allTransitions))"



                             














definition empty_dev_cl_map :: "DeviceID \<Rightarrow> CLEntry"
  where "empty_dev_cl_map  = (\<lambda>devi. \<lparr>CLEntry.content = Some 0, block_state = Invalid\<rparr>)"


definition write42 :: "Program" where
  "write42 = (\<lambda>devi. (case devi of Dev1 \<Rightarrow> ([Write 42]) |  Dev2 \<Rightarrow> []))"


definition empty_entry :: "CLEntry" where
  "empty_entry = \<lparr>CLEntry.content = Some 0, block_state = Invalid \<rparr>"








definition onestep_bad :: "Type1State \<Rightarrow> Type1State list"
where
   "onestep_bad T = (concat (map (\<lambda>f. (f T 0 @ f T 1)) badTransitions))"


definition onestep_mixed :: "Type1State \<Rightarrow> Type1State list"
where
  "onestep_mixed T = onestep T @ onestep_bad T"


fun mfold :: "('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a list" where
  "mfold f a [] = [] "
| "mfold f a (b # bs) = (let a1 = f a b in a1 # (mfold f a1 bs))"

\<comment>\<open>without "final" predicate\<close>
definition "chain_of_states Tlist  Plist =   (mfold (\<lambda>Tl P.  (filter P (concat (map onestep Tl))) ) Tlist Plist) "
                                                                                   
definition "chain_of_bad_states Tlist  Plist =   (mfold (\<lambda>Tl P.  (filter P (concat (map onestep_mixed Tl))) ) Tlist Plist) "

\<comment>\<open>returns a list, where each represents all states that satisfy the predicate P in Plist\<close>
definition "chain_of_list_states Tlist  Plist =   (mfold (\<lambda>Tl P.  (filter P (concat (map onestep Tl))) ) Tlist Plist) "


\<comment>\<open>returns a list, where each represents all states that satisfy the predicate P in Plist, allowing bad transition\<close>
definition "chain_of_states_mixed Tlist  Plist =   (mfold (\<lambda>Tl P.  (filter P (concat (map onestep_mixed Tl))) ) Tlist Plist) "


definition "chain_of_states_mixed_list Tlist  Plist =  concat (mfold (\<lambda>Tl P.  (filter P (concat (map onestep_mixed Tl))) ) Tlist Plist) "





thm onestep_def

fun many_steps_aux :: "Type1State list \<Rightarrow> nat \<Rightarrow>  Type1State list"
  where 
    "many_steps_aux Tlist (Suc n) = many_steps_aux (List.concat (List.map  (\<lambda>T'. onestep T') Tlist)) n"
  | "many_steps_aux Tlist 0 = Tlist"

fun many_steps :: "Type1State \<Rightarrow> nat \<Rightarrow> Type1State list"
  where "many_steps T n = many_steps_aux [T] n"


definition "bufferType snpt msgop = (case msgop of None \<Rightarrow> False | Some m \<Rightarrow> getSpecificTypeSnoop m = snpt)"

fun messageAtLast :: "(Message \<Rightarrow> bool) \<Rightarrow> Message list \<Rightarrow> bool"
  where "messageAtLast P [] = False"
  |     "messageAtLast P [lastm] = P lastm"
  |     "messageAtLast P (a # b # as) = messageAtLast P (b # as)"



end