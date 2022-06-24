theory Auction
imports Semantics ValidState CloseSafe
begin

definition bid :: ByteString where
"bid = [1]"

definition token_ada :: Token where
"token_ada = Token [] []"

type_synonym AuctionWinner = "(Value \<times> Party) option"

record AuctionTerms = owner :: Party
                      minBid :: int
                      maxBid :: int
                      deadline :: Slot


fun settle :: "AuctionWinner \<Rightarrow> AuctionTerms \<Rightarrow> Contract" where
  "settle None _ = Close" |
  "settle (Some (v, p)) terms = (Pay p (Party (owner terms)) token_ada v Close)"

fun choice :: "Party \<Rightarrow> ChoiceId" where
  "choice p = (ChoiceId bid p)"

(* Los bidders directamente como parties en lugar de String *)
fun partyToValueId :: "Party \<Rightarrow> ValueId" where
  "partyToValueId (PubKey pk) = ValueId pk" | 
  "partyToValueId (Role r) = ValueId r"

fun remove :: "Party \<Rightarrow> Party list \<Rightarrow> Party list" where
"remove p ls = filter ((\<noteq>) p) ls"

lemma removePresentElementReducesSize : "p \<in> set ls \<Longrightarrow> length (filter ((\<noteq>) p) ls) < length ls"
  by (simp add: length_filter_less)

lemma removeAbsentElementMantainsSize : "p \<notin> set ls \<Longrightarrow> length (filter ((\<noteq>) p) ls) = length ls"
  by (metis (mono_tags, lifting) filter_True)

type_synonym contractLoopType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms"
type_synonym handleChooseType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"
type_synonym handleDepositType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"

fun evalBoundAuction :: "(contractLoopType + (handleChooseType + handleDepositType)) \<Rightarrow> nat" where
"evalBoundAuction (Inl (_, ps, qs, _)) = 2 * length ps + 4 * length qs + 1" |
"evalBoundAuction (Inr (Inl (_, ps, qs, _, p))) = 2 * length ps + 4 * length qs + (if p \<in> set qs then 0 else 8)" |
"evalBoundAuction (Inr (Inr (_, ps, qs, _, p))) = 2 * length ps + 4 * length qs + (if p \<in> set ps then 0 else 8)"

function (sequential) contractLoop :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Contract"
and handleChoose :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Party \<Rightarrow> Case"
and handleDeposit :: "AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> AuctionTerms \<Rightarrow> Party \<Rightarrow> Case" 
where
"handleChoose m ps qs terms p = Case (Choice (choice p) [(minBid terms, maxBid terms)])
                                               (Let (partyToValueId p) 
                                                  (ChoiceValue (choice p))
                                                  (contractLoop m (p # ps) (remove p qs) terms))" |
"handleDeposit m ps qs terms p = 
   (let v = (UseValue (partyToValueId p)) in
    let ps' = (remove p ps) in
    (Case (Deposit p p token_ada v)
          (case m of
              None          \<Rightarrow> contractLoop (Some (v, p)) ps' qs terms
            | Some (v', p') \<Rightarrow> If (ValueGT v v') 
                                  (contractLoop (Some (v, p)) ps' qs terms) 
                                  (contractLoop m ps' qs terms))))" |

"contractLoop m [] [] terms = settle None terms" |
"contractLoop m ps qs terms = (When ( (map (handleChoose m ps qs terms) qs) @ 
                                      (map (handleDeposit m ps qs terms) ps)) 
                                      (deadline terms) (settle m terms))"  
  by pat_completeness auto
termination 
  apply (relation "measure (evalBoundAuction)")
  apply auto 
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize apply fastforce
  using removePresentElementReducesSize apply fastforce
  using removeAbsentElementMantainsSize by fastforce
         

fun auction :: "Party \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Party list \<Rightarrow> Slot \<Rightarrow> Contract" where
"auction own mBid MBid bidders ddl = (contractLoop None [] bidders \<lparr>owner = own, minBid = mBid, maxBid = MBid, deadline = ddl\<rparr>)" 

lemma auctionIsSafe_reduceContractStep : "reduceContractStep env fixSta (auction own mBid MBid bidders ddl) = Reduced wa ef sta cont \<Longrightarrow> wa = ReduceNoWarning"
  apply (induction bidders)
   apply (simp add: closeIsSafe_reduceContractStep)
  apply simp
  apply (cases "slotInterval env")
  by (smt (z3) ReduceStepResult.inject ReduceStepResult.simps(3) ReduceStepResult.simps(5) old.prod.case)

lemma auctionIsSafe_reductionLoop : "wa = [] \<Longrightarrow> reductionLoop reducedBefore env fixSta (auction own mBid MBid bidders ddl) wa ef = ContractQuiescent reducedAfter reduceWarns pays curState cont \<Longrightarrow> reduceWarns = []"
  apply (induction reducedBefore env fixSta "(auction own mBid MBid bidders ddl)" wa ef rule:reductionLoop.induct)
  subgoal for reducedBefore env state warnings payments
    apply (simp only:reductionLoop.simps[of reducedBefore env state "(auction own mBid MBid
           bidders ddl)" warnings payments])
    apply (simp only:reductionLoop.simps[of reducedBefore env state "(auction own mBid MBid
           bidders ddl)" "[]" payments])
    apply (induction bidders)
     apply (metis auction.simps closeIsSafe_reductionLoop contractLoop.simps(1) reductionLoop.simps settle.simps(1))
    using auctionIsSafe_reduceContractStep closeIsSafe_reductionLoop
    oops

lemma auctionIsSafe_reduceContractUntilQuiescent : "reduceContractUntilQuiescent env fixSta (auction own mBid MBid bidders ddl) = ContractQuiescent reduced reduceWarns pays curState cont \<Longrightarrow> reduceWarns = []"
  apply (induction bidders)
   apply (simp add: closeIsSafe_reduceContractUntilQuiescent)
  apply simp
  apply (cases "reduceContractStep env fixSta
               (contractLoop None [] bidders
                 \<lparr>owner = own, minBid = mBid,
                    maxBid = MBid,
                    deadline = ddl\<rparr>)")
  oops


lemma auctionIsSafe_applyInput : "applyInput env curState head (auction own mBid MBid bidders ddl) = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning"
  apply auto
  apply (induction bidders)
   apply simp
  apply (simp)
  oops

lemma auctionComputeTransactionIsSafe : "computeTransaction tra sta (auction own mBid MBid bidders ddl)  = TransactionOutput trec \<Longrightarrow>
                         txOutWarnings trec = []"
  apply (simp only:computeTransaction.simps)
  apply (auto split:IntervalResult.splits option.splits ApplyAllResult.splits
              simp del:applyAllLoop.simps)
  subgoal for env fixSta warnings payments newState cont
    apply(cases " \<not> warnings \<and>
        (contractLoop None [] bidders
          \<lparr>owner = own, minBid = mBid, maxBid = MBid, deadline = ddl\<rparr> =
         Close \<longrightarrow>
         accounts sta = [])")
    apply force
    apply (simp only:contractLoop.simps)
    apply (induction bidders)
    apply (metis TransactionOutput.inject(1) TransactionOutputRecord.select_convs(1) applyAllInputs.simps closeIsSafe_applyAllInputs contractLoop.simps(1) settle.simps(1))
    apply (simp only:contractLoop.simps handleDeposit.simps handleChoose.simps remove.simps)
    apply (simp del:applyAllLoop.simps)
    oops

(*
lemma auctionComputeTransactionIsSafe : "computeTransaction tra sta (auction own mBid MBid bidders ddl)  = TransactionOutput trec \<Longrightarrow> 
                         txOutWarnings trec = []"
  oops

theorem auctionPlayTraceIsSafe : "playTrace sl (auction own mBid MBid bidders ddl) t = TransactionOutput trec \<Longrightarrow>
                                  txOutWarnings trec = []"
  oops
*)
