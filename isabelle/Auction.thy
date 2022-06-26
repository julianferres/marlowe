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
  apply auto
  apply (induction bidders)
   apply (simp add: closeIsSafe_reduceContractStep)
  apply simp
  apply (cases "slotInterval env")
  by (smt (z3) ReduceStepResult.inject ReduceStepResult.simps(3) ReduceStepResult.simps(5) old.prod.case)


definition invariantHoldsForAuction :: "AuctionTerms \<Rightarrow> AuctionWinner \<Rightarrow> Party list \<Rightarrow> Party list \<Rightarrow> State \<Rightarrow> bool" where
"invariantHoldsForAuction terms m ps qs curState = ((\<forall>x . x \<in> set qs \<longrightarrow> \<not> member (partyToValueId x) (boundValues curState))
                                                  \<and> (\<forall>x . x \<in> set ps \<longrightarrow> findWithDefault 0 (partyToValueId x) (boundValues curState) > 0)
                                                  \<and> (\<forall>x y . m = Some (x, y) \<longrightarrow> ((lookup (y, token_ada) (accounts curState) = lookup (partyToValueId y) (boundValues curState))
                                                          \<and> (findWithDefault 0 (partyToValueId y) (boundValues curState) > 0)
                                                          \<and> (UseValue (partyToValueId y)) = x))
                                                  \<and> (minBid terms > 0))"


lemma applyCasesOfMap : "(\<And> p applyWarn newState cont2. p \<in> set ps \<Longrightarrow> applyCases env curState head [f p] = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning)
                               \<Longrightarrow> (applyCases env curState head (map f ps) = Applied applyWarn newState cont2 \<Longrightarrow> applyWarn = ApplyNoWarning)"
  apply (induction ps)
    apply simp
  apply (elim applyCases.elims)
           apply (smt (verit, ccfv_SIG) Cons_eq_map_conv applyCases.simps(1) insert_iff list.inject list.set(2))
          apply (metis ApplyResult.inject Cons_eq_map_conv insert_iff list.inject list.set(2))
         apply (smt (z3) Cons_eq_map_D applyCases.simps(3) insert_iff list.inject list.set(2))
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  by fastforce

lemma applyCasesDistributiveAgainstAppend : "(\<And> applyWarn newState cont . applyCases env curState head l1 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                         \<Longrightarrow> (\<And> applyWarn newState cont . applyCases env curState head l2 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                        \<Longrightarrow> (applyCases env curState head (l1 @ l2) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  apply (induction l1)
   apply simp
  apply (elim applyCases.elims)
           apply (smt (verit) append_Cons applyCases.simps(1) list.inject)
          apply (metis ApplyResult.inject append_Cons applyCases.simps(2) list.inject)
         apply (metis Cons_eq_append_conv applyCases.simps(3) list.inject)
        apply fastforce
       apply fastforce
      apply fastforce
     apply fastforce
    apply fastforce
   apply fastforce
  by fastforce

lemma applyInputContractLoopNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> (\<And> applyWarn newState cont. applyInput env curState head (contractLoop m ps qs terms) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  and applyInputHandleChooseNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set qs \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleChoose m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
and applyInputHandleDepositNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set ps \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleDeposit m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
    apply (induction m ps qs terms and m ps qs terms x and m ps qs terms x rule:"contractLoop_handleChoose_handleDeposit.induct" )
      defer
      defer
      apply simp
     apply (smt (verit, best) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(2))
    apply (smt (verit, ccfv_SIG) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(3))
  oops









  oops
