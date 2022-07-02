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

"contractLoop m [] [] terms = settle m terms" |
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
           apply auto
    apply (smt (verit, ccfv_SIG) ApplyResult.inject applyCases.simps(1))
   apply (meson ApplyResult.inject)
  by (metis applyCases.simps(3))

lemma applyCasesDistributiveAgainstAppend : "(\<And> applyWarn newState cont . applyCases env curState head l1 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                         \<Longrightarrow> (\<And> applyWarn newState cont . applyCases env curState head l2 = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)
                        \<Longrightarrow> (applyCases env curState head (l1 @ l2) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  apply (induction l1)
   apply simp
  apply (elim applyCases.elims)
           apply auto
    apply metis
  apply metis
  by metis

lemma applyInputContractLoopNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> (\<And> applyWarn newState cont. applyInput env curState head (contractLoop m ps qs terms) = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
  and applyInputHandleChooseNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set qs \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleChoose m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
and applyInputHandleDepositNoWarnings : "invariantHoldsForAuction terms m ps qs curState \<Longrightarrow> x \<in> set ps \<Longrightarrow> (\<And> applyWarn newState cont. applyCases env curState head [ handleDeposit m ps qs terms x ] = Applied applyWarn newState cont \<Longrightarrow> applyWarn = ApplyNoWarning)"
    apply (induction m ps qs terms and m ps qs terms x and m ps qs terms x rule:"contractLoop_handleChoose_handleDeposit.induct" )
  subgoal
    apply (elim applyCases.elims)
             apply auto
    by (metis ApplyResult.inject ApplyResult.simps(3) applyCases.simps(10))
  subgoal
    apply (simp only:handleDeposit.simps)
    apply (elim applyCases.elims)
             apply simp_all
    apply (split if_split_asm)
       apply (split if_split_asm)
        apply (meson ApplyResult.inject)
       apply (metis Action.inject(1) Case.inject evalValue.simps(12) invariantHoldsForAuction_def)
      apply (metis ApplyResult.simps(3) applyCases.simps(10))
     apply (meson Action.distinct(1) Case.inject)
    by (meson Action.distinct(3) Case.inject)
    apply simp
    apply (metis ApplyResult.simps(3) applyInput.simps(2) applyInput.simps(3) settle.elims)
   apply (smt (verit, best) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(2))
  by (smt (verit, ccfv_SIG) applyCasesDistributiveAgainstAppend applyCasesOfMap applyInput.simps(1) contractLoop.simps(3))


lemma auctionSettlementSafe_reduceContractStepEmpty : "invariantHoldsForAuction terms m [] [] fixSta \<Longrightarrow>
                                                       reduceContractStep env fixSta (contractLoop m [] [] terms) = Reduced wa ef sta cont \<Longrightarrow> cont = Close"
  apply (auto)
  apply (cases m)
   apply (simp add: closeIdemp_reduceContractStep)
  apply (auto simp del:reduceContractStep.simps)
  apply auto
proof -
  fix a :: Value and b :: Party
  assume a1: "(let moneyToPay = evalValue env fixSta a in if moneyToPay \<le> 0 then let warning = ReduceNonPositivePay b (Party (owner terms)) token_ada moneyToPay in Reduced warning ReduceNoPayment fixSta Close else let balance = moneyInAccount b token_ada (accounts fixSta); paidMoney = min balance moneyToPay; newBalance = balance - paidMoney; newAccs = updateMoneyInAccount b token_ada newBalance (accounts fixSta); warning = if paidMoney < moneyToPay then ReducePartialPay b (Party (owner terms)) token_ada paidMoney moneyToPay else ReduceNoWarning; (payment, finalAccs) = giveMoney b (Party (owner terms)) token_ada paidMoney newAccs in Reduced warning payment (fixSta\<lparr>accounts := finalAccs\<rparr>) Close) = Reduced wa ef sta cont"
  have f2: "\<forall>r ra s c rb rc sa ca. (Reduced r ra s c = Reduced rb rc sa ca) = (r = rb \<and> ra = rc \<and> s = sa \<and> c = ca)"
    by blast
  have f3: "(moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a) = (moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0)"
    by auto
  obtain rr :: "ReduceEffect \<times> ((Party \<times> Token) \<times> int) list \<Rightarrow> ReduceEffect" and pps :: "ReduceEffect \<times> ((Party \<times> Token) \<times> int) list \<Rightarrow> ((Party \<times> Token) \<times> int) list" where
f4: "giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)) = (rr (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta))), pps (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta))))"
  by (meson old.prod.exhaust)
  { assume "Reduced (ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a)) (rr (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))) (fixSta \<lparr>accounts := pps (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))\<rparr>) Close \<noteq> Reduced wa ef sta cont"
    { assume "Reduced (ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a)) (rr (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))) (fixSta \<lparr>accounts := pps (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))\<rparr>) Close \<noteq> (case giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)) of (r, ps) \<Rightarrow> Reduced (if (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) < evalValue env fixSta a then ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a) else ReduceNoWarning) r (fixSta\<lparr>accounts := ps\<rparr>) Close)"
      { assume "Reduced wa ef sta cont \<noteq> Reduced (if (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) < evalValue env fixSta a then ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a) else ReduceNoWarning) (rr (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))) (fixSta \<lparr>accounts := pps (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))\<rparr>) Close"
        then have "Reduced wa ef sta cont \<noteq> (case (rr (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta))), pps (giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)))) of (r, ps) \<Rightarrow> Reduced (if (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) < evalValue env fixSta a then ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a) else ReduceNoWarning) r (fixSta\<lparr>accounts := ps\<rparr>) Close)"
          by force
        then have "Reduced (ReduceNonPositivePay b (Party (owner terms)) token_ada (evalValue env fixSta a)) ReduceNoPayment fixSta Close = (if evalValue env fixSta a \<le> 0 then Reduced (ReduceNonPositivePay b (Party (owner terms)) token_ada (evalValue env fixSta a)) ReduceNoPayment fixSta Close else case giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)) of (r, ps) \<Rightarrow> Reduced (if (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) < evalValue env fixSta a then ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a) else ReduceNoWarning) r (fixSta\<lparr>accounts := ps\<rparr>) Close)"
          using f4 a1 by (smt (z3)) }
      then have "cont = Close \<or> Reduced (ReduceNonPositivePay b (Party (owner terms)) token_ada (evalValue env fixSta a)) ReduceNoPayment fixSta Close = (if evalValue env fixSta a \<le> 0 then Reduced (ReduceNonPositivePay b (Party (owner terms)) token_ada (evalValue env fixSta a)) ReduceNoPayment fixSta Close else case giveMoney b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (updateMoneyInAccount b token_ada (moneyInAccount b token_ada (accounts fixSta) + - 1 * (if moneyInAccount b token_ada (accounts fixSta) + - 1 * evalValue env fixSta a \<le> 0 then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a)) (accounts fixSta)) of (r, ps) \<Rightarrow> Reduced (if (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) < evalValue env fixSta a then ReducePartialPay b (Party (owner terms)) token_ada (if moneyInAccount b token_ada (accounts fixSta) \<le> evalValue env fixSta a then moneyInAccount b token_ada (accounts fixSta) else evalValue env fixSta a) (evalValue env fixSta a) else ReduceNoWarning) r (fixSta\<lparr>accounts := ps\<rparr>) Close)"
        by fastforce }
    then have ?thesis
      using f3 f2 a1 by (smt (z3)) }
  then show ?thesis
    by fastforce
qed


lemma contractLoopReducedEqualsSettlement : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                             invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                             reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow> 
                                             (cont = settle m terms \<and> fixSta = sta)"
  by (smt (verit, ccfv_SIG) ReduceStepResult.distinct(1) ReduceStepResult.distinct(3) ReduceStepResult.inject case_prod_conv contractLoop.elims old.prod.exhaust reduceContractStep.simps(4))

lemma contractLoopReducedSatisfyInvariant : "ps \<noteq> [] \<or> qs \<noteq> [] \<Longrightarrow>
                                             invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                             reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow>
                                             cont = settle m terms \<Longrightarrow> 
                                             invariantHoldsForAuction terms m [] [] sta"
  by (smt (verit, best) contractLoopReducedEqualsSettlement in_set_member invariantHoldsForAuction_def member_rec(2))


lemma auctionSettlementSafe_reduceContractStep : "invariantHoldsForAuction terms m ps qs fixSta \<Longrightarrow>
                                                  reduceContractStep env fixSta (contractLoop m ps qs terms) = Reduced wa ef sta cont \<Longrightarrow> 
                                                  cont = Close \<or> (cont = settle m terms \<and> invariantHoldsForAuction terms m [] [] sta)"
  by (metis auctionSettlementSafe_reduceContractStepEmpty contractLoopReducedEqualsSettlement contractLoopReducedSatisfyInvariant)


