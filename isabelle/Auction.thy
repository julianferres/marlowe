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

type_synonym contractLoopType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms"
type_synonym handleChooseType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"
type_synonym handleDepositType = "AuctionWinner \<times> Party list \<times> Party list \<times> AuctionTerms \<times> Party"

fun evalBoundAuction :: "(contractLoopType + (handleChooseType + handleDepositType)) \<Rightarrow> nat" where
"evalBoundAuction (Inl (_, ps, qs, _)) = (length ps) + 2 * (length qs)" |
"evalBoundAuction (Inr (Inl (_, ps, qs, _, _))) = (length ps) + 2 * (length qs)" |
"evalBoundAuction (Inr (Inr (_, ps, qs, _, _))) = (length ps) + 2 * (length qs)"


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
  apply simp
  oops

(*
fun auction :: "Party \<Rightarrow> int \<Rightarrow> int \<Rightarrow> Party list \<Rightarrow> Slot \<Rightarrow> Contract" where
"auction own mBid MBid bidders ddl = (contractLoop None [] bidders \<lparr>owner = own, minBid = mBid, maxBid = MBid, deadline = ddl\<rparr>)" 

Finding Lexicographic Orders for Termination Proofs in Isabelle/HOL


lemma auctionComputeTransactionIsSafe : "computeTransaction tra sta (auction own mBid MBid bidders ddl)  = TransactionOutput trec \<Longrightarrow> 
                         txOutWarnings trec = []"
  oops

theorem auctionPlayTraceIsSafe : "playTrace sl (auction own mBid MBid bidders ddl) t = TransactionOutput trec \<Longrightarrow>
                                  txOutWarnings trec = []"
  oops
*)
