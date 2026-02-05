section \<open> IsaCircus \<close>

theory Circus_Actions
  imports 
    "UTP-Stateful-Failure.utp_sf_rdes"
    Circus_Hiding
    Circus_Parallel
    "Circus_Toolkit.Channels_Events"
    "Circus_Toolkit.Action_Command"
begin 


unbundle no lattice_syntax
unbundle UTP_Syntax

no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types \<close>

typedef ('e, 's) action = "{P :: ('s, 'e) sfrd hrel. P is NCSP}"
  by blast

type_synonym ('a, 'e) chan = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"

setup_lifting type_definition_action

subsection \<open> Semantic Constructors \<close>

lift_definition Skip :: "('e, 's) action" is "utp_sfrd_healths.Skip" by (simp add: closure)

lift_definition Stop :: "('e, 's) action" is "utp_sfrd_healths.Stop" by (simp add: closure)

lift_definition cassigns :: "'s subst \<Rightarrow> ('e, 's) action" is AssignsCSP by (simp add: closure)

lift_definition cseq :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is "(;;)" 
  by (simp add: closure) 

adhoc_overloading useq == cseq

definition cseqIte :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where
"cseqIte A P = Finite_Set.fold (\<lambda> i. cseq (P i)) Skip A"

lift_definition cond_action :: "('e, 's) action \<Rightarrow> (bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
  is "\<lambda> P b Q. P \<triangleleft> b \<triangleright>\<^sub>R Q" by (simp add: closure)

lift_definition cextchoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" (infixl "\<box>" 59) is "\<lambda> P Q. P \<box> Q"
  by (simp add: closure)

lift_definition cExtChoice :: "'a set \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is "EXTCHOICE"
  by (simp add: closure)

definition crenaming :: "('e \<leftrightarrow> 'f) \<Rightarrow> ('e, 's) action \<Rightarrow> ('f, 's) action" where "crenaming = undefined"

lift_definition chide :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action" is "HideCSP" by (simp add:closure)

lift_definition cparallel :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
is "\<lambda> P cs Q. P \<lbrakk>cs\<rbrakk>\<^sub>C Q" by (simp add: closure)

definition "cinterleave P Q = cparallel P {} Q"

definition cInterleave :: "'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where
"cInterleave A P = Finite_Set.fold (\<lambda> i. cinterleave (P i)) Skip A"

definition cParallelIte :: "'e set \<Rightarrow> 'i set \<Rightarrow> ('i \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where
"cParallelIte cs A P = Finite_Set.fold (\<lambda> i Q. cparallel (P i) cs Q) Skip A"

lift_definition csync :: "(unit, 'e) chan \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" 
  is "\<lambda> c P. PrefixCSP (c\<cdot>())\<^sub>u P" by (simp add: closure)

lift_definition cinput :: "('a, 'e) chan \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action"
  is "\<lambda> c P. InputCSP c (\<lambda> v. (True)\<^sub>e) P" by (simp add: closure)

lift_definition coutput :: "('a, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" 
  is OutputCSP by (simp add: closure)

definition coutinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"coutinp c e A = undefined"

definition cdotinp :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr  \<Rightarrow> ('b \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotinp c e A = undefined"

definition cdotdot :: "('a \<times> 'b, 'e) chan \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdot c e1 e2 A = undefined"

definition cdotdotinp :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr  \<Rightarrow> ('c \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotinp c e1 e2 A = undefined"

definition cdotdotout :: "('a \<times> 'b \<times> 'c, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow>('c, 's) expr  \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdotout c e1 e2 e3 A = undefined"

definition cdotdotdotinp :: "('a \<times> 'b \<times> 'c \<times> 'd, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr   \<Rightarrow> ('c, 's) expr \<Rightarrow> ('d \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" where 
"cdotdotdotinp c e1 e2 e3 A = undefined"

definition cdotdotdotout :: "('a \<times> 'b \<times> 'c \<times> 'd, 'e) chan \<Rightarrow>('a, 's) expr \<Rightarrow> ('b, 's) expr   \<Rightarrow> ('c, 's) expr \<Rightarrow>('d, 's) expr \<Rightarrow>  ('e, 's) action \<Rightarrow> ('e, 's) action" where 
"cdotdotdotout c e1 e2 e3 e4 A = undefined"

lift_definition guardedchoice_action :: "'e set \<Rightarrow> ('e \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is GuardedChoiceCSP
  by (simp add: closure)
                                                                             
lift_definition cguard :: "(bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is GuardCSP
  by (metis NCSP_Guard SEXP_def)               

instantiation action :: (type, type) lattice
begin

lift_definition less_eq_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> bool" is "(\<sqsupseteq>)" .

lift_definition less_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> bool" is "(\<sqsupset>)" .

lift_definition sup_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> ('a, 'b) action"
  is "(\<sqinter>)" by (simp add: closure)

lift_definition inf_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> ('a, 'b) action"
  is "join (utp_order NCSP)" by simp 

instance 
   apply (intro_classes; transfer)
  apply simp_all
  apply (metis ref_preorder.dual_order.strict_iff_not)
  apply (meson csp_theory.join_left)
  apply (meson csp_theory.join_right)
  apply (meson csp_theory.join_le)
  done

end

instantiation action :: (type, type) bounded_lattice
begin

lift_definition top_action :: "('a, 'b) action" is "utp_rdes_healths.Chaos"
  by (simp add: closure)

lift_definition bot_action :: "('a, 'b) action" is "utp_rdes_healths.Miracle"
  by (simp add: closure)

instance
  apply (intro_classes; transfer)
   apply blast+
  done

end

instantiation action :: (type, type) complete_lattice
begin

lift_definition Inf_action :: "('a, 'b) action set \<Rightarrow> ('a, 'b) action" is "Lattice.sup (utp_order NCSP)"
  by (simp add: subsetI)

lift_definition Sup_action :: "('a, 'b) action set \<Rightarrow> ('a, 'b) action" is "Lattice.inf (utp_order NCSP)"
  by (simp add: subsetI)

instance 
  apply (intro_classes; transfer)
  apply (simp_all add: Ball_Collect csp_theory.sup_upper csp_theory.inf_lower)
  apply (metis csp_theory.sup_least is_Healthy_subset_member utp_order_carrier)
  apply (metis csp_theory.inf_greatest is_Healthy_subset_member utp_order_carrier)
  done

end

instantiation action :: (type, type) refine
begin

definition ref_by_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> bool" where
  "ref_by_action = (\<ge>)"

definition sref_by_action :: "('a, 'b) action \<Rightarrow> ('a, 'b) action \<Rightarrow> bool" where
  "sref_by_action = (>)"

instance
  apply (intro_classes, unfold_locales)
    apply (metis Circus_Actions.ref_by_action_def Circus_Actions.sref_by_action_def inf.order_iff
      inf.strict_order_iff inf_commute)
   apply (simp add: Circus_Actions.ref_by_action_def)
  apply (simp add: ref_by_action_def)
  done

end

lemma refine_action_transfer [transfer_rule]: "rel_fun cr_action (rel_fun cr_action (=)) (\<sqsubseteq>) (\<sqsubseteq>)"
  by (simp add: Transfer.Rel_def rel_fun_def cr_action_def less_eq_action.rep_eq ref_by_action_def)

abbreviation Miracle :: "('a, 'b) action" where "Miracle \<equiv> bot_class.bot"

abbreviation Chaos :: "('a, 'b) action" where "Chaos \<equiv> top_class.top"

subsection \<open> Syntax \<close>

bundle Circus_Syntax
begin

unbundle Expression_Syntax

no_notation disj (infixr "|" 30)
no_notation conj (infixr "&" 35)
no_notation funcset (infixr "\<rightarrow>" 60)

no_syntax
  "_maplet"  :: "['a, 'a] \<Rightarrow> maplet"             ("_ /\<mapsto>/ _")
  ""         :: "maplet \<Rightarrow> updbind"              ("_")
  ""         :: "maplet \<Rightarrow> maplets"             ("_")
  "_Maplets" :: "[maplet, maplets] \<Rightarrow> maplets" ("_,/ _")
  "_Map"     :: "maplets \<Rightarrow> 'a \<rightharpoonup> 'b"           ("(1[_])")


end

no_notation utp_sfrd_extchoice.extChoice (infixl "\<box>" 59)

text \<open> The types of the syntax translations represent categories in the Isabelle
  parser. 
  \<^item> @{typ id} is an identifier (i.e. a name)
  \<^item> @{typ pttrn} is a pattern, which is typically use to pattern 
    match on a parameter (e.g. @{term "\<lambda> (x, y). f x y"}.
  \<^item> @{typ logic} corresponds to any term constructable in HOL \<close>

syntax 
 \<comment> \<open> "_cseq" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ ; _" [50, 51] 50) 
    no need to define cseq syntax, cseq is overloading useq
  "_cinterrupt" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<triangle> _" [50, 51] 50)
  (*Can interrupt be defined using definition, just like cechoice??*)\<close>

  "_cinput" :: "id \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?_ \<rightarrow> _" [61, 0, 62] 62)

  "_coutput" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>!_ \<rightarrow> _" [61, 0, 62] 62)

  "_cdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>._ \<rightarrow> _" [61, 0, 62] 62)
  \<comment> \<open>_._ is parsed as a whole, so bolded here to avoid conflict\<close>

  "_coutinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>!_\<^bold>?_ \<rightarrow> _" [61, 0, 0, 62] 62)

  "_cdotinp" :: "id \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200, 200, 62] 62)


  "_cdotdot" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._ \<rightarrow> _" [61, 200, 200, 62] 62)


  "_cdotdotinp" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200,200, 200, 62] 62)


  "_cdotdotout" :: "id \<Rightarrow> logic   \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>!_ \<rightarrow> _" [61, 200,200, 200, 62] 62)

  "_cdotdotdotinp" :: "id \<Rightarrow> logic \<Rightarrow> logic  \<Rightarrow> logic \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>._\<^bold>?_ \<rightarrow> _" [61, 200,200,200, 200, 62] 62)

  "_cdotdotdotout" :: "id \<Rightarrow> logic \<Rightarrow> logic  \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic"   ("_\<^bold>._\<^bold>._\<^bold>._\<^bold>!_ \<rightarrow> _" [61, 200,200,200,200, 62] 62)

  "_csync" :: "id \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [61, 62] 61)
  "_cguard" :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [60, 61] 60)

  \<comment> \<open>the order of the parameters does not need to match the definition.\<close>
  "_crenaming" :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 60)  

  "_chide" :: "logic \<Rightarrow> chans \<Rightarrow> logic" ("_ \<Zhide> \<lbrace>_\<rbrace>" [60, 61] 60)

  "_cparallel" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk> | _ | \<rbrakk> _" [60, 0,  61] 60)
 
  "_cEChoice" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<box> _ \<in> _ \<bullet> _")

  "_cInterleave" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<interleave> _ \<in> _ \<bullet> _" [0, 0, 10] 10) 
  \<comment> \<open>\<interleave> i\<in>{1..inpSize} \<bullet> NodeIn(l,n,i)\<close>
  
  "_cseqIte" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";; _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  \<comment> \<open>;; i\<in>{1..inpSize} \<bullet> NodeIn(l,n,i)\<close>

  "_cParallelIte" :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrakk> _ \<rbrakk> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  
  "_cParam" :: "pttrn \<Rightarrow>  logic \<Rightarrow> logic" ("_ \<bullet> _" [10, 0] 10)(*TBC*) 

translations 
  "_cinput c x  P" == "CONST cinput c (\<lambda> x. P)"
  "_coutput c e P" == "CONST coutput c (e)\<^sub>e P"
  "_coutinp c e x P" == "CONST coutinp c (e)\<^sub>e (\<lambda> x. P)"
  "_cdotinp c e x P" == "CONST cdotinp c (e)\<^sub>e (\<lambda> x. P)"

  "_cdotdot c e1 e2 P" == "CONST cdotdot c (e1)\<^sub>e (e2)\<^sub>e P" 
  "_cdotdotinp c e1 e2 x P" == "CONST cdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (\<lambda> x. P)"

  "_cdotdotout c  e1 e2 e3 P" == "CONST cdotdotout c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e P" 
  "_cdotdotdotinp c  e1 e2 e3 x P" == "CONST cdotdotdotinp c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e (\<lambda> x. P)"  

  "_cdotdotdotout c  e1 e2 e3 e4 P" == "CONST cdotdotdotout c  (e1)\<^sub>e (e2)\<^sub>e (e3)\<^sub>e (e4)\<^sub>e P" 

  "_cguard b P" == "CONST cguard (b)\<^sub>e P"
  "_cdot c e P" == "CONST coutput c (e)\<^sub>e P"
  "_csync c P" == "CONST csync c P"
  "_crenaming P rn" == "CONST crenaming (_rnenum rn) P" 
  "_chide P es" == "CONST chide P (_ch_enum es)"
  "_cparallel P A Q" == "CONST cparallel P A Q " 
  "_cEChoice i A P" == "CONST cExtChoice A (\<lambda> i. P)"
  "_cInterleave i A P" == "CONST cInterleave A (\<lambda> i. P)"

  "_cseqIte i A P" == "CONST cseqIte A (\<lambda> i. P)"

  "_cParallelIte B i A P" == "CONST cParallelIte B A (\<lambda> i. P)"
  "_cParam x P" => "\<lambda> x. P"


(*Cond action and conditional simplification*)
(*
lemma "cond_action (guard_action b P) c (guard_action c Q) =
      guard_action (if (i=0) then b else c) (if (i=0) then P else Q)"
  apply transfer
  sorry
*)

subsection \<open> Normalisation Laws \<close>

(*Lemma 1: Sequential Prefix Normalisation*)
lemma "(csync e P) ;; Q = csync e (P ;; Q)"
  apply transfer
  apply (simp add: NCSP_implies_CSP PrefixCSP_seq)
  done

(*
(*Lemma 4: Binary Guarded External Choice Normalisation*)
lemma "(guard_action b P) \<box> (guard_action c Q) = 
        EXTCHOICE_action {0,1} (\<lambda> x. 
        guard_action (if x = 0 then b else c) (if x = 0 then P else Q))"
  apply transfer
  sorry

(*Lemma 5 : Guarded External Choice Normalisation*)
lemma "(EXTCHOICE_action {0..n} (\<lambda> i. guard_action (b(i)) (P(i))))
        \<box> 
        (guard_action c Q) 
        = 
        EXTCHOICE_action {0..n+1} (\<lambda> i.
        guard_action (if (i \<le> n) then b(i) else c) 
        (if (i \<le> n) then P(i) else Q))"
  apply transfer
  sorry
*)


subsection \<open> Reduction Laws \<close>

lemma extchoice_idem [simp]:
  fixes P :: "('e, 's) action"
  shows "P \<box> P = P"
  by (transfer, simp add: NCSP_implies_CSP extChoice_idem)

lemma extchoice_mono:
  fixes P\<^sub>1 P\<^sub>2 :: "('e, 's) action"
  assumes "P\<^sub>1 \<sqsubseteq> P\<^sub>2" "Q\<^sub>1 \<sqsubseteq> Q\<^sub>2"
  shows "P\<^sub>1 \<box> Q\<^sub>1 \<sqsubseteq> P\<^sub>2 \<box> Q\<^sub>2"
  using assms
  by (transfer, meson extChoice_mono)
 
(*Lemma 11: External Choice Reduction*)
lemma
  fixes Q R S :: "('e, 's) action"
  assumes "S \<sqsubseteq> Q" "S \<sqsubseteq> R"
  shows "S \<sqsubseteq> Q \<box> R"
  by (metis assms(1,2) extchoice_idem extchoice_mono)

end