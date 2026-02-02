theory Circus_Actions
  imports "UTP-Stateful-Failure.utp_sf_rdes" (* "Interaction_Trees.ITrees" *)
begin 

typedef ('e, 's) action = "{P :: ('s, 'e) sfrd hrel. P is NCSP}"
  by blast

setup_lifting type_definition_action

lift_definition Skip :: "('e, 's) action" is "utp_sfrd_healths.Skip" by (simp add: closure)

lift_definition Stop :: "('e, 's) action" is "utp_sfrd_healths.Stop" by (simp add: closure)

lift_definition assigns_action :: "'s subst \<Rightarrow> ('e, 's) action" is AssignsCSP by (simp add: closure)

lift_definition seq_action :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is "(;;)" 
  by (simp add: closure) 

adhoc_overloading useq == seq_action

lift_definition cond_action :: "('e, 's) action \<Rightarrow> (bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
  is "\<lambda> P b Q. P \<triangleleft> b \<triangleright>\<^sub>R Q" by (simp add: closure)

lift_definition extchoice_action :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" (infixl "\<box>" 59) is "\<lambda> P Q. P \<box> Q"
  by (simp add: closure)

lift_definition EXTCHOICE_action :: "'a set \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is "EXTCHOICE"
  by (simp add: closure)

no_notation extChoice (infixl "\<box>" 59)

lift_definition prefix_action :: "('e, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is PrefixCSP
  by (simp add: closure)

lift_definition guardedchoice_action :: "'e set \<Rightarrow> ('e \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is GuardedChoiceCSP
  by (simp add: closure)
                                                                             
lift_definition guard_action :: "(bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is GuardCSP
  by (metis NCSP_Guard SEXP_def)               

lemma "P is NCSP \<Longrightarrow> GuardCSP b P is NCSP"
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

(*Cond action and conditional simplification*)
lemma "cond_action (guard_action b P) c (guard_action c Q) = 
      guard_action (if (i=0) then b else c) (if (i=0) then P else Q)"
  apply transfer
  sorry

subsection \<open> Normalisation Laws \<close>

(*Lemma 1: Sequential Prefix Normalisation*)
lemma "(prefix_action e P) ;; Q = prefix_action e (P ;; Q)"
  apply transfer
  apply (simp add: NCSP_implies_CSP PrefixCSP_seq)
  done


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