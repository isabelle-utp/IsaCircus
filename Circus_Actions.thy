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

lift_definition cond_action :: "('e, 's) action \<Rightarrow> (bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
  is "\<lambda> P b Q. P \<triangleleft> b \<triangleright>\<^sub>R Q" by (simp add: closure)

lift_definition extchoice_action :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is "(\<box>)"
  by (simp add: closure)

lift_definition prefix_action :: "('e, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is PrefixCSP
  by (simp add: closure)

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

term Lattice.inf

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

abbreviation Miracle :: "('a, 'b) action" where "Miracle \<equiv> bot_class.bot"

abbreviation Chaos :: "('a, 'b) action" where "Chaos \<equiv> top_class.top"

end