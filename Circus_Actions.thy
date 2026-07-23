section \<open> IsaCircus \<close>

theory Circus_Actions
  imports 
    "UTP-Stateful-Failure.utp_sf_rdes"
    Circus_Hiding
    Circus_Renaming
    Circus_Parallel
    "Circus_Toolkit.Channels_Events"
    "Circus_Toolkit.Recursive"
    "Circus_Toolkit.IsaCircus_Syntax"
begin 

unbundle no lattice_syntax
unbundle UTP_Syntax
unbundle Circus_Syntax

no_notation extChoice (infixl "\<box>" 59)
no_notation funcset (infixr "\<rightarrow>" 60)

subsection \<open> Types \<close>

typedef ('e, 's) action = "{P :: ('s, 'e) sfrd hrel. P is NCSP}"
  by blast

setup_lifting type_definition_action

subsection \<open> Semantic Constructors \<close>

lift_definition cskip :: "('e, 's) action" is "utp_sfrd_healths.Skip" by (simp add: closure)
lift_definition cstop :: "('e, 's) action" is "utp_sfrd_healths.Stop" by (simp add: closure)
lift_definition cassigns :: "'s subst \<Rightarrow> ('e, 's) action" is AssignsCSP by (simp add: closure)
lift_definition cseq :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is "(;;)" by (simp add: closure) 
lift_definition cspec :: "('a \<Longrightarrow> 's) \<Rightarrow> 's pred \<Rightarrow> 's pred \<Rightarrow> ('e, 's) action" is SpecC by (simp add: closure)
lift_definition cassume :: "('s \<Rightarrow> \<bool>) \<Rightarrow> ('e, 's) action" is AssumeCircus by (simp add: closure)
lift_definition ccond :: "('e, 's) action \<Rightarrow> (bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
  is "\<lambda> P b Q. P \<triangleleft> b \<triangleright>\<^sub>R Q" by (simp add: closure)

lift_definition caltern_list :: "(('s \<Rightarrow> bool) \<times> ('e, 's) action) list \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is AlternateR_list
  by (rule AlternateR_list_NCSP_closed)
     (metis (no_types, lifting) Ball_set pred_prod_beta snd_conv)+

lift_definition cextchoice :: "('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is "\<lambda> P Q. extChoice P Q"
  by (simp add: closure)

lift_definition cExtChoiceIdx :: "'a set \<Rightarrow> ('a \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is "EXTCHOICE"
  by (simp add: closure)

lift_definition crename :: "('e, 's) action \<Rightarrow> ('e \<leftrightarrow> 'f) \<Rightarrow> ('f, 's) action" is RenameCSP by (simp add: closure)
lift_definition chide :: "('e, 's) action \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action" is "HideCSP" by (simp add:closure)

lift_definition cactpar :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b \<Longrightarrow> 's) \<Rightarrow> 'e set \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
is "\<lambda> ns1 ns2 cs P Q. if ns1 \<bowtie> ns2 then P \<parallel>\<^bsub>M\<^sub>C ns1 cs ns2\<^esub> Q else Miracle" by (simp add: closure)

lift_definition cparallel :: "'e set \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action"
is "\<lambda> cs P Q. P \<lbrakk>cs\<rbrakk>\<^sub>C Q" by (simp add: closure)

lift_definition cinput :: "('a, 'e) channel \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> ('e, 's) action)) \<Rightarrow> ('e, 's) action"
  is "\<lambda> c A BP. InputCSP c (\<lambda> v s. v \<in> A \<and> fst (BP v) s) (\<lambda> v. (snd (BP v)))"
  by (simp add: InputCSP_NCSP pred_prod_beta)

lift_definition coutput :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" 
  is OutputCSP by (simp add: closure)

lift_definition csync :: "(unit, 'e) channel \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" 
  is "\<lambda> c P. PrefixCSP (c\<cdot>())\<^sub>u P" by (simp add: closure)

lift_definition cprefix :: "'e \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" 
  is "\<lambda> c P. PrefixCSP (\<guillemotleft>c\<guillemotright>)\<^sub>e P" by (simp add: closure)

lift_definition guardedchoice_action :: "'e set \<Rightarrow> ('e \<Rightarrow> ('e, 's) action) \<Rightarrow> ('e, 's) action" is GuardedChoiceCSP
  by (simp add: closure)
                                                                             
lift_definition cguard :: "(bool, 's) expr \<Rightarrow> ('e, 's) action \<Rightarrow> ('e, 's) action" is GuardCSP
  by (metis NCSP_Guard SEXP_def)               

adhoc_overloading 
  Spec \<rightleftharpoons> cspec and
  Skip \<rightleftharpoons> cskip and
  Stop \<rightleftharpoons> cstop and
  uassigns \<rightleftharpoons> cassigns and
  useq \<rightleftharpoons> cseq and
  ucond \<rightleftharpoons> ccond and
  ualtern_list \<rightleftharpoons> caltern_list and
  ExtChoice \<rightleftharpoons> cextchoice and
  ExtChoiceIdx \<rightleftharpoons> cExtChoiceIdx and
  Rename \<rightleftharpoons> crename and
  Hide \<rightleftharpoons> chide and
  ParallelAct \<rightleftharpoons> cactpar and
  Parallel \<rightleftharpoons> cparallel and
  InputPrefix \<rightleftharpoons> cinput and
  OutputPrefix \<rightleftharpoons> coutput and
  SyncPrefix \<rightleftharpoons> csync and
  Guard \<rightleftharpoons> cguard

syntax "_cassume" :: "logic \<Rightarrow> logic" ("{_}\<^sub>C")
translations "_cassume p" == "CONST cassume (p)\<^sub>e"

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

definition cChaos :: "('a, 'b) action" where "cChaos \<equiv> top_class.top"

adhoc_overloading Chaos \<rightleftharpoons> cChaos

subsection \<open> Normalisation Laws \<close>

(*Lemma 1: Sequential Prefix Normalisation*)
lemma "(e \<rightarrow> P) ;; Q = e \<rightarrow> (P ;; Q)"
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

lemma refine_coinduct:
  fixes X :: "'a pred"
  assumes mono: "mono F"
    and ind: "F (X \<sqinter> \<mu> F) \<sqsubseteq> X"
  shows "\<mu> F \<sqsubseteq> X"
  by (meson coinduct ind local.mono pred_ref_iff_le)

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

lemma cseq_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cseq P\<^sub>1 Q\<^sub>1 \<le> cseq P\<^sub>2 Q\<^sub>2"
  by (transfer, meson seqr_mono)

lemma cextchoice_mono [mono_rule]: "\<lbrakk> P\<^sub>1 \<le> P\<^sub>2; Q\<^sub>1 \<le> Q\<^sub>2 \<rbrakk> \<Longrightarrow> cextchoice P\<^sub>1 Q\<^sub>1 \<le> cextchoice P\<^sub>2 Q\<^sub>2"
  by (meson extchoice_mono ref_by_action_def)

lemma PrefixCSP_mono: "\<lbrakk> \<And> x. P(x) \<sqsubseteq> Q(x) \<rbrakk> \<Longrightarrow> PrefixCSP a P \<sqsubseteq> PrefixCSP a Q"
  by (metis PrefixCSP_dist pred_refine_iff ref_by_bool_def ref_lattice.le_iff_inf)

lemma EXTCHOICE_mono:
  "\<lbrakk> \<And> i. P(i) is NCSP; \<And> i. Q(i) is NCSP; \<And> x. P(x) \<sqsubseteq> Q(x) \<rbrakk> \<Longrightarrow> EXTCHOICE I P \<sqsubseteq> EXTCHOICE I Q"
  apply (cases "I = {}")
  apply (simp add: ExtChoice_empty)
  apply (rdes_refine)
  apply blast+
  done

lemma GuardCSP_mono: 
  assumes "P is NCSP" "Q is NCSP" "P \<sqsubseteq> Q"
  shows "b &\<^sub>C P \<sqsubseteq> b &\<^sub>C Q"
  by (rdes_refine cls: assms)

lemma InputCSP_mono: "\<lbrakk> \<And> i. P(i) is NCSP; \<And> i. Q(i) is NCSP; \<And> x. P(x) \<sqsubseteq> Q(x) \<rbrakk> \<Longrightarrow> InputCSP c A P \<sqsubseteq> InputCSP c A Q"
  apply (simp add: InputCSP_def)
  apply (rule EXTCHOICE_mono)
    apply (simp_all add: closure)
  apply (rule GuardCSP_mono)
    apply (simp_all add: closure)
  apply (rule PrefixCSP_mono)
  apply (meson ref_by_fun_def)
  done

lemma cInput_mono [mono_rule]: "\<lbrakk> \<And> x::'a. (P x :: ('e, 's) action) \<le> Q x \<rbrakk> \<Longrightarrow> c\<^bold>?x \<rightarrow> P x \<le> c\<^bold>?x \<rightarrow> Q x"
  by (transfer, simp, meson InputCSP_mono)

end