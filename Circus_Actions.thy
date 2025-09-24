theory Circus_Actions
  imports "UTP-Stateful-Failure.utp_sf_rdes"
begin 

typedef ('e, 's) action = "{P::('s, 'e) sfrd hrel. P is NCSP}"
  by blast

setup_lifting type_definition_action

lift_definition Miracle :: "('e, 's) action" is "utp_rdes_healths.Miracle" by (simp add: closure)

lift_definition Chaos :: "('e, 's) action" is "utp_rdes_healths.Chaos" by (simp add: closure)

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

end