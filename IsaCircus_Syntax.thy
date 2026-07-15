theory IsaCircus_Syntax
  imports "Abstract_Prog_Syntax.Abstract_Prog_Syntax" "Circus_Toolkit.Circus_Toolkit"
begin

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

type_synonym ('a, 'e) channel = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"

consts
  cSkip      :: "'action" ("Skip")
  cStop      :: "'action" ("Stop")
  cChaos     :: "'action" ("Chaos")
  cGuard     :: "(bool, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  cAssume    :: "(bool, 's) expr \<Rightarrow> 'action"
  cInput     :: "('a, 'e) channel \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> 'action)) \<Rightarrow> 'action"
  cOutput    :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  cSync      :: "(unit, 'e) channel \<Rightarrow> 'action \<Rightarrow> 'action"
  cIChoice   :: "'i set \<Rightarrow> ('i \<Rightarrow> 'action) \<Rightarrow> 'action"
  cEChoice   :: "'i set \<Rightarrow> ('i \<Rightarrow> 'action) \<Rightarrow> 'action"
  cRenaming  :: "('e \<leftrightarrow> 'f) \<Rightarrow> 'action \<Rightarrow> 'action"
  cHide      :: "'action \<Rightarrow> 'e set \<Rightarrow> 'action"
  cParallel  :: "'action \<Rightarrow> 'e set \<Rightarrow> 'action \<Rightarrow> 'action"
  cInterrupt :: "'action \<Rightarrow> 'action \<Rightarrow> 'action" (infixl "\<triangle>" 55) 

syntax 
  "_cGuard"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [60, 61] 60)
  "_cInput"      :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?_ \<rightarrow> _" [95, 0, 96] 96)
  "_cOutput"     :: "chan \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>!_ \<rightarrow> _" [95, 0, 96] 96)
  "_cSync"       :: "chan \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [95, 96] 96)
  "_cParallel"   :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_\<rbrakk> _" [60, 0,  61] 60)
  "_cInterleave" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<interleave>" 59)
  "_cHide"       :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<Zhide> _" [60, 61] 60)
  "_cRenaming"   :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 61)

translations 
  "_cGuard b P"      == "CONST cGuard b P"
  "_cInput c x P"    == "CONST cInput c (\<lambda> x. ((CONST True)\<^sub>e, P))"
  "_cOutput c e P"   == "CONST cOutput c (e)\<^sub>e P"
  "_cSync c P"       == "CONST cSync c P"
  "_cInterleave P Q" == "CONST cParallel P {} Q"
  "_cParallel P A Q" == "CONST cParallel P A Q"
  "_cHide P A"       == "CONST cHide P A"
  "_cRenaming P f"   == "CONST cRenaming P f"

end