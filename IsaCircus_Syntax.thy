section \<open> Abstract Syntax for IsaCircus \<close>

theory IsaCircus_Syntax
  imports "Abstract_Prog_Syntax.Abstract_Prog_Syntax" "Circus_Toolkit.Circus_Toolkit"
begin

subsection \<open> Introduction \<close>

text \<open> This theory introduces an abstract syntax tree for Circus that is suitable for 
  shallow embeddings developed using Isabelle/UTP and related tools. The approach is
  to create polymorphic constants for each Circus constructor, which can later
  be instantiated with concrete types. \<close>

subsection \<open> Disable unwanted syntax \<close>

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

subsection \<open> Abstract Constants \<close>

type_synonym ('a, 'e) channel = "'a \<Longrightarrow>\<^sub>\<triangle> 'e"

consts
  Skip         :: "'action" ("Skip")
  Stop         :: "'action" ("Stop")
  Chaos        :: "'action" ("Chaos")
  Guard        :: "(bool, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  Assume       :: "(bool, 's) expr \<Rightarrow> 'action"
  InputPrefix  :: "('a, 'e) channel \<Rightarrow> ('a \<Rightarrow> (('s \<Rightarrow> bool) \<times> 'action)) \<Rightarrow> 'action"
  OutputPrefix :: "('a, 'e) channel \<Rightarrow> ('a, 's) expr \<Rightarrow> 'action \<Rightarrow> 'action"
  SyncPrefix   :: "(unit, 'e) channel \<Rightarrow> 'action \<Rightarrow> 'action"
  ExtChoice    :: "'action \<Rightarrow> 'action \<Rightarrow> 'action" 
  IntChoiceIdx :: "'i set \<Rightarrow> ('i \<Rightarrow> 'action) \<Rightarrow> 'action"
  ExtChoiceIdx :: "'i set \<Rightarrow> ('i \<Rightarrow> 'action) \<Rightarrow> 'action"
  Rename       :: "('e \<leftrightarrow> 'f) \<Rightarrow> 'action \<Rightarrow> 'action"
  Hide         :: "'action \<Rightarrow> 'e set \<Rightarrow> 'action"
  Parallel     :: "'e set \<Rightarrow> 'action \<Rightarrow> 'action \<Rightarrow> 'action"
  Interrupt    :: "'action \<Rightarrow> 'action \<Rightarrow> 'action" 

text \<open> Higher-order replication over a finite set \<close>

definition Replicate :: "('action \<Rightarrow> 'action \<Rightarrow> 'action) \<Rightarrow> 'action \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'action) \<Rightarrow> 'action" where
"Replicate Op U I P = Finite_Set.fold Op U (P ` I)"

subsection \<open> Syntax Translations \<close>

syntax 
  "_Guard"          :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<^bold>& _" [60, 61] 60)
  "_InputPrefix"    :: "chan \<Rightarrow> pttrn \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>?_ \<rightarrow> _" [95, 0, 96] 96)
  "_OutputPrefix"   :: "chan \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_\<^bold>!_ \<rightarrow> _" [95, 0, 96] 96)
  "_SyncPrefix"     :: "chan \<Rightarrow> logic \<Rightarrow> logic" ("_ \<rightarrow> _" [95, 96] 96)
  "_Parallel"       :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_\<rbrakk> _" [60, 0,  61] 60)
  "_Interleave"     :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<interleave>" 59)
  "_Hide"           :: "logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<Zhide> _" [60, 61] 60)
  "_Rename"         :: "logic \<Rightarrow> rnenum \<Rightarrow> logic" ("_ [_]" [60, 0] 61)
  "_Interrupt"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<triangle>" 55)
  "_ExtChoice"      :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infixl "\<box>" 55)
  "_InterleaveIter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<interleave> _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_SequentialIter" :: "id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (";; _ \<in> _ \<bullet> _" [0, 0, 10] 10)
  "_ParallelIter"   :: "logic \<Rightarrow> id \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lbrakk> _ \<rbrakk> _ \<in> _ \<bullet> _" [0, 0, 10] 10)

translations 
  "_Guard b P"            == "CONST Guard (b)\<^sub>e P"
  "_InputPrefix c x P"    == "CONST InputPrefix c (\<lambda> x. ((CONST True)\<^sub>e, P))"
  "_OutputPrefix c e P"   == "CONST OutputPrefix c (e)\<^sub>e P"
  "_SyncPrefix c P"       == "CONST SyncPrefix c P"
  "_Interleave P Q"       == "CONST Parallel {} P Q"
  "_Parallel P A Q"       == "CONST Parallel A P Q"
  "_Hide P A"             == "CONST Hide P A"
  "_Rename P f"           == "CONST Rename P f"
  "_ExtChoice P Q"        == "CONST ExtChoice P Q"
  "_Interrupt P Q"        == "CONST Interrupt P Q"
  "_InterleaveIter x I P" == "CONST Replicate (CONST Parallel {}) Skip I (\<lambda> x. P)"
  "_SequentialIter x I P" == "CONST Replicate (CONST useq) Skip I (\<lambda> x. P)"
  "_ParallelIter A x I P"   == "CONST Replicate (CONST Parallel A) Skip I (\<lambda> x. P)"

end