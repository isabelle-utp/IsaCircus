section \<open> Circus Parallel Composition \<close>

theory Circus_Parallel
  imports "UTP-Stateful-Failure.utp_sf_rdes"
begin

subsection \<open> Trace Merge \<close>

fun tr_par ::
  "'\<theta> set \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" where
"tr_par cs [] [] = {[]}" |
"tr_par cs (e # t) [] = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs t []))" |
"tr_par cs [] (e # t) = (if e \<in> cs then {[]} else {[e]} \<^sup>\<frown> (tr_par cs [] t))" |
"tr_par cs (e\<^sub>1 # t\<^sub>1) (e\<^sub>2 # t\<^sub>2) =
  (if e\<^sub>1 = e\<^sub>2
    then
      if e\<^sub>1 \<in> cs 
        then {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 t\<^sub>2)
        else
          ({[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))) \<union>
          ({[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))
    else
      if e\<^sub>1 \<in> cs then
        if e\<^sub>2 \<in> cs then {[]}
        else
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2)
      else
        if e\<^sub>2 \<in> cs then
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2))
        else
          {[e\<^sub>1]} \<^sup>\<frown> (tr_par cs t\<^sub>1 (e\<^sub>2 # t\<^sub>2)) \<union>
          {[e\<^sub>2]} \<^sup>\<frown> (tr_par cs (e\<^sub>1 # t\<^sub>1) t\<^sub>2))"

abbreviation tr_inter :: "'\<theta> list \<Rightarrow> '\<theta> list \<Rightarrow> '\<theta> list set" (infixr "|||\<^sub>t" 100) where
"x |||\<^sub>t y \<equiv> tr_par {} x y"

subsection \<open> Trace Merge Lemmas \<close>

lemma tr_par_empty:
"tr_par cs t1 [] = {takeWhile (\<lambda>x. x \<notin> cs) t1}"
"tr_par cs [] t2 = {takeWhile (\<lambda>x. x \<notin> cs) t2}"
\<comment> \<open> Subgoal 1 \<close>
apply (induct t1; simp)
\<comment> \<open> Subgoal 2 \<close>
apply (induct t2; simp)
done

lemma tr_par_sym:
"tr_par cs t1 t2 = tr_par cs t2 t1"
apply (induct t1 arbitrary: t2)
\<comment> \<open> Subgoal 1 \<close>
apply (simp add: tr_par_empty)
\<comment> \<open> Subgoal 2 \<close>
apply (induct_tac t2)
\<comment> \<open> Subgoal 2.1 \<close>
apply (clarsimp)
\<comment> \<open> Subgoal 2.2 \<close>
apply (clarsimp)
apply (blast)
done

lemma tr_inter_sym: "x |||\<^sub>t y = y |||\<^sub>t x"
  by (simp add: tr_par_sym)

no_notation
  Set.member  (\<open>'(:')\<close>) and
  Set.member  (\<open>(\<open>notation=\<open>infix :\<close>\<close>_/ : _)\<close> [51, 51] 50)

unbundle UTP_Syntax


subsection \<open> Merge predicates \<close>


definition CSPInnerMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) sfrd) merge" ("N\<^sub>C") where
  [pred]:
  "CSPInnerMerge ns1 cs ns2 = (
    $ref\<^sup>> \<subseteq> (($0:ref\<^sup>< \<union> $1:ref\<^sup><) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> (($0:ref\<^sup>< \<inter> $1:ref\<^sup><) - \<guillemotleft>cs\<guillemotright>) \<and>
    $<:tr\<^sup>< \<le> $tr\<^sup>> \<and>
    ($tr\<^sup>> - $<:tr\<^sup><) \<in> tr_par \<guillemotleft>cs\<guillemotright> ($0:tr\<^sup>< - $<:tr\<^sup><)($1:tr\<^sup>< - $<:tr\<^sup><) \<and>
    ($0:tr\<^sup>< - $<:tr\<^sup><) \<restriction> \<guillemotleft>cs\<guillemotright> = ($1:tr\<^sup>< - $<:tr\<^sup><) \<restriction> \<guillemotleft>cs\<guillemotright> \<and>
    $st\<^sup>> = ($<:st\<^sup>< \<oplus>\<^sub>L $0:st\<^sup>< on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L $1:st\<^sup>< on \<guillemotleft>ns2\<guillemotright>)\<^sub>e"

abbreviation CSPInnerInterleave :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) sfrd) merge" ("N\<^sub>I") where
"N\<^sub>I ns1 ns2 \<equiv> N\<^sub>C ns1 {} ns2"

(*
definition CSPInnerInterleave :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) sfrd) merge" ("N\<^sub>I") where
  [pred]:
  "N\<^sub>I ns1 ns2 = (
    $ref\<^sup>> \<subseteq> ($0:ref \<inter> $1:ref) \<and>
    $<:tr \<le>\<^sub>u $tr\<acute> \<and>
    ($tr\<acute> - $<:tr) \<in> ($0:tr - $<:tr) \<star>\<^bsub>{}\<^esub> ($1:tr - $<:tr) \<and>
    st\<^sup>> = ($<:st \<oplus> $0:st on &ns1) \<oplus> $1:st on &ns2)"
*)  

text \<open> An intermediate merge hides the state, whilst a final merge hides the refusals. \<close>
  
definition CSPInterMerge where
[pred]: "CSPInterMerge P cs Q = (P \<parallel>\<^bsub>(\<exists> st\<^sup>> \<Zspot> N\<^sub>C 0\<^sub>L cs 0\<^sub>L)\<^esub> Q)"
  
definition CSPFinalMerge where
[pred]: "CSPFinalMerge P ns1 cs ns2 Q = (P \<parallel>\<^bsub>(\<exists> ref\<^sup>> \<Zspot> N\<^sub>C ns1 cs ns2)\<^esub> Q)"
  
syntax
  "_cinter_merge" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_\<rbrakk>\<^sup>I _" [85,0,86] 86)
  "_cfinal_merge" :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_|_|_\<rbrakk>\<^sup>F _" [85,0,0,0,86] 86)
  "_wrC" :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ wr[_]\<^sub>C _" [85,0,86] 86)

translations
  "_cinter_merge P cs Q" == "CONST CSPInterMerge P cs Q"
  "_cfinal_merge P ns1 cs ns2 Q" == "CONST CSPFinalMerge P ns1 cs ns2 Q"
  "_wrC P cs Q" == "P wr\<^sub>R(N\<^sub>C 0\<^sub>L cs 0\<^sub>L) Q"

lemma CSPInnerMerge_R2m [closure]: "N\<^sub>C ns1 cs ns2 is R2m"
  by pred_auto

lemma CSPInnerMerge_RDM [closure]: "N\<^sub>C ns1 cs ns2 is RDM"
  by (rule RDM_intro, simp add: closure, simp_all add: CSPInnerMerge_def unrest unrest_ssubst_expr usubst_eval usubst)


lemma ex_ref'_R2m_closed [closure]: 
  assumes "P is R2m"
  shows "(\<exists> ref\<^sup>> \<Zspot> P) is R2m"
proof -
  have "R2m(\<exists> ref\<^sup>> \<Zspot> R2m P) = (\<exists> ref\<^sup>> \<Zspot> R2m P)"
    by (pred_auto)
  thus ?thesis
    by (metis Healthy_def' assms) 
qed

lemma CSPInnerMerge_unrests [unrest]: 
  "$<:ok\<^sup>< \<sharp> N\<^sub>C ns1 cs ns2"
  "$<:wait\<^sup>< \<sharp> N\<^sub>C ns1 cs ns2"
  by (pred_auto)+
    
lemma CSPInterMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>cs\<rbrakk>\<^sup>I Q is RR"
  by (simp add: CSPInterMerge_def parallel_RR_closed assms closure unrest)

lemma CSPInterMerge_unrest_ref [unrest]:
  assumes "P is CRR" "Q is CRR"
  shows "$ref\<^sup>< \<sharp> P \<lbrakk>cs\<rbrakk>\<^sup>I Q"
proof -
  have "$ref\<^sup>< \<sharp> CRR(P) \<lbrakk>cs\<rbrakk>\<^sup>I CRR(Q)"
    by (pred_simp, blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma CSPInterMerge_unrest_st' [unrest]:
  "$st\<^sup>> \<sharp> P \<lbrakk>cs\<rbrakk>\<^sup>I Q"
  by (pred_auto)

lemma CSPInterMerge_CRR_closed [closure]: 
  assumes "P is CRR" "Q is CRR"
  shows "P \<lbrakk>cs\<rbrakk>\<^sup>I Q is CRR"
  by (simp add: CRR_implies_RR CRR_intro CSPInterMerge_RR_closed CSPInterMerge_unrest_ref assms)

lemma CSPFinalMerge_RR_closed [closure]: 
  assumes "P is RR" "Q is RR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q is RR"
  by (simp add: CSPFinalMerge_def parallel_RR_closed assms closure unrest)

lemma CSPFinalMerge_unrest_ref [unrest]:
  assumes "P is CRR" "Q is CRR"
  shows "$ref\<^sup>< \<sharp> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q"
proof -
  have "$ref\<^sup>< \<sharp> CRR(P) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F CRR(Q)"
    by (pred_simp, blast)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma CSPFinalMerge_CRR_closed [closure]: 
  assumes "P is CRR" "Q is CRR"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q is CRR"
  by (simp add: CRR_implies_RR CRR_intro CSPFinalMerge_RR_closed CSPFinalMerge_unrest_ref assms)

lemma CSPFinalMerge_unrest_ref' [unrest]:
  assumes "P is CRR" "Q is CRR"
  shows "$ref\<^sup>> \<sharp> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q"
proof -
  have "$ref\<^sup>> \<sharp> CRR(P) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F CRR(Q)"
    by (pred_simp)
  thus ?thesis
    by (simp add: Healthy_if assms)
qed

lemma CSPFinalMerge_CRF_closed [closure]: 
  assumes "P is CRF" "Q is CRF"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q is CRF"
  by (rule CRF_intro, simp_all add: assms unrest closure)
  
lemma CSPInnerMerge_empty_Interleave:
  "N\<^sub>C ns1 {} ns2 = N\<^sub>I ns1 ns2"
  apply (pred_auto)
  oops

definition CSPMerge :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> '\<psi> set \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) sfrd) merge" ("M\<^sub>C") where
[pred]: "M\<^sub>C ns1 cs ns2 = M\<^sub>R(N\<^sub>C ns1 cs ns2) ;; Skip"

definition CSPInterleave :: "('\<alpha> \<Longrightarrow> '\<sigma>) \<Rightarrow> ('\<beta> \<Longrightarrow> '\<sigma>) \<Rightarrow> (('\<sigma>,'\<psi>) sfrd) merge" ("M\<^sub>I") where
[pred]: "M\<^sub>I ns1 ns2 = M\<^sub>R(N\<^sub>I ns1 ns2) ;; Skip"

lemma swap_CSPInnerMerge:
  "ns1 \<bowtie> ns2 \<Longrightarrow> swap\<^sub>m ;; (N\<^sub>C ns1 cs ns2) = (N\<^sub>C ns2 cs ns1)"
  apply (pred_auto)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
  using tr_par_sym apply blast
  apply (simp add: lens_indep_comm)
done
    
lemma SymMerge_CSPInnerMerge_NS [closure]: "N\<^sub>C 0\<^sub>L cs 0\<^sub>L is SymMerge"
  by (simp add: Healthy_def swap_CSPInnerMerge)
                             
    
lemma SymMerge_CSPInnerInterleave [closure]:
  "AssocMerge (N\<^sub>I 0\<^sub>L 0\<^sub>L)"
  apply (pred_auto)
  apply (rename_tac tr tr\<^sub>2' ref\<^sub>0 tr\<^sub>0' ref\<^sub>0' tr\<^sub>1' ref\<^sub>1' tr' ref\<^sub>2' tr\<^sub>i' ref\<^sub>3')
oops
    
lemma CSPInterMerge_right_false [rpred]: "P \<lbrakk>cs\<rbrakk>\<^sup>I false = false"
  by (simp add: CSPInterMerge_def)

lemma CSPInterMerge_left_false [rpred]: "false \<lbrakk>cs\<rbrakk>\<^sup>I P = false"
  by (pred_auto)

lemma CSPFinalMerge_right_false [rpred]: "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F false = false"
  by (simp add: CSPFinalMerge_def)

lemma CSPFinalMerge_left_false [rpred]: "false \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F P = false"
  by (simp add: CSPFinalMerge_def)

term par_by_merge

lemma CSPInnerMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = Q \<parallel>\<^bsub>N\<^sub>C ns2 cs ns1\<^esub> P"
proof -
  have "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = P \<parallel>\<^bsub>swap\<^sub>m ;; N\<^sub>C ns2 cs ns1\<^esub> Q"
    by (simp add: assms lens_indep_sym swap_CSPInnerMerge)
  also have "... = Q \<parallel>\<^bsub>N\<^sub>C ns2 cs ns1\<^esub> P"
    by (metis (no_types, lifting) par_by_merge_def par_by_merge_seq_add par_sep_swap)
  finally show ?thesis .
qed

lemma CSPInterMerge_commute:
  "P \<lbrakk>cs\<rbrakk>\<^sup>I Q = Q \<lbrakk>cs\<rbrakk>\<^sup>I P"
proof -
  have "P \<lbrakk>cs\<rbrakk>\<^sup>I Q = P \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> N\<^sub>C 0\<^sub>L cs 0\<^sub>L\<^esub> Q"
    by (simp add: CSPInterMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> st\<^sup>> \<Zspot> (swap\<^sub>m ;; N\<^sub>C 0\<^sub>L cs 0\<^sub>L)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> st\<^sup>> \<Zspot> N\<^sub>C 0\<^sub>L cs 0\<^sub>L)\<^esub> Q"
    by (pred_simp)
  also have "... = Q \<parallel>\<^bsub>(\<exists> st\<^sup>> \<Zspot> N\<^sub>C 0\<^sub>L cs 0\<^sub>L)\<^esub> P"
    by (simp add: par_by_merge_def par_sep_swap rel_RA1)
  also have "... = Q \<lbrakk>cs\<rbrakk>\<^sup>I P"
    by (simp add: CSPInterMerge_def)
  finally show ?thesis .
qed

lemma CSPFinalMerge_commute:
  assumes "ns1 \<bowtie> ns2"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = P \<parallel>\<^bsub>\<exists> ref\<^sup>> \<Zspot> N\<^sub>C ns1 cs ns2\<^esub> Q"
    by (simp add: CSPFinalMerge_def)
  also have "... = P \<parallel>\<^bsub>\<exists> ref\<^sup>> \<Zspot> (swap\<^sub>m ;; N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = P \<parallel>\<^bsub>swap\<^sub>m ;; (\<exists> ref\<^sup>> \<Zspot> N\<^sub>C ns2 cs ns1)\<^esub> Q"
    by pred_simp
  also have "... = Q \<parallel>\<^bsub>(\<exists> ref\<^sup>> \<Zspot> N\<^sub>C ns2 cs ns1)\<^esub> P"
    by (simp add: par_by_merge_def par_sep_swap rel_RA1)
  also have "... = Q \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: CSPFinalMerge_def)
  finally show ?thesis .
qed
  
text \<open> Important theorem that shows the form of a parallel process \<close>

lemma CSPInnerMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" 
  shows
  "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q = 
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1).
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,[],\<guillemotleft>tt\<^sub>0\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,[],\<guillemotleft>tt\<^sub>1\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($ref\<^sup>> \<subseteq> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have P:"(\<exists> (ok\<^sup>>,wait\<^sup>>) \<Zspot> R2(P)) = P" (is "?P' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms unrest closure)
  have Q:"(\<exists> (ok\<^sup>>,wait\<^sup>>) \<Zspot> R2(Q)) = Q" (is "?Q' = _")
    by (simp add: ex_unrest ex_plus Healthy_if assms unrest closure)
  from assms(1,2)
  have "?P' \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> ?Q' = 
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             ?P'\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> ?Q'\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($ref\<^sup>> \<subseteq> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
    apply (simp add: par_by_merge_alt_def, pred_auto, blast)
    apply (rename_tac ok wait tr st ref tr' ref' ref\<^sub>0 ref\<^sub>1 st\<^sub>0 st\<^sub>1 tr\<^sub>0 ok\<^sub>0 tr\<^sub>1 wait\<^sub>0 ok\<^sub>1 wait\<^sub>1)
    apply (rule_tac x="ok" in exI)
    apply (rule_tac x="wait" in exI)
    apply (rule_tac x="tr" in exI)      
    apply (rule_tac x="st" in exI)
    apply (rule_tac x="ref" in exI)
    apply (rule_tac x="tr @ tr\<^sub>0" in exI)      
    apply (rule_tac x="st\<^sub>0" in exI)
    apply (rule_tac x="ref\<^sub>0" in exI)      
    apply (auto)
    apply (metis Prefix_Order.prefixI append_minus)
  done      
  thus ?thesis
    by (simp add: P Q)
qed

(*** THESE THEOREMS SHOULD BE IN UTP_REL_LAWS ***)

lemma seqr_exists_left:
  "((\<exists> x\<^sup>< \<Zspot> P) ;; Q) = (\<exists> x\<^sup>< \<Zspot> (P ;; Q))"
  by (pred_auto)

lemma seqr_exists_right:
  "(P ;; (\<exists> x\<^sup>> \<Zspot> Q)) = (\<exists> x\<^sup>> \<Zspot> (P ;; Q))"
  by (pred_auto)

lemma CSPInterMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "P is RR" "Q is RR" 
  shows
  "P \<lbrakk>cs\<rbrakk>\<^sup>I Q = 
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($ref\<^sup>> \<subseteq> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<exists> st\<^sup>> \<Zspot> P \<parallel>\<^bsub>N\<^sub>C 0\<^sub>L cs 0\<^sub>L\<^esub> Q)"
    by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> st\<^sup>> \<Zspot>
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1).
             P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($ref\<^sup>> \<subseteq> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>0\<^sub>L\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>0\<^sub>L\<guillemotright>)\<^sub>e))"
    by (simp add: CSPInnerMerge_form assms)
  also have "... = ?rhs"
    by (pred_simp, blast)
  finally show ?thesis .
qed
  
lemma CSPFinalMerge_form:
  fixes P Q :: "('\<sigma>,'\<phi>) action"
  assumes "vwb_lens ns1" "vwb_lens ns2" "P is RR" "Q is RR" "$ref\<^sup>> \<sharp> P" "$ref\<^sup>> \<sharp> Q"
  shows
  "(P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q) = 
        (\<Sqinter> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             P\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")  
proof -
  have "?lhs = (\<exists> ref\<^sup>> \<Zspot> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
    by (simp add: CSPFinalMerge_def par_by_merge_def seqr_exists_right)
  also have "... = 
      (\<exists> ref\<^sup>> \<Zspot>
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             (\<exists> ref\<^sup>> \<Zspot> P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>,\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (\<exists> ref\<^sup>> \<Zspot> Q)\<lbrakk>\<guillemotleft>ref\<^sub>1\<guillemotright>,\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/ref\<^sup>>,st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($ref\<^sup>> \<subseteq> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright>) - \<guillemotleft>cs\<guillemotright>)
           \<and> $tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e))"
    by (simp add: CSPInnerMerge_form ex_unrest assms)
  also have "... = 
        (\<Sqinter> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             (\<exists> ref\<^sup>> \<Zspot> P)\<lbrakk>\<guillemotleft>st\<^sub>0\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>0\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk> \<and> (\<exists> ref\<^sup>> \<Zspot> Q)\<lbrakk>\<guillemotleft>st\<^sub>1\<guillemotright>,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>/st\<^sup>>,tr\<^sup><,tr\<^sup>>\<rbrakk>
           \<and> ($tr\<^sup>< \<le> $tr\<^sup>>
           \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright>
           \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>
           \<and> $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
    by (pred_simp, blast)
  also have "... = ?rhs"
    by (simp add: ex_unrest assms)
  finally show ?thesis .
qed

lemma CSPInterleave_merge: "M\<^sub>I ns1 ns2 = M\<^sub>C ns1 {} ns2"
  by (pred_auto)

lemma csp_wrR_def:
  "P wr[cs]\<^sub>C Q = (\<not>\<^sub>r ((\<not>\<^sub>r Q) ;; U0 \<and> P ;; U1 \<and> ($<:st\<^sup>> = $st\<^sup>< \<and> $<:tr\<^sup>> = $tr\<^sup><)\<^sub>e) ;; N\<^sub>C 0\<^sub>L cs 0\<^sub>L ;; R1 true)"
  by (pred_auto, metis+)

lemma csp_wrR_ns_irr:
  "(P wr\<^sub>R(N\<^sub>C ns1 cs ns2) Q) = (P wr[cs]\<^sub>C Q)"
  by (pred_auto)

lemma csp_wrR_CRC_closed [closure]:
  assumes "P is CRR" "Q is CRR"
  shows "P wr[cs]\<^sub>C Q is CRC"
proof -
  have "$ref\<^sup>< \<sharp> P wr[cs]\<^sub>C Q"
    by (simp add: csp_wrR_def rpred closure assms unrest unrest_ssubst_expr usubst_eval usubst)
  thus ?thesis
    by (rule CRC_intro, simp_all add: closure assms)
qed

lemma ref'_unrest_final_merge [unrest]: 
  "$ref\<^sup>> \<sharp> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q"
  by (pred_auto)

lemma inter_merge_CDC_closed [closure]:
  "P \<lbrakk>cs\<rbrakk>\<^sup>I Q is CDC"
  using le_less_trans by (pred_simp, blast)

lemma CSPInterMerge_alt_def:
  "P \<lbrakk>cs\<rbrakk>\<^sup>I Q = (\<exists> st\<^sup>> \<Zspot> P \<parallel>\<^bsub>N\<^sub>C 0\<^sub>L cs 0\<^sub>L\<^esub> Q)"
  by (simp add: par_by_merge_def CSPInterMerge_def seqr_exists_right)

lemma CSPFinalMerge_alt_def:
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = (\<exists> ref\<^sup>> \<Zspot> P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q)"
  by (simp add: par_by_merge_def CSPFinalMerge_def seqr_exists_right)

lemma merge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> P = 
     (\<Sqinter> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1). 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> [], tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> P \<and>
        ($ref\<^sup>> \<subseteq> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> 
        $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L (\<guillemotleft>\<sigma>\<^sub>0\<guillemotright> ($st\<^sup><)) on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1).
            [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> [], tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
            [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> [], tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR P \<and>
            ($ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr\<^sup>< \<le> $tr\<^sup>> \<and>
             tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and>
             \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> $st\<^sup>> = $st\<^sup>< \<triangleleft>\<^bsub>\<guillemotleft>ns1\<guillemotright>\<^esub> \<guillemotleft>st\<^sub>0\<guillemotright> \<triangleleft>\<^bsub>\<guillemotleft>ns2\<guillemotright>\<^esub> \<guillemotleft>st\<^sub>1\<guillemotright>)\<^sub>e)"
    by (simp add: CSPInnerMerge_form assms closure Healthy_if)
  also have "... =      (\<Sqinter> (ref\<^sub>1, st\<^sub>1, tt\<^sub>1). 
        [s\<^sub>0]\<^sub>S\<^sub>< \<and>
        [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> [], tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR P \<and>
        ($ref\<^sup>> \<subseteq> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> 
        $st\<^sup>> = ($st\<^sup>< \<oplus>\<^sub>L (\<guillemotleft>\<sigma>\<^sub>0\<guillemotright> ($st\<^sup><)) on \<guillemotleft>ns1\<guillemotright>) \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
    by (pred_simp, blast)
  finally show ?thesis by (simp add: closure assms Healthy_if)
qed

lemma merge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = 
     (\<Sqinter> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0). 
        [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> [], tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
        [s\<^sub>1]\<^sub>S\<^sub>< \<and>
        ($ref\<^sup>> \<subseteq> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
        tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<lceil>t\<^sub>1\<rceil>\<^sub>S\<^sub>< \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<lceil>t\<^sub>1\<rceil>\<^sub>S\<^sub>< \<restriction> \<guillemotleft>cs\<guillemotright> \<and> 
        st\<^sup>> = st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright> \<oplus>\<^sub>L (\<guillemotleft>\<sigma>\<^sub>1\<guillemotright> ($st\<^sup><)) on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<parallel>\<^bsub>N\<^sub>C ns2 cs ns1\<^esub> P"
    by (simp add: CSPInnerMerge_commute assms)
  also from assms have "... = ?rhs"
    apply (simp add: assms merge_csp_do_left lens_indep_sym)
    apply (pred_auto)
    using assms(3) lens_indep_comm tr_par_sym apply fastforce
    using assms(3) lens_indep.lens_put_comm tr_par_sym apply fastforce
    done
  finally show ?thesis .
qed

lemma merge_csp_enable_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "P \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> \<E>(s\<^sub>0,t\<^sub>0,E\<^sub>0) = 
             (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0). 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and> 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             ((\<forall> e. \<guillemotleft>e\<guillemotright> \<in> \<lceil>E\<^sub>0\<rceil>\<^sub>S\<^sub>< \<longrightarrow> \<guillemotleft>e\<guillemotright> \<notin> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<restriction> \<guillemotleft>cs\<guillemotright> \<and>
             $st\<^sup>> = $st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright> \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>0,t\<^sub>0, E\<^sub>0) \<and>
             ($ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              $tr\<^sup>< \<le> $tr\<^sup>> \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> $st\<^sup>> = $st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright> \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
    by (simp add: CSPInnerMerge_form assms closure unrest unrest_ssubst_expr usubst_eval usubst, pred_simp)
  also have "... = (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             ((\<lceil>s\<^sub>0\<rceil>\<^sub>S\<^sub>< \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> = \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<and> (\<forall> e. \<guillemotleft>e\<guillemotright> \<in> \<lceil>E\<^sub>0\<rceil>\<^sub>S\<^sub>< \<longrightarrow> \<guillemotleft>e\<guillemotright> \<notin> \<guillemotleft>ref\<^sub>1\<guillemotright>)) \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             $tr\<^sup>< \<le> $tr\<^sup>> \<and> tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<guillemotleft>tt\<^sub>0\<guillemotright> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> $st\<^sup>> = $st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright> \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
    by (simp add: csp_enable_def, pred_simp, blast)
  also have "... = ?rhs"
    by (pred_simp, blast)
  finally show ?thesis .
qed

lemma merge_csp_enable_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR"
  shows "\<E>(s\<^sub>0,t\<^sub>0,E\<^sub>0) \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> P = 
             (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0). 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and> 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> P \<and>
             ((\<forall> e. \<guillemotleft>e\<guillemotright> \<in> \<lceil>E\<^sub>0\<rceil>\<^sub>S\<^sub>< \<longrightarrow> \<guillemotleft>e\<guillemotright> \<notin> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<and>
              $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              tt \<in> tr_par \<guillemotleft>cs\<guillemotright> \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<guillemotleft>tt\<^sub>0\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<lceil>t\<^sub>0\<rceil>\<^sub>S\<^sub>< \<restriction> \<guillemotleft>cs\<guillemotright> \<and>
              $st\<^sup>> = $st\<^sup>< \<oplus>\<^sub>L \<guillemotleft>st\<^sub>0\<guillemotright> on \<guillemotleft>ns1\<guillemotright> \<oplus>\<^sub>L \<guillemotleft>st\<^sub>1\<guillemotright> on \<guillemotleft>ns2\<guillemotright>)\<^sub>e)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = P \<parallel>\<^bsub>N\<^sub>C ns2 cs ns1\<^esub> \<E>(s\<^sub>0,t\<^sub>0,E\<^sub>0)"
    by (simp add: CSPInnerMerge_commute assms)
  also from assms have "... = ?rhs"
    apply (simp add: merge_csp_enable_right assms(4) lens_indep_sym)
    apply (pred_simp)
    oops

text \<open> The result of merge two terminated stateful traces is to (1) require both state preconditions
  hold, (2) merge the traces using, and (3) merge the state using a parallel assignment. \<close>

lemma FinalMerge_csp_do_left:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<^sup>> \<sharp> P"
  shows "\<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F P =         
         (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>0 \<star>\<^bsub>cs\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             st\<^sup>> = $st \<oplus> \<lparr>&\<^bold>v \<leadsto> $st\<rparr> \<dagger> \<sigma>\<^sub>0 on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>0,\<sigma>\<^sub>0,t\<^sub>0) \<and>
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> ref\<^sup>> \<Zspot> P) \<and>
             tr\<^sup>< \<le> tr\<^sup>> \<and> &tt \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> 
             st\<^sup>> = $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form ex_unrest Healthy_if unrest closure assms)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, tt\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> RR(\<exists> ref\<^sup>> \<Zspot> P) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>0 \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             st\<^sup>> = $st \<oplus> \<lparr>&\<^bold>v \<leadsto> $st\<rparr> \<dagger> \<sigma>\<^sub>0 on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (rel_blast)
  also have "... = 
        (\<^bold>\<exists> (st\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and>
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>0 \<star>\<^bsub>cs\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             st\<^sup>> = $st \<oplus> \<lparr>&\<^bold>v \<leadsto> $st\<rparr> \<dagger> \<sigma>\<^sub>0 on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: ex_unrest Healthy_if unrest closure assms)
  finally show ?thesis .
qed
      
lemma FinalMerge_csp_do_right:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "P is RR" "$ref\<^sup>> \<sharp> P"
  shows "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) =         
         (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> 
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> P \<and>
             [s\<^sub>1]\<^sub>S\<^sub>< \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>t\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>t\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
             st\<^sup>> = $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<lparr>&\<^bold>v \<leadsto> $st\<rparr> \<dagger> \<sigma>\<^sub>1 on &ns2)"
  (is "?lhs = ?rhs")
proof -
  have "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) = \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns2|cs|ns1\<rbrakk>\<^sup>F P"
    by (simp add: assms CSPFinalMerge_commute)
  also have "... = ?rhs"
    apply (simp add: FinalMerge_csp_do_left assms lens_indep_sym conj_comm)
    apply (rel_auto)
    using assms(3) lens_indep.lens_put_comm tr_par_sym apply fastforce+
  done
  finally show ?thesis .
qed
  
lemma FinalMerge_csp_do:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S')" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<^bold>\<exists> (st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<and>
             [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             tr\<^sup>< \<le> tr\<^sup>> \<and> &tt \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> \<and> 
             st\<^sup>> = $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &ns1 \<oplus> \<guillemotleft>st\<^sub>1\<guillemotright> on &ns2)"
    by (simp add: CSPFinalMerge_form unrest closure assms)
  also have "... = 
        ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> [\<langle>\<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2\<rangle>\<^sub>a]\<^sub>S')"
    by (rel_auto)
  finally show ?thesis .
qed

lemma FinalMerge_csp_do' [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         (\<^bold>\<exists> trace \<bullet> \<Phi>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>, \<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2, \<guillemotleft>trace\<guillemotright>))"
  by (simp add: FinalMerge_csp_do assms, rel_auto)

(*
lemma FinalMerge_csp_do' [rpred]:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2"
  shows "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
         (\<Sqinter> trace | \<guillemotleft>trace\<guillemotright> \<in> \<lceil>t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<bullet>
                    \<Phi>(s\<^sub>1 \<and> s\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>, \<sigma>\<^sub>1 [&ns1|&ns2]\<^sub>s \<sigma>\<^sub>2, \<guillemotleft>trace\<guillemotright>))"
  by (simp add: FinalMerge_csp_do assms, rel_auto)
*)

lemma CSPFinalMerge_UINF_mem_left [rpred]: 
  "(\<Sqinter> i\<in>A \<bullet> P(i)) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = (\<Sqinter> i\<in>A \<bullet> P(i) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q)"
  by (simp add: CSPFinalMerge_def par_by_merge_USUP_mem_left)

lemma CSPFinalMerge_UINF_ind_left [rpred]: 
  "(\<Sqinter> i \<bullet> P(i)) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q = (\<Sqinter> i \<bullet> P(i) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q)"
  by (simp add: CSPFinalMerge_def par_by_merge_USUP_ind_left)

lemma CSPFinalMerge_UINF_mem_right [rpred]: 
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (\<Sqinter> i\<in>A \<bullet> Q(i)) = (\<Sqinter> i\<in>A \<bullet> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q(i))"
  by (simp add: CSPFinalMerge_def par_by_merge_USUP_mem_right)

lemma CSPFinalMerge_UINF_ind_right [rpred]: 
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (\<Sqinter> i \<bullet> Q(i)) = (\<Sqinter> i \<bullet> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q(i))"
  by (simp add: CSPFinalMerge_def par_by_merge_USUP_ind_right)

lemma InterMerge_csp_enable_left:
  assumes "P is RR" "st\<^sup>> \<sharp> P"
  shows "\<E>(s\<^sub>0,t\<^sub>0,E\<^sub>0) \<lbrakk>cs\<rbrakk>\<^sup>I P =         
         (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, t\<^sub>1) \<bullet> 
             [s\<^sub>0]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e \<bullet> \<guillemotleft>e\<guillemotright> \<in> \<lceil>E\<^sub>0\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u \<guillemotleft>ref\<^sub>0\<guillemotright>) \<and>
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t\<^sub>1\<guillemotright>] \<dagger> P \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>0 \<star>\<^bsub>cs\<^esub> \<guillemotleft>t\<^sub>1\<guillemotright> \<and> t\<^sub>0 \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>t\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
  (is "?lhs = ?rhs")
    apply (simp add: CSPInterMerge_form ex_unrest Healthy_if unrest closure assms usubst)
    apply (simp add: csp_enable_def usubst unrest assms closure)
  apply (rel_auto)
  done

lemma InterMerge_csp_enable:
  "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>cs\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
        ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
         (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter> E\<^sub>2 \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((E\<^sub>1 \<union> E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<^sup>>) \<and>
         [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t)" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             tr\<^sup>< \<le> tr\<^sup>> \<and> &tt \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0, tt\<^sub>1) \<bullet> 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             tr\<^sup>< \<le> tr\<^sup>> \<and> &tt \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>)"
    by (rel_auto)
  also have "... = 
        ( [s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and>
          (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 \<inter> E\<^sub>2 \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((E\<^sub>1 \<union> E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<^sup>>) \<and>
          [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t
         )"  
    apply (rel_auto)
    apply (rename_tac tr st tr' ref')
    apply (rule_tac x="- \<lbrakk>E\<^sub>1\<rbrakk>\<^sub>e st" in exI)
    apply (simp)
    apply (rule_tac x="- \<lbrakk>E\<^sub>2\<rbrakk>\<^sub>e st" in exI)
    apply (auto)
  done
  finally show ?thesis .
qed

lemma InterMerge_csp_enable' [rpred]:
  "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>cs\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
          (\<^bold>\<exists> trace \<bullet> \<E>( s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>
                      , \<guillemotleft>trace\<guillemotright>
                      , (E\<^sub>1 \<inter> E\<^sub>2 \<inter> \<guillemotleft>cs\<guillemotright>) \<union> ((E\<^sub>1 \<union> E\<^sub>2) - \<guillemotleft>cs\<guillemotright>)))"
  by (simp add: InterMerge_csp_enable, rel_auto)

lemma InterMerge_csp_enable_csp_do [rpred]:
  "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<lbrakk>cs\<rbrakk>\<^sup>I \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) = 
  (\<^bold>\<exists> trace \<bullet> \<E>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>,\<guillemotleft>trace\<guillemotright>,E\<^sub>1 - \<guillemotleft>cs\<guillemotright>))" 
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<Sqinter> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1, tt\<^sub>0, tt\<^sub>1). 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>1\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>1\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>1\<guillemotright>] \<dagger> \<Phi>(s\<^sub>2,\<sigma>\<^sub>2,t\<^sub>2) \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             tr\<^sup>< \<le> tr\<^sup>> \<and> &tt \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>tt\<^sub>1\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>)"
    by (simp add: CSPInterMerge_form unrest closure)
  also have "... = 
        (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, tt\<^sub>0) \<bullet> 
             [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> \<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) \<and>
             [s\<^sub>2]\<^sub>S\<^sub>< \<and>
             $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
             [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto) 
  also have "... = ([s\<^sub>1 \<and> s\<^sub>2]\<^sub>S\<^sub>< \<and> (\<^bold>\<forall> e\<in>\<lceil>(E\<^sub>1 - \<guillemotleft>cs\<guillemotright>)\<rceil>\<^sub>S\<^sub>< \<bullet> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u $ref\<^sup>>) \<and>
                    [\<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t)"
    by (rel_auto)
       (metis Diff_iff Diff_subset Int_Diff Un_Diff_Int semilattice_inf_class.inf.idem semilattice_sup_class.sup.absorb_iff1 semilattice_sup_class.sup.commute set_eq_subset) 
  also have "... = (\<^bold>\<exists> trace \<bullet> \<E>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>, \<guillemotleft>trace\<guillemotright>, E\<^sub>1 - \<guillemotleft>cs\<guillemotright>))"
    by (rel_auto)
  finally show ?thesis .
qed

lemma InterMerge_csp_do_csp_enable [rpred]:
  "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>cs\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = 
   (\<^bold>\<exists> trace \<bullet> \<E>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> t\<^sub>1 \<star>\<^bsub>cs\<^esub> t\<^sub>2 \<and> t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>2 \<restriction> \<guillemotleft>cs\<guillemotright>,\<guillemotleft>trace\<guillemotright>,E\<^sub>2 - \<guillemotleft>cs\<guillemotright>))" 
  (is "?lhs = ?rhs")
proof -
  have "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) \<lbrakk>cs\<rbrakk>\<^sup>I \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) = \<E>(s\<^sub>2,t\<^sub>2,E\<^sub>2) \<lbrakk>cs\<rbrakk>\<^sup>I \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1)"
    by (simp add: CSPInterMerge_commute)
  also have "... = ?rhs"
    by (simp add: rpred trace_merge_commute eq_upred_sym, rel_auto)
  finally show ?thesis .
qed

lemma CSPInterMerge_or_left [rpred]: 
  "(P \<or> Q) \<lbrakk>cs\<rbrakk>\<^sup>I R = (P \<lbrakk>cs\<rbrakk>\<^sup>I R \<or> Q \<lbrakk>cs\<rbrakk>\<^sup>I R)"
  by (simp add: CSPInterMerge_def par_by_merge_or_left)

lemma CSPInterMerge_or_right [rpred]:
  "P \<lbrakk>cs\<rbrakk>\<^sup>I (Q \<or> R) = (P \<lbrakk>cs\<rbrakk>\<^sup>I Q \<or> P \<lbrakk>cs\<rbrakk>\<^sup>I R)"
  by (simp add: CSPInterMerge_def par_by_merge_or_right)

lemma CSPFinalMerge_or_left [rpred]: 
  "(P \<or> Q) \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F R = (P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F R \<or> Q \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F R)"
  by (simp add: CSPFinalMerge_def par_by_merge_or_left)

lemma CSPFinalMerge_or_right [rpred]:
  "P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F (Q \<or> R) = (P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q \<or> P \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F R)"
  by (simp add: CSPFinalMerge_def par_by_merge_or_right)

lemma CSPInterMerge_UINF_mem_left [rpred]: 
  "(\<Sqinter> i\<in>A \<bullet> P(i)) \<lbrakk>cs\<rbrakk>\<^sup>I Q = (\<Sqinter> i\<in>A \<bullet> P(i) \<lbrakk>cs\<rbrakk>\<^sup>I Q)"
  by (simp add: CSPInterMerge_def par_by_merge_USUP_mem_left)

lemma CSPInterMerge_UINF_ind_left [rpred]: 
  "(\<Sqinter> i \<bullet> P(i)) \<lbrakk>cs\<rbrakk>\<^sup>I Q = (\<Sqinter> i \<bullet> P(i) \<lbrakk>cs\<rbrakk>\<^sup>I Q)"
  by (simp add: CSPInterMerge_def par_by_merge_USUP_ind_left)

lemma CSPInterMerge_UINF_mem_right [rpred]: 
  "P \<lbrakk>cs\<rbrakk>\<^sup>I (\<Sqinter> i\<in>A \<bullet> Q(i)) = (\<Sqinter> i\<in>A \<bullet> P \<lbrakk>cs\<rbrakk>\<^sup>I Q(i))"
  by (simp add: CSPInterMerge_def par_by_merge_USUP_mem_right)

lemma CSPInterMerge_UINF_ind_right [rpred]: 
  "P \<lbrakk>cs\<rbrakk>\<^sup>I (\<Sqinter> i \<bullet> Q(i)) = (\<Sqinter> i \<bullet> P \<lbrakk>cs\<rbrakk>\<^sup>I Q(i))"
  by (simp add: CSPInterMerge_def par_by_merge_USUP_ind_right)

lemma CSPInterMerge_shEx_left [rpred]: 
  "(\<^bold>\<exists> i \<bullet> P(i)) \<lbrakk>cs\<rbrakk>\<^sup>I Q = (\<^bold>\<exists> i \<bullet> P(i) \<lbrakk>cs\<rbrakk>\<^sup>I Q)"
  using CSPInterMerge_UINF_ind_left[of P cs Q]
  by (simp add: UINF_is_exists)

lemma CSPInterMerge_shEx_right [rpred]: 
  "P \<lbrakk>cs\<rbrakk>\<^sup>I (\<^bold>\<exists> i \<bullet> Q(i)) = (\<^bold>\<exists> i \<bullet> P \<lbrakk>cs\<rbrakk>\<^sup>I Q(i))"
  using CSPInterMerge_UINF_ind_right[of P cs Q]
  by (simp add: UINF_is_exists)

lemma par_by_merge_seq_remove: "(P \<parallel>\<^bsub>M ;; R\<^esub> Q) = (P \<parallel>\<^bsub>M\<^esub> Q) ;; R"
  by (simp add: par_by_merge_seq_add[THEN sym])

lemma utrace_leq: "(x \<le>\<^sub>u y) = (\<^bold>\<exists> z \<bullet> y = x ^\<^sub>u \<guillemotleft>z\<guillemotright>)"
  by (rel_auto)

lemma trace_pred_R1_true: "[P(trace)]\<^sub>t ;; R1 true =  [(\<^bold>\<exists> tt\<^sub>0 \<bullet> \<guillemotleft>tt\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>trace\<guillemotright> \<and> P(tt\<^sub>0))]\<^sub>t"
  apply (rel_auto)
  using minus_cancel_le apply blast
  apply (metis diff_add_cancel_left' le_add trace_class.add_diff_cancel_left trace_class.add_left_mono)
  done

lemma wrC_csp_do_init [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) wr[cs]\<^sub>C \<I>(s\<^sub>2, t\<^sub>2) = 
   (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<I>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1  \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>, \<guillemotleft>tt\<^sub>1\<guillemotright>))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<not>\<^sub>r (\<Sqinter> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0). 
              [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r \<I>(s\<^sub>2, t\<^sub>2)) \<and>
              [s\<^sub>1]\<^sub>S\<^sub>< \<and>
              $ref\<^sup>> \<subseteq> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
              [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> 
              st\<^sup>> = $st) ;; R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove merge_csp_do_right pr_var_def closure Healthy_if rpred, rel_auto)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<lceil>s\<^sub>2\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> [s\<^sub>1]\<^sub>S\<^sub>< \<and>
                     [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (rel_auto)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<lceil>s\<^sub>2\<rceil>\<^sub>S\<^sub>< \<and> (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<guillemotleft>tt\<^sub>0\<guillemotright> = \<lceil>t\<^sub>2\<rceil>\<^sub>S\<^sub>< ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)) \<and> [s\<^sub>1]\<^sub>S\<^sub>< \<and>
                     [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (simp add: utrace_leq)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>1 \<bullet> [s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (rel_auto)
  also have "... =
        (\<^bold>\<forall> tt\<^sub>1 \<bullet> \<not>\<^sub>r ([s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t ;; R1 true))"
    by (rel_auto)
  also have "... =
        (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<not>\<^sub>r ([s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>trace\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t))"
    by (simp add: trace_pred_R1_true, rel_auto)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

lemma wrC_csp_do_false [wp]:
  "\<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) wr[cs]\<^sub>C false = 
  (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<I>(s\<^sub>1 \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = \<Phi>(s\<^sub>1,\<sigma>\<^sub>1,t\<^sub>1) wr[cs]\<^sub>C \<I>(true, \<guillemotleft>[]\<guillemotright>)"
    by (simp add: rpred)
  also have "... = ?rhs"
    by (simp add: wp)
  finally show ?thesis .
qed
  
lemma wrC_csp_enable_init [wp]:
  fixes t\<^sub>1  t\<^sub>2 :: "('a list, 'b) uexpr"
  shows
  "\<E>(s\<^sub>1,t\<^sub>1,E\<^sub>1) wr[cs]\<^sub>C \<I>(s\<^sub>2, t\<^sub>2) = 
   (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<I>(s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1  \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>, \<guillemotleft>tt\<^sub>1\<guillemotright>))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = 
        (\<not>\<^sub>r (\<^bold>\<exists> (ref\<^sub>0, ref\<^sub>1, st\<^sub>0, st\<^sub>1 :: 'b,
           tt\<^sub>0) \<bullet> [s\<^sub>1]\<^sub>S\<^sub>< \<and>
                   [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<not>\<^sub>r \<I>(s\<^sub>2,t\<^sub>2)) \<and>
                   (\<^bold>\<forall> e \<bullet> \<guillemotleft>e\<guillemotright> \<in> \<lceil>E\<^sub>1\<rceil>\<^sub>S\<^sub>< \<Rightarrow> \<guillemotleft>e\<guillemotright> \<notin>\<^sub>u \<guillemotleft>ref\<^sub>1\<guillemotright>) \<and>
                   $ref\<^sup>> \<subseteq> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<union> \<guillemotleft>ref\<^sub>1\<guillemotright>) \<inter> \<guillemotleft>cs\<guillemotright> \<union> (\<guillemotleft>ref\<^sub>0\<guillemotright> \<inter> \<guillemotleft>ref\<^sub>1\<guillemotright> - \<guillemotleft>cs\<guillemotright>) \<and>
                   [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t \<and> st\<^sup>> = $st) ;;\<^sub>h
          R1 true)"
    by (simp add: wrR_def par_by_merge_seq_remove merge_csp_enable_right pr_var_def closure Healthy_if rpred, rel_auto)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<lceil>s\<^sub>2\<rceil>\<^sub>S\<^sub>< \<and> \<lceil>t\<^sub>2\<rceil>\<^sub>S\<^sub>< \<le>\<^sub>u \<guillemotleft>tt\<^sub>0\<guillemotright>) \<and> [s\<^sub>1]\<^sub>S\<^sub>< \<and>
                     [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (rel_blast)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>0 \<bullet> (\<lceil>s\<^sub>2\<rceil>\<^sub>S\<^sub>< \<and> (\<^bold>\<exists> tt\<^sub>1 \<bullet> \<guillemotleft>tt\<^sub>0\<guillemotright> = \<lceil>t\<^sub>2\<rceil>\<^sub>S\<^sub>< ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>)) \<and> [s\<^sub>1]\<^sub>S\<^sub>< \<and>
                     [\<guillemotleft>trace\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (simp add: utrace_leq)
  also have "... =
        (\<not>\<^sub>r (\<^bold>\<exists> tt\<^sub>1 \<bullet> [s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t) ;; R1 true)"
    by (rel_auto)
  also have "... =
        (\<^bold>\<forall> tt\<^sub>1 \<bullet> \<not>\<^sub>r ([s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>trace\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t ;; R1 true))"
    by (rel_auto)
  also have "... =
        (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<not>\<^sub>r ([s\<^sub>1 \<and> s\<^sub>2 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<le>\<^sub>u \<guillemotleft>trace\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<in> (t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright>) \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> t\<^sub>2 ^\<^sub>u \<guillemotleft>tt\<^sub>1\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>]\<^sub>t))"
    by (simp add: trace_pred_R1_true, rel_auto)
  also have "... = ?rhs"
    by (rel_auto)
  finally show ?thesis .
qed

lemma wrC_csp_enable_false [wp]:
  "\<E>(s\<^sub>1,t\<^sub>1,E) wr[cs]\<^sub>C false = 
  (\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<I>(s\<^sub>1 \<and> \<guillemotleft>tt\<^sub>1\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> t\<^sub>1 \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = t\<^sub>1 \<restriction> \<guillemotleft>cs\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>))"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = \<E>(s\<^sub>1,t\<^sub>1,E) wr[cs]\<^sub>C \<I>(true, \<guillemotleft>[]\<guillemotright>)"
    by (simp add: rpred)
  also have "... = ?rhs"
    by (simp add: wp)
  finally show ?thesis .
qed

subsection \<open> Parallel operator \<close>

syntax
  "_par_circus"   :: "logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic"  ("_ \<lbrakk>_\<parallel>_\<parallel>_\<rbrakk> _" [75,0,0,0,76] 76)
  "_par_csp"      :: "logic \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("_ \<lbrakk>_\<rbrakk>\<^sub>C _" [75,0,76] 76)
  "_inter_circus" :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic"  ("_ \<lbrakk>_\<parallel>_\<rbrakk> _" [75,0,0,76] 76)
  
translations
  "_par_circus P ns1 cs ns2 Q" == "P \<parallel>\<^bsub>M\<^sub>C ns1 cs ns2\<^esub> Q"
  "_par_csp P cs Q" == "_par_circus P 0\<^sub>L cs 0\<^sub>L Q"
  "_inter_circus P ns1 ns2 Q" == "_par_circus P ns1 {} ns2 Q"

abbreviation InterleaveCSP :: "('s, 'e) action \<Rightarrow> ('s, 'e) action \<Rightarrow> ('s, 'e) action" (infixr "|||" 75)
where "P ||| Q \<equiv> P \<lbrakk>\<emptyset>\<parallel>\<emptyset>\<rbrakk> Q"

abbreviation SynchroniseCSP :: "('s, 'e) action \<Rightarrow> ('s, 'e) action \<Rightarrow> ('s, 'e) action" (infixr "||" 75)
where "P || Q \<equiv> P \<lbrakk>UNIV\<rbrakk>\<^sub>C Q"

definition CSP5 :: "'\<phi> process \<Rightarrow> '\<phi> process" where
[pred]: "CSP5(P) = (P ||| Skip)"

definition C2 :: "('\<sigma>, '\<phi>) action \<Rightarrow> ('\<sigma>, '\<phi>) action" where
[pred]: "C2(P) = (P \<lbrakk>\<Sigma>\<parallel>{}\<parallel>\<emptyset>\<rbrakk> Skip)"

definition CACT :: "('s, 'e) action \<Rightarrow> ('s, 'e) action" where
[pred]: "CACT(P) = C2(NCSP(P))"

abbreviation CPROC :: "'e process \<Rightarrow> 'e process" where
"CPROC(P) \<equiv> CACT(P)"

lemma Skip_right_form:
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "P\<^sub>3 is RR" "st\<^sup>> \<sharp> P\<^sub>2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) ;; Skip = \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> (\<exists> ref\<^sup>> \<Zspot> P\<^sub>3))"
proof -
  have 1:"RR(P\<^sub>3) ;; \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) = (\<exists> ref\<^sup>> \<Zspot> RR(P\<^sub>3))"
    by (rel_auto)
  show ?thesis
    by (rdes_simp cls: assms, metis "1" Healthy_if assms(3))
qed

lemma ParCSP_rdes_def [rdes_def]:
  fixes P\<^sub>1 :: "('s,'e) action"
  assumes "P\<^sub>1 is CRC" "Q\<^sub>1 is CRC" "P\<^sub>2 is CRR" "Q\<^sub>2 is CRR" "P\<^sub>3 is CRR" "Q\<^sub>3 is CRR" 
          "st\<^sup>> \<sharp> P\<^sub>2" "st\<^sup>> \<sharp> Q\<^sub>2" 
          "ns1 \<bowtie> ns2"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> \<^bold>R\<^sub>s(Q\<^sub>1 \<turnstile> Q\<^sub>2 \<diamondop> Q\<^sub>3) = 
         \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[cs]\<^sub>C P\<^sub>1 \<and> (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[cs]\<^sub>C P\<^sub>1 \<and> 
              (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[cs]\<^sub>C Q\<^sub>1 \<and> (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[cs]\<^sub>C Q\<^sub>1) \<turnstile>
             (P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or> P\<^sub>3 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or> P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>3) \<diamondop>
             (P\<^sub>3 \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q\<^sub>3))"
  (is "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = ?rhs")
proof -
  have 1: "\<And> P Q. P wr\<^sub>R(N\<^sub>C ns1 cs ns2) Q = P wr[cs]\<^sub>C Q" "\<And> P Q. P wr\<^sub>R(N\<^sub>C ns2 cs ns1) Q = P wr[cs]\<^sub>C Q"
    by (rel_auto)+
  have 2: "(\<exists> st\<^sup>> \<bullet> N\<^sub>C ns1 cs ns2) = (\<exists> st\<^sup>> \<bullet> N\<^sub>C 0\<^sub>L cs 0\<^sub>L)"
    by (rel_auto)
  have "?P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ?Q = (?P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> ?Q) ;;\<^sub>h Skip"
    by (simp add: CSPMerge_def par_by_merge_seq_add)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[cs]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[cs]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[cs]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[cs]\<^sub>C Q\<^sub>1) \<turnstile>
                    (P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or>
                     P\<^sub>3 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or> 
                     P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>3) \<diamondop>
                     P\<^sub>3 \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q\<^sub>3) ;;\<^sub>h Skip"
    by (simp add: parallel_rdes_def swap_CSPInnerMerge CSPInterMerge_def closure assms 1 2)
  also 
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[cs]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[cs]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[cs]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[cs]\<^sub>C Q\<^sub>1) \<turnstile>
                    (P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or>
                     P\<^sub>3 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or> 
                     P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>3) \<diamondop>
                    (\<exists> ref\<^sup>> \<Zspot> (P\<^sub>3 \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q\<^sub>3)))"
     by (simp add: Skip_right_form  closure parallel_RR_closed assms unrest)
  also
  have "... =  \<^bold>R\<^sub>s (((Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>2) wr[cs]\<^sub>C P\<^sub>1 \<and>
                    (Q\<^sub>1 \<Rightarrow>\<^sub>r Q\<^sub>3) wr[cs]\<^sub>C P\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>2) wr[cs]\<^sub>C Q\<^sub>1 \<and> 
                    (P\<^sub>1 \<Rightarrow>\<^sub>r P\<^sub>3) wr[cs]\<^sub>C Q\<^sub>1) \<turnstile>
                    (P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or>
                     P\<^sub>3 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>2 \<or> 
                     P\<^sub>2 \<lbrakk>cs\<rbrakk>\<^sup>I Q\<^sub>3) \<diamondop>
                    (P\<^sub>3 \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q\<^sub>3))"
  proof -
    have "(\<exists> ref\<^sup>> \<Zspot> (P\<^sub>3 \<parallel>\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q\<^sub>3)) = (P\<^sub>3 \<lbrakk>ns1|cs|ns2\<rbrakk>\<^sup>F Q\<^sub>3)"
      by (rel_blast)
    thus ?thesis by simp
  qed
  finally show ?thesis .
qed
       
subsection \<open> Parallel Laws \<close>

lemma ParCSP_expand:
  "P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q = (P \<parallel>\<^sub>R\<^bsub>N\<^sub>C ns1 cs ns2\<^esub> Q) ;; Skip"
  by (simp add: CSPMerge_def par_by_merge_seq_add)
    
lemma parallel_is_CSP [closure]:
  assumes "P is CSP" "Q is CSP"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CSP"
proof -
  have "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) is CSP"
    by (simp add: closure assms)
  hence "(P \<parallel>\<^bsub>M\<^sub>R(N\<^sub>C ns1 cs ns2)\<^esub> Q) ;; Skip is CSP"
    by (simp add: closure)
  thus ?thesis
    by (simp add: CSPMerge_def par_by_merge_seq_add)
qed  

lemma parallel_is_NCSP [closure]:
  assumes "ns1 \<bowtie> ns2" "P is NCSP" "Q is NCSP"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is NCSP"
proof -
  have "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = (\<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> \<^bold>R\<^sub>s(pre\<^sub>R Q \<turnstile> peri\<^sub>R Q \<diamondop> post\<^sub>R Q))"
    by (metis NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_design_alt assms wait'_cond_peri_post_cmt)
  also have "... is NCSP"
    by (simp add: ParCSP_rdes_def assms closure unrest)
  finally show ?thesis .
qed

theorem parallel_commutative:
  assumes "ns1 \<bowtie> ns2"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = (Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P)"
proof -
  have "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = P \<parallel>\<^bsub>swap\<^sub>m ;; (M\<^sub>C ns2 cs ns1)\<^esub> Q"
    by (simp add: CSPMerge_def seqr_assoc[THEN sym] swap_merge_rd swap_CSPInnerMerge lens_indep_sym assms)
  also have "... = Q \<lbrakk>ns2\<parallel>cs\<parallel>ns1\<rbrakk> P"
    by (metis par_by_merge_commute_swap)
  finally show ?thesis .
qed

text \<open> @{term CSP5} is precisely @{term C2} when applied to a process \<close>

lemma CSP5_is_C2:
  fixes P :: "'e process"
  assumes "P is NCSP"
  shows "CSP5(P) = C2(P)"
  unfolding CSP5_def C2_def by (rdes_eq cls: assms)

text \<open> The form of C2 tells us that a normal CSP process has a downward closed set of refusals \<close>

lemma csp_do_triv_merge:
  assumes "P is CRF"
  shows "P \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) = P" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<^bold>\<exists> (st\<^sub>0, t\<^sub>0) \<bullet> [st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>t\<^sub>0\<guillemotright>] \<dagger> CRF(P) \<and> [true]\<^sub>S\<^sub>< \<and> [\<guillemotleft>trace\<guillemotright> = \<guillemotleft>t\<^sub>0\<guillemotright>]\<^sub>t \<and> st\<^sup>> = $st \<oplus> \<guillemotleft>st\<^sub>0\<guillemotright> on &\<^bold>v \<oplus> \<guillemotleft>id\<guillemotright>($st)\<^sub>a on \<emptyset>)"
    by (simp add: FinalMerge_csp_do_right assms closure unrest Healthy_if, rel_auto)
  also have "... = CRF(P)"
    by (rel_auto)
  finally show ?thesis
    by (simp add: assms Healthy_if)
qed
  
lemma csp_do_triv_wr:
  assumes "P is CRC"
  shows "\<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) wr[{}]\<^sub>C P = P" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<not>\<^sub>r (\<Sqinter> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0). 
                   [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> $ref\<^sup>>;st\<^sup>> \<bullet> RR(\<not>\<^sub>r P)) \<and>
                    $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> = \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> 
                    st\<^sup>> = $st) ;; R1 true)"
      by (simp add: wrR_def par_by_merge_seq_remove rpred merge_csp_do_right ex_unrest Healthy_if pr_var_def closure assms unrest usubst, rel_auto)
  also have "... = (\<not>\<^sub>r (\<exists> $ref\<^sup>>;st\<^sup>> \<bullet> RR(\<not>\<^sub>r P)) ;; R1 true)"
    by (rel_auto, meson order_refl)
  also have "... = (\<not>\<^sub>r (\<not>\<^sub>r P) ;; R1 true)"
    by (simp add: Healthy_if closure ex_unrest unrest assms)
  also have "... = P"
    by (metis CRC_implies_RC Healthy_def RC1_def RC_implies_RC1 assms)
  finally show ?thesis .
qed

lemma C2_form:
  assumes "P is NCSP"
  shows "C2(P) = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<^sup>>\<rbrakk> \<and> $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
proof -
  have 1:"\<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) wr[{}]\<^sub>C pre\<^sub>R P = pre\<^sub>R P" (is "?lhs = ?rhs")
    by (simp add: csp_do_triv_wr closure assms)
  have 2: "(pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>{}\<rbrakk>\<^sup>I \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) = 
           (\<^bold>\<exists> ref\<^sub>0 \<bullet> (peri\<^sub>R P)\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<^sup>>\<rbrakk> \<and> $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright>)" (is "?lhs = ?rhs")
  proof -
    have "?lhs = peri\<^sub>R P \<lbrakk>{}\<rbrakk>\<^sup>I \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>)"
      by (simp add: SRD_peri_under_pre closure assms unrest)
    also have "... = (\<exists> st\<^sup>> \<bullet> (peri\<^sub>R P \<parallel>\<^bsub> N\<^sub>C 0\<^sub>L {} 0\<^sub>L\<^esub> \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>)))"
      by (simp add: CSPInterMerge_def par_by_merge_def seqr_exists_right)
    also have "... = 
         (\<exists> st\<^sup>> \<bullet> \<Sqinter> (ref\<^sub>0, st\<^sub>0, tt\<^sub>0). 
            [ref\<^sup>> \<leadsto> \<guillemotleft>ref\<^sub>0\<guillemotright>, st\<^sup>> \<leadsto> \<guillemotleft>st\<^sub>0\<guillemotright>, tr\<^sup>< \<leadsto> \<guillemotleft>[]\<guillemotright>, tr\<^sup>> \<leadsto> \<guillemotleft>tt\<^sub>0\<guillemotright>] \<dagger> (\<exists> st\<^sup>> \<bullet> RR(peri\<^sub>R P)) \<and>
             $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright> \<and> [\<guillemotleft>trace\<guillemotright> = \<guillemotleft>tt\<^sub>0\<guillemotright>]\<^sub>t \<and> st\<^sup>> = $st)"
      by (simp add: merge_csp_do_right pr_var_def assms Healthy_if closure rpred unrest ex_unrest, rel_auto)
    also have "... = 
         (\<^bold>\<exists> ref\<^sub>0 \<bullet> (\<exists> st\<^sup>> \<bullet> RR(peri\<^sub>R P))\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<^sup>>\<rbrakk> \<and> $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright>)"
      by (rel_auto)
    also have "... = ?rhs"
      by (simp add: closure ex_unrest Healthy_if unrest assms)
    finally show ?thesis .
  qed
  have 3: "(pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) = post\<^sub>R(P)" (is "?lhs = ?rhs")
    by (simp add: csp_do_triv_merge SRD_post_under_pre unrest assms closure)
  show ?thesis
  proof -
    have "C2(P) = \<^bold>R\<^sub>s (\<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) wr[{}]\<^sub>C pre\<^sub>R P \<turnstile>
          (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P) \<lbrakk>{}\<rbrakk>\<^sup>I \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>) \<diamondop> (pre\<^sub>R P \<Rightarrow>\<^sub>r post\<^sub>R P) \<lbrakk>\<Sigma>|{}|\<emptyset>\<rbrakk>\<^sup>F \<Phi>(true,id\<^sub>s,\<guillemotleft>[]\<guillemotright>))"
      by (simp add: C2_def, rdes_simp cls: assms)
    also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> (\<^bold>\<exists> ref\<^sub>0 \<bullet> peri\<^sub>R P\<lbrakk>\<guillemotleft>ref\<^sub>0\<guillemotright>/$ref\<^sup>>\<rbrakk> \<and> $ref\<^sup>> \<subseteq> \<guillemotleft>ref\<^sub>0\<guillemotright>) \<diamondop> post\<^sub>R P)"
      by (simp add: 1 2 3)
    finally show ?thesis .
  qed
qed

lemma C2_CDC_form:
  assumes "P is NCSP"
  shows "C2(P) = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> CDC(peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
  by (simp add: C2_form assms CDC_def)

lemma C2_rdes_def:
  assumes "P\<^sub>1 is CRC" "P\<^sub>2 is CRR" "P\<^sub>3 is CRR" "st\<^sup>> \<sharp> P\<^sub>2" "$ref\<^sup>> \<sharp> P\<^sub>3"
  shows "C2(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> CDC(P\<^sub>2) \<diamondop> P\<^sub>3)"
  by (simp add: C2_form assms closure rdes unrest usubst, rel_auto)

lemma C2_NCSP_intro:
  assumes "P is NCSP" "peri\<^sub>R(P) is CDC"
  shows "P is C2"
proof -
  have "C2(P) = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> CDC(peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
    by (simp add: C2_CDC_form assms(1))
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)"
    by (simp add: Healthy_if assms)
  also have "... = P"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma C2_rdes_intro:
  assumes "P\<^sub>1 is CRC" "P\<^sub>2 is CRR" "P\<^sub>2 is CDC" "P\<^sub>3 is CRR" "st\<^sup>> \<sharp> P\<^sub>2" "$ref\<^sup>> \<sharp> P\<^sub>3"
  shows "\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) is C2"
  unfolding Healthy_def
  by (simp add: C2_rdes_def assms unrest closure Healthy_if)

lemma C2_implies_CDC_peri [closure]:
  assumes "P is NCSP" "P is C2"
  shows "peri\<^sub>R(P) is CDC"
proof -
  have "peri\<^sub>R(P) = peri\<^sub>R (\<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> CDC(peri\<^sub>R P) \<diamondop> post\<^sub>R P))"
    by (metis C2_CDC_form Healthy_if assms(1) assms(2))
  also have "... = CDC (pre\<^sub>R P \<Rightarrow>\<^sub>r peri\<^sub>R P)"
    by (simp add: rdes rpred assms closure unrest del: NSRD_peri_under_pre)
  also have "... = CDC (peri\<^sub>R P)"
    by (simp add: SRD_peri_under_pre closure unrest assms)
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma CACT_intro:
  assumes "P is NCSP" "P is C2"
  shows "P is CACT"
  by (metis CACT_def Healthy_def assms(1) assms(2))

lemma CACT_rdes_intro:
  assumes "P\<^sub>1 is CRC" "P\<^sub>2 is CRR" "P\<^sub>2 is CDC" "P\<^sub>3 is CRR" "st\<^sup>> \<sharp> P\<^sub>2" "$ref\<^sup>> \<sharp> P\<^sub>3"
  shows "\<^bold>R\<^sub>s (P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3) is CACT"
  by (rule CACT_intro, simp add: closure assms, rule C2_rdes_intro, simp_all add: assms)

lemma C2_NCSP_quasi_commute:
  assumes "P is NCSP"
  shows "C2(NCSP(P)) = NCSP(C2(P))"
proof -
  have 1: "C2(NCSP(P)) = C2(P)"
    by (simp add: assms Healthy_if)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> CDC(peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
    by (simp add: C2_CDC_form assms)
  also have "... is NCSP"
    by (rule NCSP_rdes_intro, simp_all add: closure assms unrest)
  finally show ?thesis
    by (simp add: Healthy_if 1)
qed

lemma C2_quasi_idem:
  assumes "P is NCSP"
  shows "C2(C2(P)) = C2(P)"
proof -
  have "C2(C2(P)) = C2(C2(\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))))"
    by (simp add: NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_tri_design assms)
  also have "... = \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> CDC (peri\<^sub>R P) \<diamondop> post\<^sub>R P)"
    by (simp add: C2_rdes_def closure assms unrest CDC_idem)
  also have "... = C2(P)"
    by (simp add: C2_CDC_form assms)
  finally show ?thesis .
qed

lemma CACT_implies_NCSP [closure]:
  assumes "P is CACT"
  shows "P is NCSP"
proof - 
  have "P = C2(NCSP(NCSP(P)))"
    by (metis CACT_def Healthy_Idempotent Healthy_if NCSP_Idempotent assms)
  also have "... = NCSP(C2(NCSP(P)))"
    by (simp add: C2_NCSP_quasi_commute Healthy_Idempotent NCSP_Idempotent)
  also have "... is NCSP"
    by (metis CACT_def Healthy_def assms calculation)
  finally show ?thesis .
qed

lemma CACT_implies_C2 [closure]:
  assumes "P is CACT"
  shows "P is C2"
  by (metis CACT_def CACT_implies_NCSP Healthy_def assms)

lemma CACT_idem: "CACT(CACT(P)) = CACT(P)"
  by (simp add: CACT_def C2_NCSP_quasi_commute[THEN sym] C2_quasi_idem Healthy_Idempotent Healthy_if NCSP_Idempotent)

lemma CACT_Idempotent: "Idempotent CACT"
  by (simp add: CACT_idem Idempotent_def)

lemma PACT_elim [RD_elim]: 
  "\<lbrakk> X is CACT; P(\<^bold>R\<^sub>s(pre\<^sub>R(X) \<turnstile> peri\<^sub>R(X) \<diamondop> post\<^sub>R(X))) \<rbrakk> \<Longrightarrow> P(X)"
  using CACT_implies_NCSP NCSP_elim by blast

lemma Miracle_C2_closed [closure]: "Miracle is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma Chaos_C2_closed [closure]: "Chaos is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma Skip_C2_closed [closure]: "Skip is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma Stop_C2_closed [closure]: "Stop is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma Miracle_CACT_closed [closure]: "Miracle is CACT"
  by (simp add: CACT_intro Miracle_C2_closed csp_theory.top_closed)

lemma Chaos_CACT_closed [closure]: "Chaos is CACT"
  by (simp add: CACT_intro closure)

lemma Skip_CACT_closed [closure]: "Skip is CACT"
  by (simp add: CACT_intro closure)

lemma Stop_CACT_closed [closure]: "Stop is CACT"
  by (simp add: CACT_intro closure)

lemma seq_C2_closed [closure]:
  assumes "P is NCSP" "P is C2" "Q is NCSP" "Q is C2"
  shows "P ;; Q is C2"
  by (rdes_simp cls: assms(1,3), rule C2_rdes_intro, simp_all add: closure assms unrest)

lemma seq_CACT_closed [closure]:
  assumes "P is CACT" "Q is CACT"
  shows "P ;; Q is CACT"
  by (meson CACT_implies_C2 CACT_implies_NCSP CACT_intro assms csp_theory.Healthy_Sequence seq_C2_closed)

lemma AssignsCSP_C2 [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma AssignsCSP_CACT [closure]: "\<langle>\<sigma>\<rangle>\<^sub>C is CACT"
  by (simp add: CACT_intro closure)

lemma map_st_ext_CDC_closed [closure]:
  assumes "P is CDC"
  shows "P \<oplus>\<^sub>r map_st\<^sub>L[a] is CDC"
proof -
  have "CDC P \<oplus>\<^sub>r map_st\<^sub>L[a] is CDC"
    by (rel_auto)
  thus ?thesis
    by (simp add: assms Healthy_if)
qed

lemma rdes_frame_ext_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "a:[P]\<^sub>R\<^sup>+ is C2"
  by (rdes_simp cls:assms(2), rule C2_rdes_intro, simp_all add: closure assms unrest)

lemma rdes_frame_ext_CACT_closed [closure]:
  assumes "vwb_lens a" "P is CACT"
  shows "a:[P]\<^sub>R\<^sup>+ is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma UINF_C2_closed [closure]:
  assumes "A \<noteq> {}" "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "\<And> i. i \<in> A \<Longrightarrow> P(i) is C2"
  shows "(\<Sqinter> i\<in>A \<bullet> P(i)) is C2"
proof -
  have "(\<Sqinter> i\<in>A \<bullet> P(i)) = (\<Sqinter> i\<in>A \<bullet> \<^bold>R\<^sub>s(pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i))))"
    by (simp add: closure SRD_reactive_tri_design assms cong: UINF_cong)
  also have "... is C2"
    by (rdes_simp cls: assms, rule C2_rdes_intro, simp_all add: closure unrest assms)
  finally show ?thesis .
qed

lemma UINF_CACT_closed [closure]:
  assumes "A \<noteq> {}" "\<And> i. i \<in> A \<Longrightarrow> P(i) is CACT"
  shows "(\<Sqinter> i\<in>A \<bullet> P(i)) is CACT"
  by (rule CACT_intro, simp_all add: assms closure)

lemma inf_C2_closed [closure]: 
  assumes "P is NCSP" "Q is NCSP" "P is C2" "Q is C2"
  shows "P \<sqinter> Q is C2"
  by (rdes_simp cls: assms, rule C2_rdes_intro, simp_all add: closure unrest assms)

lemma cond_CDC_closed [closure]:
  assumes "P is CDC" "Q is CDC"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is CDC"
proof -
  have "CDC P \<triangleleft> b \<triangleright>\<^sub>R CDC Q is CDC"
    by (rel_auto)
  thus ?thesis 
    by (simp add: Healthy_if assms)
qed

lemma cond_C2_closed [closure]:
  assumes "P is NCSP" "Q is NCSP" "P is C2" "Q is C2"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is C2"
  by (rdes_simp cls: assms, rule C2_rdes_intro, simp_all add: closure unrest assms)

lemma cond_CACT_closed [closure]:
  assumes "P is CACT" "Q is CACT"
  shows "P \<triangleleft> b \<triangleright>\<^sub>R Q is CACT"
  by (rule CACT_intro, simp_all add: assms closure)

lemma gcomm_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "b \<rightarrow>\<^sub>R P is C2"
  by (rdes_simp cls: assms, rule C2_rdes_intro, simp_all add: closure unrest assms)

lemma SpecC_CACT [closure]: "a:[p,q]\<^sub>C is CACT"
  by (simp add: SpecC_def, rule CACT_rdes_intro, simp_all add: closure; rel_auto)

lemma AssumeCircus_CACT [closure]: "[b]\<^sub>C is CACT"
  by (metis AssumeCircus_NCSP AssumeCircus_def CACT_intro NCSP_Skip Skip_C2_closed gcomm_C2_closed)

lemma StateInvR_CACT [closure]: "sinv\<^sub>R(b) is CACT"
  by (simp add: CACT_rdes_intro rdes_def closure unrest)

lemma AlternateR_C2_closed [closure]:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "Q is NCSP"
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is C2" "Q is C2"
  shows "(if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi) is C2"
proof (cases "A = {}")
  case True
  then show ?thesis
    by (simp add: assms(4))
next
  case False
  then show ?thesis
    by (simp add: AlternateR_def closure assms)
qed

lemma AlternateR_CACT_closed [closure]:
  assumes "\<And> i. i \<in> A \<Longrightarrow> P(i) is CACT" "Q is CACT"
  shows "(if\<^sub>R i\<in>A \<bullet> g(i) \<rightarrow> P(i) else Q fi) is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma AlternateR_list_C2_closed [closure]:
  assumes 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP" "Q is NCSP"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is C2" "Q is C2"
  shows "(AlternateR_list A Q) is C2"
  apply (simp add: AlternateR_list_def)
  apply (rule AlternateR_C2_closed)
  apply (auto simp add: assms closure)
   apply (metis assms nth_mem prod.collapse)+
  done

lemma AlternateR_list_CACT_closed [closure]:
  assumes "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is CACT" "Q is CACT"
  shows "(AlternateR_list A Q) is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma R4_CRR_closed [closure]: "P is CRR \<Longrightarrow> R4(P) is CRR"
  by (rule CRR_intro, simp_all add: closure unrest R4_def)

lemma WhileC_C2_closed [closure]:
  assumes "P is NCSP" "P is Productive" "P is C2"
  shows "while\<^sub>C b do P od is C2"
proof -
  have "while\<^sub>C b do P od = while\<^sub>C b do Productive(\<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P)) od"
    by (simp add: assms Healthy_if SRD_reactive_tri_design closure)
  also have "... = while\<^sub>C b do \<^bold>R\<^sub>s (pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> R4(post\<^sub>R P)) od"
    by (simp add: Productive_RHS_design_form unrest assms rdes closure R4_def)
  also have "... is C2"
    by (simp add: WhileC_def, simp add: closure assms unrest rdes_def C2_rdes_intro)
  finally show ?thesis .
qed

lemma WhileC_CACT_closed [closure]:
  assumes "P is CACT" "P is Productive"
  shows "while\<^sub>C b do P od is CACT"
  using CACT_implies_C2 CACT_implies_NCSP CACT_intro WhileC_C2_closed WhileC_NCSP_closed assms by blast

lemma IterateC_C2_closed [closure]:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is NCSP" "\<And> i. i \<in> A \<Longrightarrow> P(i) is Productive" "\<And> i. i \<in> A \<Longrightarrow> P(i) is C2" 
  shows "(do\<^sub>C i\<in>A \<bullet> g(i) \<rightarrow> P(i) od) is C2"
  unfolding IterateC_def by (simp add: closure assms)

lemma IterateC_CACT_closed [closure]:
  assumes 
    "\<And> i. i \<in> A \<Longrightarrow> P(i) is CACT" "\<And> i. i \<in> A \<Longrightarrow> P(i) is Productive" 
  shows "(do\<^sub>C i\<in>A \<bullet> g(i) \<rightarrow> P(i) od) is CACT"
  by (metis CACT_implies_C2 CACT_implies_NCSP CACT_intro IterateC_C2_closed IterateC_NCSP_closed assms)
  
lemma IterateC_list_C2_closed [closure]:
  assumes 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is NCSP" 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is Productive"
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is C2"
  shows "(IterateC_list A) is C2"
  unfolding IterateC_list_def 
  by (rule IterateC_C2_closed, (metis assms atLeastLessThan_iff nth_map nth_mem prod.collapse)+)

lemma IterateC_list_CACT_closed [closure]:
  assumes 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is CACT" 
    "\<And> b P. (b, P) \<in> set A \<Longrightarrow> P is Productive"
  shows "(IterateC_list A) is CACT"
  by (metis CACT_implies_C2 CACT_implies_NCSP CACT_intro IterateC_list_C2_closed IterateC_list_NCSP_closed assms)

lemma GuardCSP_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "g &\<^sub>C P is C2"
  by (rdes_simp cls: assms(1), rule C2_rdes_intro, simp_all add: closure assms unrest)

lemma GuardCSP_CACT_closed [closure]:
  assumes "P is CACT"
  shows "g &\<^sub>C P is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma DoCSP_C2 [closure]:
  "do\<^sub>C(a) is C2"
  by (rdes_simp, rule C2_rdes_intro, simp_all add: closure unrest)

lemma DoCSP_CACT [closure]:
  "do\<^sub>C(a) is CACT"
  by (rule CACT_intro, simp_all add: closure)

lemma PrefixCSP_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "a \<rightarrow>\<^sub>C P is C2"
  unfolding PrefixCSP_def by (metis DoCSP_C2 Healthy_def NCSP_DoCSP NCSP_implies_CSP assms seq_C2_closed)

lemma PrefixCSP_CACT_closed [closure]:
  assumes "P is CACT"
  shows "a \<rightarrow>\<^sub>C P is CACT"
  using CACT_implies_C2 CACT_implies_NCSP CACT_intro NCSP_PrefixCSP PrefixCSP_C2_closed assms by blast

lemma ExtChoice_C2_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) is NCSP" "\<And> i. i \<in> I \<Longrightarrow> P(i) is C2"
  shows "(\<box> i\<in>I \<bullet> P(i)) is C2"
proof (cases "I = {}")
  case True
  then show ?thesis by (simp add: closure ExtChoice_empty)
next
  case False
  show ?thesis
    by (rule C2_NCSP_intro, simp_all add: assms closure unrest periR_ExtChoice' False)
qed

lemma ExtChoice_CACT_closed [closure]:
  assumes "\<And> i. i \<in> I \<Longrightarrow> P(i) is CACT"
  shows "(\<box> i\<in>I \<bullet> P(i)) is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma extChoice_C2_closed [closure]:
  assumes "P is NCSP" "P is C2" "Q is NCSP" "Q is C2"
  shows "P \<box> Q is C2"
proof -
  have "P \<box> Q = (\<box> I\<in>{P,Q} \<bullet> I)"
    by (metis eq_id_iff extChoice_def)
  also have "... is C2"
    by (rule ExtChoice_C2_closed, auto simp add: assms)
  finally show ?thesis .
qed

lemma extChoice_CACT_closed [closure]:
  assumes "P is CACT" "Q is CACT"
  shows "P \<box> Q is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma state_srea_C2_closed [closure]: 
  assumes "P is NCSP" "P is C2"
  shows "state 'a \<bullet> P is C2"
  by (rule C2_NCSP_intro, simp_all add: closure rdes assms)

lemma state_srea_CACT_closed [closure]: 
  assumes "P is CACT"
  shows "state 'a \<bullet> P is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

lemma parallel_C2_closed [closure]:
  assumes "ns1 \<bowtie> ns2" "P is NCSP" "Q is NCSP" "P is C2" "Q is C2"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is C2"
proof -
  have "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) = (\<^bold>R\<^sub>s(pre\<^sub>R P \<turnstile> peri\<^sub>R P \<diamondop> post\<^sub>R P) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> \<^bold>R\<^sub>s(pre\<^sub>R Q \<turnstile> peri\<^sub>R Q \<diamondop> post\<^sub>R Q))"
    by (metis NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_design_alt assms wait'_cond_peri_post_cmt)
  also have "... is C2"
    by (simp add: ParCSP_rdes_def C2_rdes_intro assms closure unrest)
  finally show ?thesis .
qed

lemma parallel_CACT_closed [closure]:
  assumes "ns1 \<bowtie> ns2" "P is CACT" "Q is CACT"
  shows "(P \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> Q) is CACT"
  by (meson CACT_implies_C2 CACT_implies_NCSP CACT_intro assms parallel_C2_closed parallel_is_NCSP)

lemma RenameCSP_C2_closed [closure]:
  assumes "P is NCSP" "P is C2"
  shows "P\<lparr>f\<rparr>\<^sub>C is C2"
  by (simp add: RenameCSP_def C2_rdes_intro RenameCSP_pre_CRC_closed closure assms unrest)

lemma RenameCSP_CACT_closed [closure]:
  assumes "P is CACT"
  shows "P\<lparr>f\<rparr>\<^sub>C is CACT"
  by (rule CACT_intro, simp_all add: closure assms)

text \<open> This property depends on downward closure of the refusals \<close>

lemma rename_extChoice_pre:
  assumes "inj f" "P is NCSP" "Q is NCSP" "P is C2" "Q is C2"
  shows "(P \<box> Q)\<lparr>f\<rparr>\<^sub>C = (P\<lparr>f\<rparr>\<^sub>C \<box> Q\<lparr>f\<rparr>\<^sub>C)"
  by (rdes_eq_split cls: assms)

lemma rename_extChoice:
  assumes "inj f" "P is CACT" "Q is CACT"
  shows "(P \<box> Q)\<lparr>f\<rparr>\<^sub>C = (P\<lparr>f\<rparr>\<^sub>C \<box> Q\<lparr>f\<rparr>\<^sub>C)"
  by (simp add: CACT_implies_C2 CACT_implies_NCSP assms rename_extChoice_pre)

lemma interleave_commute:
  "P ||| Q = Q ||| P"
  by (auto intro: parallel_commutative zero_lens_indep)

lemma interleave_unit:
  assumes "P is CPROC"
  shows "P ||| Skip = P"
  by (metis CACT_implies_C2 CACT_implies_NCSP CSP5_def CSP5_is_C2 Healthy_if assms)

lemma parallel_miracle:
  "P is NCSP \<Longrightarrow> Miracle \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> P = Miracle"
  by (simp add: CSPMerge_def par_by_merge_seq_add[THEN sym] Miracle_parallel_left_zero Skip_right_unit closure)

lemma parallel_assigns:
  assumes "vwb_lens ns1" "vwb_lens ns2" "ns1 \<bowtie> ns2" "x \<subseteq>\<^sub>L ns1" "y  \<subseteq>\<^sub>L ns2"
  shows "(x :=\<^sub>C u) \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> (y :=\<^sub>C v) = x, y :=\<^sub>C u, v"
  using assms by (rdes_eq)

(* Trying to find a form of reactive design which when interleaved with Chaos yields Chaos *)

definition Accept :: "('s, 'e) action" where
[upred_defs, rdes_def]: "Accept = \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(true,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>UNIV\<guillemotright>) \<diamondop> false)"

definition [upred_defs, rdes_def]: "CACC(P) = (P \<or> Accept)"

lemma CACC_form: 
  assumes "P\<^sub>1 is RC" "P\<^sub>2 is RR" "st\<^sup>> \<sharp> P\<^sub>2"  "P\<^sub>3 is RR"
  shows "CACC(\<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> P\<^sub>2 \<diamondop> P\<^sub>3)) = \<^bold>R\<^sub>s(P\<^sub>1 \<turnstile> (\<E>(true,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>UNIV\<guillemotright>) \<or> P\<^sub>2) \<diamondop> P\<^sub>3)"
  by (rdes_eq cls: assms)

lemma CACC_refines_Accept:
  assumes "P is CACC"
  shows "P \<sqsubseteq> Accept"
proof -
  have "CACC(P) \<sqsubseteq> Accept" by rel_auto
  thus ?thesis by (simp add: Healthy_if assms)
qed

lemma DoCSP_CACC [closure]: "do\<^sub>C(e) is CACC"
  unfolding Healthy_def by (rdes_eq)

lemma CACC_seq_closure_left [closure]:
  assumes "P is NCSP" "P is CACC" "Q is NCSP"
  shows "(P ;; Q) is CACC"
proof -
  have 1: "(P ;; Q) = CACC(P) ;; Q"
    by (simp add: Healthy_if assms(2))
  also have 2:"... = \<^bold>R\<^sub>s ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r pre\<^sub>R Q) \<turnstile> (peri\<^sub>R P \<or> \<E>(true,\<guillemotleft>[]\<guillemotright>, \<guillemotleft>UNIV\<guillemotright>) \<or> post\<^sub>R P ;; peri\<^sub>R Q) \<diamondop> post\<^sub>R P ;; post\<^sub>R Q)"
    by (rdes_simp cls: assms) 
  also have "... = CACC(...)"
    by (rdes_eq cls: assms)
  also have "... = CACC(P ;; Q)"
    by (simp add: "1" "2")
  finally show ?thesis
    by (simp add: Healthy_def)
qed

lemma CACC_seq_closure_right:
  assumes "P is NCSP" "P ;; Chaos = Chaos" "Q is NCSP" "Q is CACC"
  shows "(P ;; Q) is CACC"
  oops

lemma Chaos_is_CACC [closure]: "Chaos is CACC"
  unfolding Healthy_def by (rdes_eq)

lemma intChoice_is_CACC [closure]:
  assumes "P is NCSP" "P is CACC" "Q is NCSP" "Q is CACC"
  shows "P \<sqinter> Q is CACC"
proof -
  have "CACC(P) \<sqinter> CACC(Q) is CACC"
    unfolding Healthy_def by (rdes_eq cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms(2) assms(4))
qed

lemma extChoice_is_CACC [closure]:
  assumes "P is NCSP" "P is CACC" "Q is NCSP" "Q is CACC"
  shows "P \<box> Q is CACC"
proof -
  have "CACC(P) \<box> CACC(Q) is CACC"
    unfolding Healthy_def by (rdes_eq cls: assms)
  thus ?thesis
    by (simp add: Healthy_if assms(2) assms(4))
qed

lemma Chaos_par_zero:
  assumes "P is NCSP" "P is CACC" "ns1 \<bowtie> ns2"
  shows "Chaos \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> P = Chaos"
proof -
  have pprop: "(\<^bold>\<forall> (tt\<^sub>0, tt\<^sub>1) \<bullet> \<I>(\<guillemotleft>tt\<^sub>1\<guillemotright> \<in> \<guillemotleft>tt\<^sub>0\<guillemotright> \<star>\<^bsub>cs\<^esub> \<guillemotleft>[]\<guillemotright> \<and> \<guillemotleft>tt\<^sub>0\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright> = \<guillemotleft>[]\<guillemotright> \<restriction> \<guillemotleft>cs\<guillemotright>,\<guillemotleft>tt\<^sub>1\<guillemotright>)) = false"
    by (rel_simp, auto simp add: tr_par_empty)
       (metis append_Nil2 seq_filter_Nil takeWhile.simps(1))

  have 1:"P = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P))"
    by (simp add: NCSP_implies_NSRD NSRD_is_SRD SRD_reactive_tri_design assms(1))

  have "... \<sqsubseteq> \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> \<E>(true,\<guillemotleft>[]\<guillemotright>,\<guillemotleft>UNIV\<guillemotright>) \<diamondop> false)"
    by (metis "1" Accept_def CACC_refines_Accept assms(2))

  hence "peri\<^sub>R P \<sqsubseteq> (pre\<^sub>R P \<and> \<E>(true,\<guillemotleft>[]\<guillemotright>, \<guillemotleft>UNIV\<guillemotright>))"
    by (auto simp add: RHS_tri_design_refine' closure assms)

  hence "peri\<^sub>R(P) = ((pre\<^sub>R P \<and> \<E>(true,\<guillemotleft>[]\<guillemotright>, \<guillemotleft>UNIV\<guillemotright>)) \<or> peri\<^sub>R(P))"
    by (simp add: assms(2) utp_pred_laws.sup.absorb2)

  with 1 have "P = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (pre\<^sub>R(P) \<and> \<E>(true, \<guillemotleft>[]\<guillemotright>, \<guillemotleft>UNIV\<guillemotright>) \<or> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))

  also have "... = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> (\<E>(true, \<guillemotleft>[]\<guillemotright>, \<guillemotleft>UNIV\<guillemotright>) \<or> peri\<^sub>R(P)) \<diamondop> post\<^sub>R(P))"
    by (rel_auto)

  also have "Chaos \<lbrakk>ns1\<parallel>cs\<parallel>ns2\<rbrakk> ... = Chaos"
    by (rdes_simp cls: assms, simp add: pprop)

  finally show ?thesis .
qed

lemma Chaos_inter_zero:
  assumes "P is NCSP" "P is CACC"
  shows "Chaos ||| P = Chaos"
  by (simp add: Chaos_par_zero assms(1) assms(2))
*)

end