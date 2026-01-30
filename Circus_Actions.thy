theory Circus_Actions
  imports "UTP-Stateful-Failure.utp_sf_rdes" (* "Interaction_Trees.ITrees" *)
begin 

hide_const J


thm rpred (* Reactive predicate algebraic laws *)

lemma USUPs_combine:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> 'a pred"
  shows "(\<Squnion>i\<in>I. \<Squnion>j\<in>J. P i j) = (\<Squnion>(i,j)\<in>I\<times>J. P i j)"
  by pred_auto

lemma UINFs_combine:
  fixes P :: "'i \<Rightarrow> 'j \<Rightarrow> 'a pred"
  shows "(\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. P i j) = (\<Sqinter>(i,j)\<in>I\<times>J. P i j)"
  by pred_auto

lemma R5_idem [rpred]: "R5(R5 P) = R5 P"
  by pred_auto

lemma ExtChoice_const:  
  assumes "I \<noteq> {}" "P is NCSP"
  shows "(\<box> i\<in>I. P) = P"
  apply (rdes_expand cls:assms(2))
  apply (simp add: rdes_def rdes_rel_norms rdes rpred closure alpha frame usubst unrest wp assms(1) del: SEXP_apply)
  apply (rule_tac rdes_tri_eq_intro srdes_tri_eq_intro)
    apply simp
   apply pred_auto
  apply simp
  done (* rdes_eq cls:assms(2) simps:  assms(1) *)

lemma EXTCHOICE_combine: 
  assumes "\<And> i j. P i j is NCSP"
  shows "(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)"
proof (cases "I \<noteq> {} \<and> J \<noteq> {}")
  case True
  have 1:"I \<noteq> {}" using True by simp
  have 2:"J \<noteq> {}" using True by simp
  have "(\<box> i\<in>I. EXTCHOICE J (\<lambda> j. P i j)) 
         = (\<box> i\<in>I. EXTCHOICE J (\<lambda> j. \<^bold>R\<^sub>s(pre\<^sub>R(P i j) \<turnstile> peri\<^sub>R(P i j) \<diamondop> post\<^sub>R(P i j))))"
    by (metis (mono_tags, lifting) ExtChoice_cong NCSP_implies_CSP SRD_reactive_tri_design assms) 
  also have "... = 
   \<^bold>R\<^sub>s((\<Squnion>i\<in>I. \<Squnion>j\<in>J. pre\<^sub>R (P i j)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 ((\<Squnion>j\<in>J. R5 (peri\<^sub>R (P i j))) \<or> (\<Sqinter>j\<in>J. R4 (peri\<^sub>R (P i j))))) \<or>
       (\<Sqinter>i\<in>I. R4 ((\<Squnion>j\<in>J. R5 (peri\<^sub>R (P i j))) \<or> (\<Sqinter>j\<in>J. R4 (peri\<^sub>R (P i j)))))) \<diamondop>
      (\<Sqinter>i\<in>I. \<Sqinter>j\<in>J. post\<^sub>R (P i j)))"
    by (simp add: ExtChoice_tri_rdes' 1 2 closure unrest)
  also have "... = 
   \<^bold>R\<^sub>s ((\<Squnion>ij\<in>I \<times> J. pre\<^sub>R (P (fst ij) (snd ij))) \<turnstile>
      ((\<Squnion>ij\<in>I \<times> J. R5 (peri\<^sub>R (P (fst ij) (snd ij)))) \<or> (\<Sqinter>ij\<in>I \<times> J. R4 (peri\<^sub>R (P (fst ij) (snd ij))))) \<diamondop>
      (\<Sqinter>ij\<in>I \<times> J. post\<^sub>R (P (fst ij) (snd ij))))"
    by (simp add: USUPs_combine UINFs_combine rpred 1 2 split_beta)
  also have "... = (\<box> ij\<in>I \<times> J. \<^bold>R\<^sub>s(pre\<^sub>R(P (fst ij) (snd ij)) \<turnstile> peri\<^sub>R(P (fst ij) (snd ij)) \<diamondop> post\<^sub>R(P (fst ij) (snd ij))))"
    by (simp add: ExtChoice_tri_rdes' 1 2 closure unrest)
  also have "... = (\<box> (i, j)\<in>I \<times> J. \<^bold>R\<^sub>s(pre\<^sub>R(P i j) \<turnstile> peri\<^sub>R(P i j) \<diamondop> post\<^sub>R(P i j)))"
    by (simp add: case_prod_beta')
  also have "... = (\<box> (i, j)\<in>I \<times> J. P i j)"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))
  finally show ?thesis .
next
  case False
  have "I = {} \<or> J = {}" using False by simp

  {assume "I = {}"
    have 1:"(\<box> i\<in>I. EXTCHOICE J (P i)) = Stop"
      using assms
      by (simp add: ExtChoice_empty \<open>I = {}\<close>) 
    have 2:"(\<box> (i, j)\<in>I \<times> J. P i j) = Stop"
      using assms
      by (simp add: ExtChoice_empty \<open>I = {}\<close>)

    have 3: "(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)"
      using 1 2 by argo
  }

  {assume "J = {}"
    have test:"(\<box> i\<in>I. Stop) = Stop"
      by (metis ExtChoice_const ExtChoice_empty NCSP_Stop)
      

    have 1:"(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> i\<in>I. Stop)"
      using assms
      by (simp add: ExtChoice_empty \<open>J = {}\<close>)
      
    have 2:"(\<box> (i, j)\<in>I \<times> J. P i j) = Stop"
      using assms
      by (simp add: ExtChoice_empty \<open>J = {}\<close>)

    have 3: "(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)"
      using 1 2 test by simp
  }

  then show ?thesis
    using \<open>I = {} \<Longrightarrow> (\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)\<close>
      \<open>I = {} \<or> J = {}\<close> by argo 
qed 


lemma intern_extern_distribute:
  assumes "I \<noteq> {}" "\<And> i. P i is NCSP" "Q is NCSP"
  shows "(\<box> i\<in>I. (P i)) \<sqinter> Q = 
          (\<box> i\<in>I. (P i) \<sqinter> Q)"
proof - 
  have "(\<box> i\<in>I. (P i)) = (\<box> i\<in>I. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i))))"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design
        assms(2))
        
  have "... = 
(\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i))))"
    by (simp add: ExtChoice_tri_rdes' assms(1) ok'_pre_unrest)

  have "Q = \<^bold>R\<^sub>s( pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using assms by (simp add: NCSP_implies_CSP SRD_reactive_tri_design)

  have "(\<box> i\<in>I. (P i)) \<sqinter> Q = (\<box> i\<in>I. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i)))) 
      \<sqinter> \<^bold>R\<^sub>s( pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using
      \<open>EXTCHOICE I P = (\<box> i\<in>I. \<^bold>R\<^sub>s (pre\<^sub>R (P i) \<turnstile> peri\<^sub>R (P i) \<diamondop> post\<^sub>R (P i)))\<close>
      \<open>Q = \<^bold>R\<^sub>s (pre\<^sub>R Q \<turnstile> peri\<^sub>R Q \<diamondop> post\<^sub>R Q)\<close> by argo

  also have "... = 
    (\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i)))) 
      \<sqinter> \<^bold>R\<^sub>s( pre\<^sub>R(Q) \<turnstile> peri\<^sub>R(Q) \<diamondop> post\<^sub>R(Q))"
    using
      \<open>(\<box> i\<in>I. \<^bold>R\<^sub>s (pre\<^sub>R (P i) \<turnstile> peri\<^sub>R (P i) \<diamondop> post\<^sub>R (P i))) = \<^bold>R\<^sub>s ((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile> ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or> (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop> (\<Sqinter>i\<in>I. post\<^sub>R (P i)))\<close>
    by argo

  also have "... = 
     \<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<and> pre\<^sub>R(Q)) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<or> peri\<^sub>R(Q)) \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i)) \<or> post\<^sub>R(Q)))"
    by (meson RHS_tri_design_choice)

    also have "... = 
     \<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i) \<and> pre\<^sub>R(Q))) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<or> peri\<^sub>R(Q)) \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i)) \<or> post\<^sub>R(Q)))"
      by (simp add: INF_inf_const2 assms(1) conj_pred_def)

      also have "... = 
     \<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i) \<and> pre\<^sub>R(Q))) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<or> peri\<^sub>R(Q)) \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i) \<or> post\<^sub>R(Q))))"
        by (simp add: assms(1) disj_pred_def
            ref_lattice.INF_inf_const2)

        also have "... = 
     \<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i) \<and> pre\<^sub>R(Q))) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i) \<or> peri\<^sub>R(Q))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i) \<or> peri\<^sub>R(Q)))) ) \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i) \<or> post\<^sub>R(Q))))"
          by rdes_eq

        also have "... = 
        \<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R((P i) \<sqinter> Q))) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R((P i) \<sqinter> (Q)))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R((P i) \<sqinter> (Q)))) )) \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R((P i) \<sqinter> (Q)))))"
          by rdes_eq

        
            
        also have "... = 
        (\<box> i\<in>I. \<^bold>R\<^sub>s(((pre\<^sub>R((P i) \<sqinter> Q))) \<turnstile>
            (peri\<^sub>R((P i) \<sqinter> Q)) \<diamondop>
            (post\<^sub>R((P i) \<sqinter> Q))))"
          by (simp add: ExtChoice_tri_rdes' assms(1) ok'_pre_unrest)

        also have "... = 
            (\<box> i\<in>I. P i \<sqinter> Q)"
          by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(2,3)
              srdes_theory.meet_is_healthy)

        finally show ?thesis .
      qed


      term "((\<Squnion>i\<in>A. cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i)))
              \<triangleleft> $tr\<^sup>> = $tr\<^sup>< \<and> $wait\<^sup>> \<triangleright>
             (\<Sqinter>i\<in>A. cmt\<^sub>R (\<^bold>R\<^sub>s (P i \<turnstile> Q i))))"

find_theorems expr_if sup 
find_theorems useq extChoice
find_theorems useq EXTCHOICE
find_theorems useq AssumeR
(*?P ;; ?Q \<box> ?R = (?P ;; ?Q) \<box> (?P ;; ?R)*)
(*utp_rdes_prog.AssumeR_gcomm
[?b]\<^sup>\<top>\<^sub>R ;; ?c \<rightarrow>\<^sub>R ?P = (?b \<and> ?c) \<rightarrow>\<^sub>R ?P
*)

find_theorems GuardedCommR extChoice
find_theorems expr_if Miracle


find_theorems extChoice

thm extChoice_alt_def

(*declare [[pretty_print_exprs=false]]*)

lemma extChoice_alt_def':
  assumes "a \<noteq> b"
  shows "P \<box> Q = (\<box>i\<in>{a,b}. P \<triangleleft> \<guillemotleft>i = a\<guillemotright> \<triangleright> Q)"
  using assms by (simp add: extChoice_def ExtChoice_def)


lemma extChoice_alt_def'':
  assumes "a \<noteq> b"
  shows "P \<box> Q = (\<box>i\<in>{a,b}. P \<triangleleft> \<guillemotleft>i = a\<guillemotright> \<triangleright>\<^sub>R Q)" 
  unfolding lift_cond_srea_def
  sorry
(*
proof -
  have "(\<box>i\<in>{a,b}. P \<triangleleft> \<guillemotleft>i = a\<guillemotright> \<triangleright>\<^sub>R Q) =
         (expr_if P (\<lceil>[[[\<lambda>\<s>. i = a]\<^sub>e]\<^sub>e \<up> fst\<^sub>L]\<^sub>e\<rceil>\<^sub>S) Q)"
    unfolding lift_cond_srea_def by simp
  *)
  

thm RD_elim

(*lemma "(\<Squnion>i\<in>I. P(i)) \<triangleleft> b \<triangleright>\<^sub>R Q = (\<Squnion>i\<in>I. P(i) \<triangleleft> b \<triangleright>\<^sub>R Q)"
  sorry
lemma assumptionDistribute:
  assumes "I \<noteq> {}" "\<And> i. P i is NCSP"
  shows "(b \<rightarrow>\<^sub>R (\<box> i\<in>I. (P i))) = ((\<box> i\<in>I. b \<rightarrow>\<^sub>R (P i)))"
proof - 
  have "(b \<rightarrow>\<^sub>R (\<box> i\<in>I. (P i))) = (\<box> i\<in>I. (P i)) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    unfolding gcmd_def by simp

  also have "... = (\<box> i\<in>I. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i)))) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(2))

  also have "... = (\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    by (simp add: ExtChoice_tri_rdes' assms(1) ok'_pre_unrest)

   also have "... = (\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> false)"
     by (simp add: Miracle_tri_def)

   also have "... = (\<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<triangleleft> b \<triangleright>\<^sub>R true\<^sub>r) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R false)  \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i)) \<triangleleft> b \<triangleright>\<^sub>R false)))"
     by (simp add: cond_srea_form)

   also have "... = 
\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (b \<rightarrow>\<^sub>R P i)) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i)))))  \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (b \<rightarrow>\<^sub>R P i))))"
     apply (simp add: rdes assms)
     apply (rule_tac srdes_tri_eq_intro)
     apply pred_auto
     sorry
  
  apply (insert assms(2))
  apply (erule RD_elim)
  
  apply (rdes_eq_split cls: assms(2-3) simps:assms(1))
  sorry*)
(*
proof - 
  have "(b \<rightarrow>\<^sub>R (\<box> i\<in>I. (P i))) = (\<box> i\<in>I. (P i)) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    unfolding gcmd_def by simp

  also have "... = (\<box> i\<in>I. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i)))) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(2))

  also have "... = (\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R Miracle"
    by (simp add: ExtChoice_tri_rdes' assms(1) ok'_pre_unrest)

   also have "... = (\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>I. post\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R \<^bold>R\<^sub>s(true\<^sub>r \<turnstile> false \<diamondop> false)"
     by (simp add: Miracle_tri_def)

   also have "... = (\<^bold>R\<^sub>s(((\<Squnion>i\<in>I. pre\<^sub>R (P i)) \<triangleleft> b \<triangleright>\<^sub>R true\<^sub>r) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (P i)))) \<triangleleft> b \<triangleright>\<^sub>R false)  \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (P i)) \<triangleleft> b \<triangleright>\<^sub>R false)))"
     by (simp add: cond_srea_form)

   also have "... = 
\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (b \<rightarrow>\<^sub>R P i)) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i)))))  \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (b \<rightarrow>\<^sub>R P i))))"
     sorry

   (*End of the proof: *)
   have "\<^bold>R\<^sub>s((\<Squnion>i\<in>I. pre\<^sub>R (b \<rightarrow>\<^sub>R P i)) \<turnstile>
      (((\<Squnion>i\<in>I. R5 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i))) \<or>
       (\<Sqinter>i\<in>I. R4 (peri\<^sub>R (b \<rightarrow>\<^sub>R P i)))))  \<diamondop>
      ((\<Sqinter>i\<in>I. post\<^sub>R (b \<rightarrow>\<^sub>R P i)))) =
      (\<box> i\<in>I. \<^bold>R\<^sub>s((pre\<^sub>R (b \<rightarrow>\<^sub>R P i)) \<turnstile> (peri\<^sub>R (b \<rightarrow>\<^sub>R P i)) \<diamondop> (post\<^sub>R (b \<rightarrow>\<^sub>R P i))))"
     by (simp add: ExtChoice_tri_rdes' assms(1) ok'_pre_unrest)

   have "... =  
        ((\<box> i\<in>I. b \<rightarrow>\<^sub>R (P i)))"
     by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(2) gcmd_SRD)

  



    
*)
  


    
  

term "ucond"

find_theorems "(\<box>)" "(;;)"

find_theorems "?P \<sqinter> (?Q ;; ?R)"

find_theorems ICSP R5

lemma periR_ICSP [rdes]:
  assumes "P is ICSP" 
  shows "peri\<^sub>R(P) = (\<not>\<^sub>r pre\<^sub>R(P))"
  apply (insert assms)
  apply (erule RD_elim)
  apply (simp add: rdes assms closure)
  done

find_theorems AssumeR

thm AssumeR_rdes_def

lemma ExtChoice_seq_distl:
  assumes "I \<noteq> {}" "\<And> i. Q i is NCSP"
  shows "AssumeR b ;; (\<box> i\<in>I. (Q i)) = (\<box> i\<in>I. (AssumeR b ;; Q i))"
proof -
  have "AssumeR b ;; (\<box> i\<in>I. (Q i)) = \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> false\<^sub>h \<diamondop> [b]\<^sup>\<top>\<^sub>r) ;; (\<box> i\<in>I. (\<^bold>R\<^sub>s( pre\<^sub>R(Q(i)) \<turnstile> peri\<^sub>R(Q(i)) \<diamondop> post\<^sub>R(Q(i)))))"
    by (metis (lifting) AssumeR_rdes_def ExtChoice_cong NCSP_implies_CSP
        SRD_reactive_tri_design assms(2))
  also have "... =  (\<box> i\<in>I. \<^bold>R\<^sub>s (true\<^sub>r \<turnstile> false\<^sub>h \<diamondop> [b]\<^sup>\<top>\<^sub>r) ;; (\<^bold>R\<^sub>s(pre\<^sub>R(Q(i)) \<turnstile> peri\<^sub>R(Q(i)) \<diamondop> post\<^sub>R(Q(i)))))"
    apply (simp add: rdes_def closure unrest wp rpred rdes assms seq_SUP_distl seqr_or_distr)
    apply (rule srdes_tri_eq_intro)
      apply pred_auto
    apply pred_simp
    using assms(1) apply blast
    apply pred_simp
    done
  finally show ?thesis
    by (metis (no_types, lifting) AssumeR_rdes_def ExtChoice_cong
        NCSP_implies_CSP SRD_reactive_tri_design assms(2))
qed

(*
lemma ExtChoice_seq_distl:
  assumes "I \<noteq> {}" "P is ICSP" "\<And> i. Q i is NCSP"
  shows "P ;; (\<box> i\<in>I. (Q i)) = (\<box> i\<in>I. (P ;; Q i))"
proof -
  have "P ;; (\<box> i\<in>I. (Q i)) = \<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;; (\<box> i\<in>I. (\<^bold>R\<^sub>s( pre\<^sub>R(Q(i)) \<turnstile> peri\<^sub>R(Q(i)) \<diamondop> post\<^sub>R(Q(i)))))"
    by (metis (no_types, lifting) ExtChoice_cong ICSP_implies_NCSP
        NCSP_implies_CSP SRD_reactive_tri_design assms(2,3))
  also have "... = \<^bold>R\<^sub>s
     ((pre\<^sub>R P \<and> post\<^sub>R P wp\<^sub>r (\<Squnion>x\<in>I. pre\<^sub>R (Q x))) \<turnstile>
      (peri\<^sub>R P \<or>
       post\<^sub>R P ;;
       ((\<Squnion>x\<in>I. R5 (peri\<^sub>R (Q x))) \<or> (\<Sqinter>x\<in>I. R4 (peri\<^sub>R (Q x))))) \<diamondop>
      (post\<^sub>R P ;; (\<Sqinter>x\<in>I. post\<^sub>R (Q x))))"
    by (simp add: rdes_def closure unrest assms)
  also from assms(1) have "... =  (\<box> i\<in>I. (\<^bold>R\<^sub>s(pre\<^sub>R(P) \<turnstile> peri\<^sub>R(P) \<diamondop> post\<^sub>R(P)) ;;  \<^bold>R\<^sub>s( pre\<^sub>R(Q(i)) \<turnstile> peri\<^sub>R(Q(i)) \<diamondop> post\<^sub>R(Q(i)))))"
    apply (simp add: rdes_def closure unrest wp rpred rdes assms(2-3) seq_SUP_distl seqr_or_distr)
    apply (rule srdes_tri_eq_intro)
      apply pred_auto
    apply pred_simp
    defer
apply pred_simp

  also have "... = (\<box> i\<in>I. (P ;; Q i))"
    by (metis (mono_tags, lifting) ICSP_implies_NCSP NCSP_implies_CSP
        SRD_reactive_tri_design assms(2,3))
*)

term "(\<box> i\<in>I. (P i)) \<triangleleft> tr\<^sup>< = 0 \<triangleright>\<^sub>R Q"

term "\<lceil>b\<rceil>\<^sub>S\<^sub><"

lemma cond_distrib:
  assumes "I \<noteq> {}" "\<And> i. P i is NCSP" "Q is NCSP"
  shows "(\<box> i\<in>I. (P i)) \<triangleleft> b \<triangleright>\<^sub>R Q = 
          (\<box> i\<in>I. (P i) \<triangleleft> b \<triangleright>\<^sub>R Q)"

proof - 
  have "(\<box> i\<in>I. (P i)) \<triangleleft> b \<triangleright>\<^sub>R Q = (((AssumeR(b)) ;; (\<box> i\<in>I. (P i))) \<sqinter> ((AssumeR(\<not> b)) ;; Q))"
    by (simp add: NCSP_ExtChoice NCSP_implies_NSRD assms(2,3) cond_srea_AssumeR_form)


  also have "... = 
    (((\<box> i\<in>I. (AssumeR(b)) ;; (P i))) \<sqinter> ((AssumeR(\<not> b)) ;; Q))"
    by (simp add: ExtChoice_seq_distl assms(1,2))

also have "... = 
    (((\<box> i\<in>I. ((AssumeR(b)) ;; (P i)) \<sqinter> ((AssumeR(\<not> b)) ;; Q))))"
  by (smt (verit) AssumeR_as_gcmd ExtChoice_cong GuardedCommR_NCSP_closed
      NCSP_implies_NSRD assms(1,2,3) gcmd_seq_distr intern_extern_distribute
      nsrdes_theory.Unit_Left)

  also have "... = 
      (\<box> i\<in>I. (P i) \<triangleleft> b \<triangleright>\<^sub>R Q)"
    by (simp add: NCSP_implies_NSRD assms(2,3) cond_srea_AssumeR_form)

  finally show ?thesis .
 qed


  find_theorems "extChoice"

(*Relating reactive |> to normal UTP |> *)

  term "P \<triangleleft> (lift_cond_srea (e)\<^sub>e) \<triangleright> Q"

  term "lift_cond_srea (e)\<^sub>e"

(*declare [[show_types]]*)
find_theorems expr_if

consts n::nat

definition f :: "bool \<times> nat \<Rightarrow> nat" where 
"f x = (if fst x then snd x else n + snd x)"

definition g :: "nat \<Rightarrow> bool \<times> nat" where 
"g x = (if (x \<ge> n) then (False,x) else (True,x))"

lemma "inv f = g"

term "{(i::bool,x). x \<in> {0..n}}"



lemma
  fixes n :: nat
  assumes "\<And> i. P i is NCSP"
  shows  "(\<box> i\<in>{n}. P(i)) = P(n)"
  by (metis ExtChoice_cong ExtChoice_const assms insert_not_empty
      singletonD)

term "(\<box> i\<in>I. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i))))"

find_theorems "extChoice"
lemma 
  assumes "P is NCSP" "Q is NCSP"  
  shows  "P \<box> Q =  \<^bold>R\<^sub>s
     ((pre\<^sub>R(P) \<and> pre\<^sub>R(Q)) \<turnstile>
      (R5 (peri\<^sub>R(P) \<and> peri\<^sub>R(Q)) \<or> R4 (peri\<^sub>R(P) \<or> peri\<^sub>R(Q))) \<diamondop> (post\<^sub>R(P) \<or> post\<^sub>R(Q)))"
  apply (insert assms)
  apply (erule RD_elim)+
  by (metis NCSP_implies_CSP NCSP_implies_NSRD SRD_reactive_tri_design
      assms(1,2) extChoice_rdes_def' preR_RR)
  


lemma 
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" 
  shows "(\<Squnion>i\<in>S\<^sub>1 \<union> S\<^sub>2. P(i)) = 
        (\<Squnion>i\<in>S\<^sub>1. P(i)) \<squnion> (\<Squnion>i\<in>S\<^sub>2. P(i))"
  by (simp add:Complete_Lattices.complete_lattice_class.INF_union)

lemma 
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" 
shows "(\<Squnion>i\<in>S\<^sub>1 \<union> S\<^sub>2. pre\<^sub>R (P i)) = 
(\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<squnion> (\<Squnion>i\<in>S\<^sub>2. pre\<^sub>R (P i))"
  by (meson INF_union)

lemma 
  fixes S ::"nat set"
  assumes "\<And> i. P i is NCSP" "S \<noteq> {}"
  shows "pre\<^sub>R((\<box> i\<in>S. P(i))) = (\<Squnion>i\<in>S. pre\<^sub>R(P(i)))"
  by (simp add: assms(1,2) preR_EXTCHOICE)
  

find_theorems "peri\<^sub>R" "R5"

(*Pericondition lemmas for distributed external choice*)
find_theorems "peri\<^sub>R"
find_theorems "pre\<^sub>R" "NCSP"
term "npre\<^sub>R"
find_theorems "R4"

lemma r5_peri_dist1:
  fixes S
  assumes "\<And> i. P i is NCSP" "S \<noteq> {}"
  shows "(\<Squnion>i\<in>S. R5 (peri\<^sub>R (P(i)))) = R5 (peri\<^sub>R((\<box> i\<in>S. P(i))))"

proof - 
  (*LHS:*)
  have "(\<Squnion>i\<in>S. R5 (peri\<^sub>R (P(i)))) = (R5(\<Squnion>i\<in>S. (peri\<^sub>R (P(i)))))"
    by (simp add: R5_USUP assms)

  have "... = (R5(\<Squnion>i\<in>S. (pre\<^sub>R(P(i)) \<longrightarrow>\<^sub>r peri\<^sub>R (P(i)))))"
    by (simp add: NCSP_implies_NSRD NSRD_peri_under_pre assms)


  (*RHS:*)
  have "R5(peri\<^sub>R((\<box> i\<in>S. P(i)))) =
        R5((R5((\<Squnion> i\<in>S. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S. peri\<^sub>R (P(i)))))"
    by (simp add: assms(1,2) periR_ExtChoice')

  have"... =
      (R5((\<Squnion> i\<in>S. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r ((\<Squnion> i\<in>S. peri\<^sub>R (P(i))))))"
    by (simp add: R5_R4 R5_disj R5_idem)

  have "... =
      (R5(\<Squnion>i\<in>S. (pre\<^sub>R(P(i)) \<longrightarrow>\<^sub>r peri\<^sub>R (P(i)))))"
  
  

find_theorems "peri\<^sub>R" "Inf"
(*R5 Case*)
lemma R5_dist_peri: 
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" "Q is NCSP"
  shows "((\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P i))))
      = R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i))))"

proof -
(*Additional lemmas*)
  have "peri\<^sub>R(Q) = (pre\<^sub>R(Q) \<longrightarrow>\<^sub>r peri\<^sub>R(Q))"
    by (simp add: NCSP_implies_NSRD NSRD_peri_under_pre assms(4))

  have "(\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P(i)))) = ( R5(\<Squnion>i\<in>S\<^sub>1. (peri\<^sub>R (P(i)))))"
    by (simp add: R5_USUP assms(2))

  have "(((\<Squnion>i\<in>S\<^sub>1. (peri\<^sub>R (P(i))))) \<sqinter> ((\<Squnion>i\<in>S\<^sub>1. (peri\<^sub>R (P(i))))))
       = (\<Squnion>i\<in>S\<^sub>1.((( (peri\<^sub>R (P(i))))) \<sqinter> ((peri\<^sub>R (P(i))))))"
    by auto

  have "(((\<Squnion>i\<in>S\<^sub>1. (\<not>\<^sub>rpre\<^sub>R (P(i))))) \<or> ((\<Squnion>i\<in>S\<^sub>1. (peri\<^sub>R (P(i))))))
       = (\<Squnion>i\<in>S\<^sub>1.(peri\<^sub>R(P(i))))"
  
    
(*Starting from RHS: *)
  (*have "R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) = undefined"
    sorry*)
    
  have "R5(peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i)))) =
        R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))"
    by (simp add: assms(1,2) periR_ExtChoice')

  have "... = 
      (R5(R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r ((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))) \<or> R5(R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))"
    by (simp add: R5_disj)

  have "... = 
      (R5(R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r ((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))) \<or> false)"
    by (simp add: R5_R4)

  have "... = 
      (R5(R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r ((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))))"
    by simp

  have "... = 
      (R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r ((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))))"
    by (simp add: R5_idem)

    finally show ?thesis sorry

  qed

  

 
  
    
    
    

  
lemma templemma:
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" 
  shows  "(\<box> i\<in>S\<^sub>1 \<union> S\<^sub>2 . P(i)) = (\<box> i\<in>S\<^sub>1. P(i)) \<box> (\<box> i\<in>S\<^sub>2. P(i))"
  sorry
(*
proof -
  (*RHS*)
  have " 
    (\<box> i\<in>S\<^sub>1. P(i)) \<box> (\<box> i\<in>S\<^sub>2. P(i))
    = 
    \<^bold>R\<^sub>s
     ((pre\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> pre\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) \<turnstile>
      (R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) \<or> R4 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i))))) \<diamondop> (post\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> post\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))))"
    by (metis CSP_ExtChoice NCSP_ExtChoice NCSP_implies_NSRD
        SRD_reactive_tri_design assms(1) extChoice_rdes_def' preR_RR)

  
  
  (*LHS: *)
  have "(\<box> i\<in>S\<^sub>1 \<union> S\<^sub>2. P(i)) = 
    (\<box> i\<in>S\<^sub>1 \<union> S\<^sub>2. \<^bold>R\<^sub>s( pre\<^sub>R(P(i)) \<turnstile> peri\<^sub>R(P(i)) \<diamondop> post\<^sub>R(P(i))))"
    by (simp add: NCSP_implies_CSP SRD_reactive_tri_design assms(1))

    have "... = \<^bold>R\<^sub>s
     ((\<Squnion>i\<in>S\<^sub>1 \<union> S\<^sub>2. pre\<^sub>R (P i)) \<turnstile>
      ((\<Squnion>i\<in>S\<^sub>1 \<union> S\<^sub>2. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>S\<^sub>1 \<union> S\<^sub>2. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>S\<^sub>1 \<union> S\<^sub>2. post\<^sub>R (P i)))"
      by (simp add: ExtChoice_tri_rdes' assms closure unrest)

   have "... = \<^bold>R\<^sub>s
     (((\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<and> (\<Squnion>i\<in>S\<^sub>2. pre\<^sub>R (P i))) \<turnstile>
      ((\<Squnion>i\<in>S\<^sub>1 \<union> S\<^sub>2. R5 (peri\<^sub>R (P i))) \<or>
       (\<Sqinter>i\<in>S\<^sub>1 \<union> S\<^sub>2. R4 (peri\<^sub>R (P i)))) \<diamondop>
      (\<Sqinter>i\<in>S\<^sub>1 \<union> S\<^sub>2. post\<^sub>R (P i)))"
     by (simp add: INF_union conj_pred_def)

   have "... = \<^bold>R\<^sub>s
     (((\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<and> (\<Squnion>i\<in>S\<^sub>2. pre\<^sub>R (P i))) \<turnstile>
      (( (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P i))) ) \<or>
       ( (\<Sqinter>i\<in>S\<^sub>1. R4 (peri\<^sub>R (P i))) \<or> (\<Sqinter>i\<in>S\<^sub>2. R4 (peri\<^sub>R (P i))) )) \<diamondop>
      (\<Sqinter>i\<in>S\<^sub>1 \<union> S\<^sub>2. post\<^sub>R (P i)))"
     by (simp add: INF_union SUP_union conj_pred_def disj_pred_def)

  have "... = \<^bold>R\<^sub>s
     (((\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<and> (\<Squnion>i\<in>S\<^sub>2. pre\<^sub>R (P i))) \<turnstile>
      (( (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P i))) ) \<or>
       ( (\<Sqinter>i\<in>S\<^sub>1. R4 (peri\<^sub>R (P i))) \<or> (\<Sqinter>i\<in>S\<^sub>2. R4 (peri\<^sub>R (P i))) )) \<diamondop>
      ((\<Sqinter>i\<in>S\<^sub>1. post\<^sub>R (P i)) \<or> (\<Sqinter>i\<in>S\<^sub>2. post\<^sub>R (P i)) ))"
    by (simp add: INF_union SUP_union conj_pred_def disj_pred_def)

  have "... = 
    \<^bold>R\<^sub>s
     ((pre\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> pre\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) \<turnstile>
      (R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) \<or> R4 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i))))) \<diamondop> (post\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> post\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))))"
    sorry
    have "(pre\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> pre\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) =
      ((\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<and> (\<Squnion>i\<in>S\<^sub>2. pre\<^sub>R (P i)))"
      by (simp add: assms(1,2,3) preR_EXTCHOICE)

    have "((\<Sqinter>i\<in>S\<^sub>1. post\<^sub>R (P i)) \<or> (\<Sqinter>i\<in>S\<^sub>2. post\<^sub>R (P i)) ) =  (post\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> post\<^sub>R((\<box> i\<in>S\<^sub>2. P(i))))"
      by (simp add: assms(1,2,3) postR_ExtChoice)
  
    have "(( (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P i))) ) \<or>
       ( (\<Sqinter>i\<in>S\<^sub>1. R4 (peri\<^sub>R (P i))) \<or> (\<Sqinter>i\<in>S\<^sub>2. R4 (peri\<^sub>R (P i))) )) =
      
      (R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) \<or> R4 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<or> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))))" 
      sorry          
*)
 
lemma 
  assumes "\<And> i. P i is NCSP"
  shows "(\<box> i\<in>{n}. P(i)) = P(n)"
  by (metis ExtChoice_cong ExtChoice_const assms insert_not_empty singletonD)


(*  shows "(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)"*)
(*declare [[pretty_print_exprs=false]]*)
lemma "{0..n+1} = {0..n} \<union> {n+1}"
  by (metis Suc_eq_plus1 Un_insert_right atLeast0_atMost_Suc boolean_algebra.disj_zero_right)


lemma extchoice_cond_distribute:
  fixes n :: nat
  assumes "\<And> i. P i is NCSP" "Q is NCSP"
  shows "(\<box> i\<in>{0..n}. (P i)) \<box> Q = 
          (\<box> i\<in>{0..(n+1)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q))"
proof 
    have "(\<box> i\<in>{0..(n+1)}. (P(i))) = 
      (\<box> i\<in>{0..(n)}. (P(i))) \<box>
      (\<box> i\<in>{n+1}. (P(i)))"
      using assms apply (simp add: templemma)
      by (metis Un_insert_right atLeast0_atMost_Suc atLeastatMost_empty_iff bot_nat_0.extremum
          insert_not_empty sup_bot.right_neutral templemma)

  have "(\<box> i\<in>{0..(n+1)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) = 
      (\<box> i\<in>{0..(n)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (\<box> i\<in>{n+1}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q))"
    by (metis (no_types, lifting) NCSP_cond_srea Suc_eq_plus1 Un_insert_right assms(1,2)
        atLeast0_atMost_Suc atLeastatMost_empty_iff2 empty_not_insert sup_bot.right_neutral templemma
        zero_le)

  also have "... = 
      (\<box> i\<in>{0..(n)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (P(n+1) \<triangleleft> (\<guillemotleft>n+1 \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)"
    sorry

  also have "... = 
      (\<box> i\<in>{0..n}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (Q)"
    by (simp add: cond_st_false)  
    

  also have "... = 
      (\<box> i\<in>{0..n}. P(i)) \<box> Q"  
    by (metis Suc_eq_plus1 atLeastatMost_empty atLeastatMost_empty_iff2 cond_st_false
        lessI)

  finally show ?thesis .
qed
  
    


(*
Old Proof: 
proof -
  have "(\<box> i\<in>{0..n}. (P i)) \<box> Q = 
        (\<box>i0::nat \<in>{n,n+1}. (\<box> i\<in>{0..n}. (P i)) \<triangleleft> \<guillemotleft>i0\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q)"
    apply (simp add: extChoice_alt_def')
    sorry
  also have "... = 
        (\<box>i0::nat \<in>{n,n+1}. (\<box> i\<in>{0..n}. (P i) \<triangleleft> \<guillemotleft>i0\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q))"
    by (simp add: assms(1,2) cond_distrib)  

  also have "... = 
        (\<box>i0::nat \<in>{n,n+1}. (EXTCHOICE {0::nat..n} (\<lambda> i::nat. ((P i) \<triangleleft> \<guillemotleft>i0\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q))))"
    by force
  also have "... = (\<box>(i0::nat,i::nat) \<in> {n,n+1} \<times> {0..n}. (P i) \<triangleleft> \<guillemotleft>i0\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q)"
    sorry

  also have "... = 
    (\<box>(i0::nat,i::nat) \<in> {n,n+1} \<times> {0..n}. 
      (P i) \<triangleleft> \<guillemotleft>i0\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q)"
    sorry
  also have "... = (\<box> i\<in>{0..(n+1)}. (P(i) \<triangleleft> (\<guillemotleft>i\<guillemotright> \<le> \<guillemotleft>n\<guillemotright>) \<triangleright>\<^sub>R Q))"
  proof -
    {have "(\<box>(i::nat) \<in> {0..n}. (P i) \<triangleleft> \<guillemotleft>n\<guillemotright> = \<guillemotleft>n\<guillemotright> \<triangleright>\<^sub>R Q) = 
          (\<box>(i::nat) \<in> {0..n}. (P i))"
        by (simp add: cond_st_true)
      also have "(\<box>(i::nat) \<in> {0..n}. (P i)) = 
                  (\<box>(i::nat) \<in> {0..n}. (P(i) \<triangleleft> (\<guillemotleft>i\<guillemotright> \<le> \<guillemotleft>n\<guillemotright>) \<triangleright>\<^sub>R Q))"
        sorry
          
        }
    
  show ?thesis 
    sorry
qed
*)

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