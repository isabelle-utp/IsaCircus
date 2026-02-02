theory Ziggy_Laws
  imports "UTP-Stateful-Failure.utp_sf_rdes" (* "Interaction_Trees.ITrees" *)
begin
 
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

lemma R4_seq_R4_right: "R4(R5(P) ;; Q) = R5(P) ;; R4(Q)"
  by pred_auto

find_theorems Injective

lemma ExtChoice_seq_distl:
  assumes "I \<noteq> {}" "P is ICSP" "\<And> i. Q i is NCSP"
  shows "P ;; (\<box> i\<in>I. (Q i)) = (\<box> i\<in>I. (P ;; Q i))"
  apply (rdes_eq_split cls:assms(2-3) simps:assms(1))
    apply (simp_all add: assms(1) conj_INF_dist R4_seq_R4_right)
  apply pred_auto
  


lemma ExtChoice_seq_distl:
  assumes "I \<noteq> {}" "\<And> i. Q i is NCSP"
  shows "AssumeR b ;; (\<box> i\<in>I. (Q i)) = (\<box> i\<in>I. (AssumeR b ;; Q i))"
  apply (rdes_eq cls:assms(2) simps:assms(1))
  using assms(1) apply blast+
  done
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

lemma peri_eq:
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" 
  shows "(\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))) = 
(\<Squnion> i\<in>S\<^sub>1. (R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))
"
  sorry


(*R5 Case*)     
lemma R5_dist_peri: 
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" 
  shows "((\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P i))))
      = R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i))))"

proof -
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

  have "... = 
    R5(\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<or> ((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))))"
    by (simp add: rea_impl_def)

  have "... = 
    (R5(\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i)))) \<or> R5(((\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))))"
    by (meson R5_disj)

  have "... = 
    ((((\<Squnion> i\<in>S\<^sub>1. R5(peri\<^sub>R (P(i))) \<or> R5(\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i))))))))"
  proof -
    have "\<And>p pa. ((p::('b, 'a) action) \<or> pa) = pa \<sqinter> p"
      by (smt (z3) disj_pred_def pred_ba.sup_commute)
    then show ?thesis
      by (simp add: INF_sup R5_USUP assms(2) disj_pred_def preR_UINF_member)
  qed

    have "... = 
    (\<Squnion> i\<in>S\<^sub>1. R5(peri\<^sub>R (P(i)) \<or> (\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i))))))"
      by (simp add: R5_disj)

    have "... = 
    (\<Squnion> i\<in>S\<^sub>1. R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or>
           (\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i))))))"
      by (metis INF_const R5_R4 R5_disj R5_idem
          \<open>(R5 (\<not>\<^sub>r (\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i))) \<or> R5 (\<Squnion>i\<in>S\<^sub>1. peri\<^sub>R (P i))) = (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i)) \<or> R5 (\<not>\<^sub>r pre\<^sub>R (\<Sqinter> (P ` S\<^sub>1))))\<close>
          \<open>(\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i)) \<or> R5 (\<not>\<^sub>r pre\<^sub>R (\<Sqinter> (P ` S\<^sub>1)))) = (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i) \<or> \<not>\<^sub>r pre\<^sub>R (\<Sqinter> (P ` S\<^sub>1))))\<close>
          assms(2) preR_UINF_member pred_ba.boolean_algebra.disj_zero_right pred_ba.sup_idem
          pred_ba.sup_left_commute rea_impl_disj rea_impl_false)
      
    have "... = 
      (\<Squnion> i\<in>S\<^sub>1. R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> (\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      by (simp add: pred_ba.sup.assoc pred_ba.sup_commute)

    have "... = 
      (\<Squnion> i\<in>S\<^sub>1. R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))) \<or> (\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i))))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      by (simp add: R5_disj R5_idem pred_ba.sup.assoc rea_impl_def)

    have "... =
      (\<Squnion> i\<in>S\<^sub>1. R5((R5(\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<or> (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))) \<or> (\<not>\<^sub>r (pre\<^sub>R (\<Sqinter> i\<in>S\<^sub>1. P(i))))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      by (simp add: rea_impl_def)

  
    have "... =
      (\<Squnion> i\<in>S\<^sub>1. R5((R5(\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<or> (\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1.(pre\<^sub>R (P(i))))) \<or> (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))) ) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      by (smt (verit, ccfv_SIG) Sup.SUP_cong assms(2) preR_UINF_member pred_ba.sup_commute)

    
    have "... =
      (\<Squnion> i\<in>S\<^sub>1. R5((R5(\<not>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<or> (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i))) ) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      by force

  
    have "... =
       (\<Squnion> i\<in>S\<^sub>1. R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r  (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))
           ))"
      using
        \<open>R5 ((\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<longrightarrow>\<^sub>r (\<Squnion>i\<in>S\<^sub>1. peri\<^sub>R (P i))) = R5 (\<not>\<^sub>r (\<Squnion>i\<in>S\<^sub>1. pre\<^sub>R (P i)) \<or> (\<Squnion>i\<in>S\<^sub>1. peri\<^sub>R (P i)))\<close>
      by presburger

    have "... = 

        (\<Squnion> i\<in>S\<^sub>1. R5((R5((\<Squnion> i\<in>S\<^sub>1. pre\<^sub>R (P(i))) \<longrightarrow>\<^sub>r (\<Squnion> i\<in>S\<^sub>1. peri\<^sub>R (P(i)))) \<or> R4(\<Sqinter> i\<in>S\<^sub>1. peri\<^sub>R (P(i))))))"
      by force
    
    have "... = 
      (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P(i))))"
      apply (subst peri_eq)
        apply (simp add: assms)
      apply (simp add: assms)
      by (metis (no_types) INF_const R5_USUP assms(1,2) peri_eq)
    


    have "R5(peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i)))) = (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P(i))))"
      sorry

    have "R5 (peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i))) \<and> peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))) = 
        (R5(peri\<^sub>R((\<box> i\<in>S\<^sub>1. P(i)))) \<and> R5(peri\<^sub>R((\<box> i\<in>S\<^sub>2. P(i)))))"
      by (simp add: R5_conj)

    also have "... = 
        ((\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P(i)))) \<and> (\<Squnion>i\<in>S\<^sub>2. R5 (peri\<^sub>R (P(i)))))"
      by (metis R5_USUP \<open>R5 (peri\<^sub>R (EXTCHOICE S\<^sub>1 P)) = (\<Squnion>i\<in>S\<^sub>1. R5 (peri\<^sub>R (P i)))\<close> assms(1,3)
          periR_ExtChoice' peri_eq ref_lattice.SUP_eq_const)

    

    finally show ?thesis sorry

  qed

  

 
  
    
    
    

  
lemma 
  fixes S\<^sub>1 S\<^sub>2::"nat set"
  assumes "\<And> i. P i is NCSP" "S\<^sub>1 \<noteq> {}" "S\<^sub>2 \<noteq> {}" 
  shows  "(\<box> i\<in>S\<^sub>1 \<union> S\<^sub>2 . P(i)) = (\<box> i\<in>S\<^sub>1. P(i)) \<box> (\<box> i\<in>S\<^sub>2. P(i))"
  sorry
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

 

(*  shows "(\<box> i\<in>I. EXTCHOICE J (P i)) = (\<box> (i, j)\<in>I \<times> J. P i j)"*)
declare [[pretty_print_exprs=false]]

lemma
  fixes n :: nat
  assumes "\<And> i. P i is NCSP" "Q is NCSP"
  shows "(\<box> i\<in>{0..n}. (P i)) \<box> Q = 
          (\<box> i\<in>{0..(n+1)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q))"
proof 
  have "(\<box> i\<in>{n+1}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) = 
      (P(n+1) \<triangleleft> (\<guillemotleft>n+1 \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)"
    by (metis ExtChoice_cong ExtChoice_const NCSP_cond_srea assms(1,2)
        empty_iff insertE insert_not_empty)
    
  have "(\<box> i\<in>{0..(n+1)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) = 
      (\<box> i\<in>{0..(n)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (\<box> i\<in>{n+1}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q))"
    sorry

  also have "... = 
      (\<box> i\<in>{0..(n)}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (P(n+1) \<triangleleft> (\<guillemotleft>n+1 \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)"
    sorry

  also have "... = 
      (\<box> i\<in>{0..n}. (P(i) \<triangleleft> (\<guillemotleft>i \<le> n\<guillemotright>) \<triangleright>\<^sub>R Q)) \<box>
      (Q)"  
    sorry

  also have "... = 
      (\<box> i\<in>{0..n}. P(i)) \<box> Q"  
    sorry

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

end
