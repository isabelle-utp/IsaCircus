theory Circus_Renaming
  imports Circus_Hiding
begin

subsection \<open> Renaming Reactive Relations \<close>

subsection \<open> Renaming \<close>

definition csp_rename :: "('s, 'e) sfrd hrel \<Rightarrow> ('e \<leftrightarrow> 'f) \<Rightarrow> ('s, 'f) sfrd hrel" ("(_)\<lparr>_\<rparr>\<^sub>c" [999, 0] 999) where
[pred]: "P\<lparr>R\<rparr>\<^sub>c = R2(($tr\<^sup>> = [] \<and> $st\<^sup>> = $st\<^sup><)\<^sub>e 
                   ;; P 
                   ;; (list_all2 (\<lambda> x y. (x, y) \<in> \<guillemotleft>R\<guillemotright>) ($tr\<^sup><) ($tr\<^sup>>) \<and> $st\<^sup>> = $st\<^sup>< \<and> \<guillemotleft>R\<guillemotright>\<^sup>\<sim>\<lparr>$ref\<^sup>>\<rparr>  \<subseteq> ($ref\<^sup><))\<^sub>e)"


lemma csp_rename_CRR_closed [closure]: 
  assumes "P is CRR"
  shows "P\<lparr>f\<rparr>\<^sub>c is CRR"
proof -
  have "(CRR P)\<lparr>f\<rparr>\<^sub>c is CRR"
    by (pred_auto)
  thus ?thesis by (simp add: assms Healthy_if)
qed

lemma csp_rename_disj [rpred]: "(P \<or> Q)\<lparr>R\<rparr>\<^sub>c = (P\<lparr>R\<rparr>\<^sub>c \<or> Q\<lparr>R\<rparr>\<^sub>c)"
  by (pred_auto; blast)

lemma csp_rename_UINF_ind [rpred]: "(\<Sqinter> i. P i)\<lparr>R\<rparr>\<^sub>c = (\<Sqinter> i. (P i)\<lparr>R\<rparr>\<^sub>c)"
  by (pred_auto; blast)

lemma csp_rename_UINF_mem [rpred]: "(\<Sqinter> i \<in> A. P i)\<lparr>R\<rparr>\<^sub>c = (\<Sqinter> i \<in> A. (P i)\<lparr>R\<rparr>\<^sub>c)"
  by (pred_auto; blast)

text \<open> Renaming distributes through conjunction only when both sides are downward closed \<close>

(*
lemma csp_rename_conj [rpred]: 
  assumes "injective R" "P is CRR" "Q is CRR" "P is CDC" "Q is CDC"
  shows "(P \<and> Q)\<lparr>R\<rparr>\<^sub>c = (P\<lparr>R\<rparr>\<^sub>c \<and> Q\<lparr>R\<rparr>\<^sub>c)"
proof -
  from assms(1) have "((CDC (CRR P)) \<and> (CDC (CRR Q)))\<lparr>R\<rparr>\<^sub>c = ((CDC (CRR P))\<lparr>R\<rparr>\<^sub>c \<and> (CDC (CRR Q))\<lparr>R\<rparr>\<^sub>c)"
    apply (pred_auto)
    apply blast
     apply blast
    apply (auto simp add: injective_def)
    apply (meson order_refl order_trans)
    done
  thus ?thesis
    by (simp add: assms Healthy_if)
qed
*)  

lemma csp_rename_seq [rpred]:
  assumes "P is CRR" "Q is CRR"
  shows "(P ;; Q)\<lparr>f\<rparr>\<^sub>c = P\<lparr>f\<rparr>\<^sub>c ;; Q\<lparr>f\<rparr>\<^sub>c"
  oops

lemma csp_rename_R4 [rpred]:
  "(R4(P))\<lparr>R\<rparr>\<^sub>c = R4(P\<lparr>R\<rparr>\<^sub>c)"
  apply (pred_auto, blast)
  using less_le apply fastforce
  apply (metis Prefix_Order.Nil_prefix dual_order.refl less_eq_list_def list_all2_Nil minus_cancel
      order_less_le prefix_concat_minus)
  done

lemma csp_rename_R5 [rpred]:
  "(R5(P))\<lparr>f\<rparr>\<^sub>c = R5(P\<lparr>f\<rparr>\<^sub>c)"
  apply (pred_auto, blast)
  using less_le apply fastforce
  done

lemma csp_rename_do [rpred]: "\<Phi>(s,\<sigma>,t)\<lparr>f\<rparr>\<^sub>c = \<Phi>(s,\<sigma>,map \<guillemotleft>f\<guillemotright> t)"
  oops

lemma csp_rename_enable [rpred]: "\<E>(s,t,E)\<lparr>f\<rparr>\<^sub>c = \<E>(s,map \<guillemotleft>f\<guillemotright> t, image \<guillemotleft>f\<guillemotright> E)"
  oops

lemma st'_unrest_csp_rename [unrest]: "$st\<^sup>> \<sharp> P \<Longrightarrow> $st\<^sup>> \<sharp> P\<lparr>f\<rparr>\<^sub>c"
  by (pred_auto; blast)

lemma ref'_unrest_csp_rename [unrest]: "$ref\<^sup>> \<sharp> P \<Longrightarrow> $ref\<^sup>> \<sharp> P\<lparr>f\<rparr>\<^sub>c"
  by (pred_auto; blast)

lemma csp_rename_CDC_closed [closure]:
  "P is CDC \<Longrightarrow> P\<lparr>f\<rparr>\<^sub>c is CDC"
  by (pred_auto; blast)


subsection \<open> Renaming \<close>

definition RenameCSP :: "('s, 'e) sfrd hrel \<Rightarrow> ('e \<leftrightarrow> 'f) \<Rightarrow> ('s, 'f) sfrd hrel" ("(_)\<lparr>_\<rparr>\<^sub>C" [999, 0] 999) where
[pred]: "RenameCSP P R = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r pre\<^sub>R(P))\<lparr>R\<rparr>\<^sub>c ;; true\<^sub>r) \<turnstile> ((peri\<^sub>R(P))\<lparr>R\<rparr>\<^sub>c) \<diamondop> ((post\<^sub>R(P))\<lparr>R\<rparr>\<^sub>c))"

lemma RenameCSP_rdes_def [rdes_def]: 
  assumes "P is CRC" "Q is CRR" "R is CRR"
  shows "(\<^bold>R\<^sub>s(P \<turnstile> Q \<diamondop> R))\<lparr>f\<rparr>\<^sub>C = \<^bold>R\<^sub>s((\<not>\<^sub>r (\<not>\<^sub>r P)\<lparr>f\<rparr>\<^sub>c ;; true\<^sub>r) \<turnstile> Q\<lparr>f\<rparr>\<^sub>c \<diamondop> R\<lparr>f\<rparr>\<^sub>c)" (is "?lhs = ?rhs")
proof -
  have "?lhs =  \<^bold>R\<^sub>s ((\<not>\<^sub>r (\<not>\<^sub>r P)\<lparr>f\<rparr>\<^sub>c ;; true\<^sub>r) \<turnstile> (P \<longrightarrow>\<^sub>r Q)\<lparr>f\<rparr>\<^sub>c \<diamondop> (P \<longrightarrow>\<^sub>r R)\<lparr>f\<rparr>\<^sub>c)"
    by (simp add: RenameCSP_def rdes closure assms)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r (\<not>\<^sub>r CRC(P))\<lparr>f\<rparr>\<^sub>c ;; true\<^sub>r) \<turnstile> (CRC(P) \<longrightarrow>\<^sub>r CRR(Q))\<lparr>f\<rparr>\<^sub>c \<diamondop> (CRC(P) \<longrightarrow>\<^sub>r CRR(R))\<lparr>f\<rparr>\<^sub>c)"
    by (simp add: Healthy_if assms)
  also have "... = \<^bold>R\<^sub>s ((\<not>\<^sub>r (\<not>\<^sub>r CRC(P))\<lparr>f\<rparr>\<^sub>c ;; true\<^sub>r) \<turnstile> (CRR(Q))\<lparr>f\<rparr>\<^sub>c \<diamondop> (CRR(R))\<lparr>f\<rparr>\<^sub>c)"
    apply (rule srdes_tri_eq_intro)
      apply pred_simp
    apply (pred_simp, meson dual_order.refl)+
    done
  also have "... = ?rhs"
    by (simp add: Healthy_if assms)
  finally show ?thesis .
qed

lemma RenameCSP_pre_CRC_closed:
  assumes "P is CRR"
  shows "\<not>\<^sub>r (\<not>\<^sub>r P)\<lparr>f\<rparr>\<^sub>c ;; R1 true is CRC"
  apply (rule CRC_intro'')
   apply (simp add: unrest closure assms)
  apply (simp add: Healthy_def, simp add: RC1_def rpred closure CRC_idem assms seqr_assoc) 
  done
  
lemma RenameCSP_NCSP_closed [closure]:
  assumes "P is NCSP"
  shows "P\<lparr>f\<rparr>\<^sub>C is NCSP"
  by (simp add: RenameCSP_def RenameCSP_pre_CRC_closed closure assms unrest)

lemma csp_rename_false [rpred]: 
  "false\<lparr>f\<rparr>\<^sub>c = false"
  by (pred_auto)

lemma rename_Skip: "Skip\<lparr>f\<rparr>\<^sub>C = Skip"
  by (rdes_eq)

lemma rename_Chaos: "Chaos\<lparr>f\<rparr>\<^sub>C = Chaos"
  apply (rdes_eq)
  using minus_cancel apply blast
  done

lemma rename_Miracle: "Miracle\<lparr>f\<rparr>\<^sub>C = Miracle"
  by (rdes_eq)


lemma rename_DoCSP: "(do\<^sub>C(a))\<lparr>f\<rparr>\<^sub>C = do\<^sub>C(\<guillemotleft>f\<guillemotright> a)"
  oops

end