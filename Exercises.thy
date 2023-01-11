(*<*)
theory Exercises (* NOTE: the name of the theory must exactly match the name of this file. *)
imports Main
begin
(*>*)

text \<open> Prove the following: \<close>

lemma strict_positive_paradox: "A \<longrightarrow> B \<longrightarrow> B" oops
lemma prefixing: "(A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)" oops
lemma suffixing: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)" oops
lemma "(A \<longleftrightarrow> B) \<longleftrightarrow> (B \<longleftrightarrow> A)" oops
lemma strengthening_the_antecedent: "(A \<longrightarrow> C) \<longrightarrow> (A \<and> B \<longrightarrow> C)" oops
lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> B \<and> C" oops
lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B \<or> C)" oops
lemma "(A \<longrightarrow> C) \<and> (B \<longrightarrow> C) \<longrightarrow> A \<or> B \<longrightarrow> C" oops
lemma disjunction_associativity: "A \<or> B \<or> C \<longleftrightarrow> (A \<or> B) \<or> C" oops
lemma "A \<or> B \<and> C \<longrightarrow> (A \<or> B) \<and> (A \<or> C)" oops
lemma explosion: "A \<and> \<not> A \<longrightarrow> B" oops
lemma "A \<or> B \<longrightarrow> \<not> A \<longrightarrow> B" oops
lemma double_negation_intro: "A \<longrightarrow> \<not> \<not> A" oops
lemma "\<not> \<not> (A \<or> \<not> A)" oops
lemma excluded_middle: "A \<or> \<not> A" oops
lemma conditional_excluded_middle: "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)" oops
lemma "(A \<longrightarrow> B) \<or> (B \<longrightarrow> C)" oops
lemma "(A \<longrightarrow> B) \<longleftrightarrow> (\<not> A \<or> B)" oops
lemma "(A \<longrightarrow> B) \<longleftrightarrow> \<not> (A \<and> \<not> B)" oops
lemma "(\<forall> x. F x) \<longrightarrow> F a \<and> F b" oops
lemma dracula: "(\<forall> x. R x d) \<longrightarrow> (\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m" oops
lemma "(\<forall> x. F x \<and> G x) \<longrightarrow> (\<forall> x. F x)" oops
lemma "(\<forall> x. F x) \<longrightarrow> (\<forall> x. F x \<longrightarrow> G x)" oops
lemma converse_drinker: "\<exists> x. (\<exists> y. F y) \<longrightarrow> F x" oops
lemma "(\<exists> x. F x) \<longrightarrow> (\<exists> x. F x \<or> G x)" oops
lemma not_all_implies_some_not: "\<not> (\<forall> x. F x) \<longrightarrow> (\<exists> x. \<not> F x)" oops
lemma drinker: "\<exists> x. F x \<longrightarrow> (\<forall> x. F x)" oops
lemma "\<forall> x. \<exists> y. x = y" oops
lemma "a = b \<longrightarrow> b = a" oops

text \<open> These exercises are worth 30% and due by February 2nd \<close>

(*<*) end (*>*)