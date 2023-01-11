(*<*)
theory Answers (* NOTE: the name of the theory must exactly match the name of this file. *)
imports Main
begin
(*>*)

section \<open> Answers \<close>

text \<open> \begin{Answer}[ref = biconditional] \end{Answer} \<close>

lemma "(A \<longleftrightarrow> B) \<longleftrightarrow> (B \<longleftrightarrow> A)"
proof (rule iffI)
  assume left: "A \<longleftrightarrow> B"
  show "B \<longleftrightarrow> A"
  proof (rule iffI)
    assume "B"
    with left show "A" by (rule iffD2)
  next
    assume "A"
    with left show "B" by (rule iffD1)
  qed
next
  assume right: "B \<longleftrightarrow> A"
  show "A \<longleftrightarrow> B"
  proof
    assume "A"
    with right show "B" by (rule iffD2)
  next
    assume "B"
    with right show "A" by (rule iffD1)
  qed
qed

text \<open> \begin{Answer}[ref = disjEexercises] \end{Answer}  \<close>

lemma "A \<or> B \<and> C \<longrightarrow> (A \<or> B) \<and> (A \<or> C)"
proof
  assume "A \<or> B \<and> C"
  thus "(A \<or> B) \<and> (A \<or> C)"
  proof (rule disjE)
    assume "A"
    show "(A \<or> B) \<and> (A \<or> C)"
    proof
      show "A \<or> B" using `A`..
      show "A \<or> C" using `A`..
    qed
  next
    assume "B \<and> C"
    show "(A \<or> B) \<and> (A \<or> C)"
    proof
      from `B \<and> C` have "B"..
      thus "A \<or> B"..
      from `B \<and> C` have "C"..
      thus "A \<or> C"..
    qed
  qed
qed

text \<open> \begin{Answer}[ref = explosion] \end{Answer}  \<close>

lemma explosion: "A \<and> \<not> A \<longrightarrow> B"
proof
  assume "A \<and> \<not> A"
  hence "\<not> A"..
  from `A \<and> \<not> A` have "A"..
  with `\<not> A` show "B" by (rule notE)
qed

text \<open> \begin{Answer}[ref = doublenegationintroduction] \end{Answer}  \<close>

lemma "A \<longrightarrow> \<not> \<not> A"
proof
  assume "A"
  show "\<not> \<not> A"
  proof
    assume "\<not> A"
    thus "False" using `A`..
  qed
qed

text \<open> \begin{Answer}[ref = dracula] \end{Answer}  \<close>

lemma "(\<forall> x. R x d) \<longrightarrow> (\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m"
proof
  assume "\<forall> x. R x d"
  hence "R d d" by (rule allE)
  show "(\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m"
  proof
    assume "\<forall> z. R d z \<longrightarrow> z = m"
    hence "R d d \<longrightarrow> d = m" by (rule allE)
    thus "d = m" using `R d d`..
  qed
qed

text \<open> \begin{Answer}[ref = conversedrinker] \end{Answer}  \<close>

lemma "\<exists> x. (\<exists> y. F y) \<longrightarrow> F x"
proof cases
  assume "\<exists> x. F x"
  then obtain x where x: "F x"..
  hence "(\<exists> y. F y) \<longrightarrow> F x"..
  thus "\<exists> x. (\<exists> y. F y) \<longrightarrow> F x"..
next
  assume "\<not> (\<exists> x. F x)"
  have "(\<exists> y. F y) \<longrightarrow> F x"
  proof
    assume "\<exists> y. F y"
    with `\<not> (\<exists> x. F x)` show "F x"..
  qed
  thus "\<exists> x. (\<exists> y. F y) \<longrightarrow> F x"..
qed

text \<open> \begin{Answer}[ref = demorgan] \end{Answer}  \<close>

lemma not_all_implies_some_not: "\<not> (\<forall> x. F x) \<longrightarrow> (\<exists> x. \<not> F x)"
proof
  assume "\<not> (\<forall> x. F x)"
  show "(\<exists> x. \<not> F x)"
  proof (rule ccontr)
    assume "\<not> (\<exists> x. \<not> F x)"
    have "\<forall> x. F x"
    proof (rule allI)
      fix a
      show "F a"
      proof (rule ccontr)
        assume "\<not> F a"
        hence "\<exists> x. \<not> F x" by (rule exI)
        with `\<not> (\<exists> x. \<not> F x)` show "False"..
      qed
    qed
    with `\<not> (\<forall> x. F x)` show "False"..
  qed
qed

text \<open> \begin{Answer}[ref = drinker] \end{Answer}  \<close>

lemma "\<exists> x. F x \<longrightarrow> (\<forall> x. F x)"
proof cases
  assume "\<forall> x. F x"
  hence "F a \<longrightarrow> (\<forall> x. F x)"..
  thus "\<exists> x. F x \<longrightarrow> (\<forall> x. F x)" by (rule exI)
next
  assume "\<not> (\<forall> x. F x)"
  with not_all_implies_some_not have "\<exists> x. \<not> F x"..
  then obtain a where "\<not> F a" by (rule exE)
  have "F a \<longrightarrow> (\<forall> x. F x)"
  proof
    assume "F a"
    with `\<not> F a` show "\<forall> x. F x" by (rule notE)
  qed
  thus "\<exists> x. F x \<longrightarrow> (\<forall> x. F x)"..
qed

text \<open> \begin{Answer}[ref = everythingissomething] \end{Answer}  \<close>

lemma "\<forall> x. \<exists> y. x = y"
proof
  fix x
  have "x = x" by (rule refl)
  thus "\<exists> y. x = y"..
qed

text \<open> \begin{Answer}[ref = symmetry] \end{Answer}  \<close>

lemma "a = b \<longrightarrow> b = a"
proof
  assume "a = b"
  have "a = a"..
  with `a = b` show "b = a" by (rule subst)
qed

(*<*) end (*>*)