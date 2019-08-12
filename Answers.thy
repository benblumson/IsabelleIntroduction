(*<*)
theory Answers (* NOTE: the name of the theory must exactly match the name of this file. *)
imports Main
begin
(*>*)

section {* Answers *}

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


(*<*) end (*>*)